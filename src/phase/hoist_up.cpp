#include "mim/plug/clos2/phase/hoist_up.h"

#include "mim/def.h"
#include "mim/phase.h"

#include "fe/vector.h"

using namespace mim;
using namespace mim::plug;
using namespace mim::plug::clos2;

/// calculate [@p fvs ... mapsto @p n # ...] @p def
/// this has to be done in an extra Rewriter because the fvs might already be mapped indirectly.
/// It cannot be done using VarRewriter because the fvs dont have to be Var's
static inline const Def* subst_free_vars(World& w, const DefVec& fvs, const Def* n, const Def* def) {
    auto sub = Rewriter(w);

    if (fvs.size() == 1)
        sub.map(fvs[0], n);
    else
        for (size_t i = 0; i < fvs.size(); i++)
            sub.map(fvs[i], n->proj(n->num_projs(), i));

    return sub.rewrite(def);
}

const Def* HoistUp::hoistUp(const Lam* lam) {
    auto& w = new_world();

    push();

    auto fvset       = fvana_.free_vars(lam);
    auto fvs         = DefVec{fvset.begin(), fvset.end()};
    std::ranges::sort(fvs, GIDLt<const Def*>());
    auto environment = DefVec{fvs.size(), [&](auto i) { return rewrite(fvs[i]); }};

    if (auto it = outerlams_.find(lam); it != outerlams_.end()) {
        log().i("reuse {} ~> {}", lam, it->second);
        return w.app(it->second, environment);
    }

    // create pi for outer lambda
    // TODO: use actual type, (umax of fvs + ? ) ; it should be the same as the kind of lam???
    auto outer_pi = w.mut_pi(w.type(), false);
    if (auto sig = w.tuple(environment)->type(); sig->is_closed())
        outer_pi->set_dom(sig);
    else {
        auto outer_sig = w.mut_sigma(rewrite(old_world().umax<UMax::Term>(fvs)), fvs.size());
        auto subst = Rewriter(w);
        for (size_t i = 0; i < fvs.size(); i++) {
            outer_sig->set(i, subst.rewrite(environment[i]->type()));
            subst.map(environment[i], outer_sig->var(fvs.size(), i));
        }
        assert(!outer_sig->is_immutabilizable());
        if (outer_sig->is_immutabilizable()) outer_sig->immutabilize();
        outer_pi->set_dom(outer_sig);
    }

    // rewrite codom then substitue free vars
    auto wrong_inner_pi = rewrite(lam->type())->as<Pi>();
    auto codom          = subst_free_vars(w, environment, outer_pi->var(), wrong_inner_pi)->as<Pi>();
    outer_pi->set_codom(codom);

    // create outer lam
    auto outer_lam = w.mut_lam(outer_pi);

    // now we can create the inner_lam
    auto inner_pi  = subst_free_vars(w, environment, outer_lam->var(), wrong_inner_pi)->as<Pi>();
    auto inner_lam = w.mut_lam(inner_pi);
    inner_lam->set(lam->dbg_key());
    outer_lam->set(lam->dbg_key());
    outer_lam->set(false, inner_lam); // false filter because we dont want to just insert the environment back in

    // set argument dbg keys
    if (auto mut = lam->isa_mut<Lam>()) {
        if (mut->num_doms() == 1)
            inner_lam->var()->set(mut->var()->dbg_key());
        else {
            auto num_doms = mut->num_doms();
            assert(num_doms == inner_lam->num_doms() && "inner_lam and lam should have the same num_doms()");

            for (size_t i = 0; i < mut->num_doms(); i++)
                inner_lam->var(num_doms, i)->set(mut->var(num_doms, i)->dbg_key());
        }
    }

    // we have to to the actual rewrite after we have cleared the old2new mappings
    // because it might introduce new free vars (when something was already indirectly mapped, for example extractions
    // of something)
    worklist_.emplace(lam, fvs);
    outerlams_[lam] = outer_lam;

    log().i("hoistup {} ~> {}:{} with free vars {}", lam, outer_lam, outer_lam->type(), outer_lam->free_vars());

    // this checks that the type is now closed
    if (!outer_lam->type()->is_closed())
        outer_lam->blame("outer_lam's type is not closed, has free vars {}", outer_lam->type()->free_vars()).bail();

    pop();

    return annotate(w.app(outer_lam, environment), anno::closure);
}

const Def* HoistUp::annotate(const Def* def, anno a) {
    auto& w = new_world();
    return w.call(a, def);
}

void HoistUp::finalize() {
    auto& w = new_world();

    while (!worklist_.empty()) {
        auto stub = worklist_.front();
        worklist_.pop();
        
        auto& lam = stub.lam;
        auto& fvs = stub.fvs;

        auto outer_lam = outerlams_.at(lam);
        auto inner_lam = outer_lam->body()->as_mut<Lam>();

        log().i("finalize {}", lam);
        push();

        auto env = outer_lam->var();
        env->set("env");

        if (fvs.size() == 1) {
            env->set(fvs[0]->sym());
            map(fvs[0], env);
            log().i("mapping {} to {}", fvs[0], env);
        } else
            for (size_t i = 0; i < fvs.size(); i++) {
                auto f = fvs[i];
                auto e = w.extract(env, i);
                e->set(f->sym());
                map(f, e);
                log().i("mapping {} to {}", f, e);
            }

        if (lam->is_mutable()) {
            auto v = lam->as_mut<Lam>()->var();
            auto n = inner_lam->var();
            map(v, n);
            log().i("mapping mut var {} to {}", v, n);
        }

        // fix recursive and mutable recursive calls to prevent including their environments as free variables
        for (auto m : lam->body()->local_muts())
            if (auto l = m->isa<Lam>(); l && outerlams_.contains(l)) {
                log().i("remapping {} from {} to nullptr", l, RWPhase::lookup(l));
                map(l, nullptr); // if l was already rewritten we let hoist_up take care of rewriting
            }

        auto body = rewrite(lam->body());
        log().i("rewrote body of {}", lam);
        inner_lam->set(rewrite(lam->filter()), body);

        pop();

        // this checks that the body doesnt contain free vars
        if (!outer_lam->is_closed())
            outer_lam->blame("outer_lam is not closed, has free vars {}", outer_lam->free_vars()).bail();
    }
}

const Def* HoistUp::rewrite_mut_Lam(Lam* lam) {
    if (is_bootstrapping() || lam->is_external()) {
        push();
        auto new_mut = RWPhase::rewrite_mut_Lam(lam);
        pop();
        return map(lam, new_mut);
    }

    return map(lam, hoistUp(lam));
}

const Def* HoistUp::rewrite_imm_Lam(const Lam* lam) {
    if (is_bootstrapping() || lam->is_external()) {
        push();
        auto new_imm = RWPhase::rewrite_imm_Lam(lam);
        pop();
        return new_imm;
    }

    return hoistUp(lam);
}
