#include "mim/plug/clos2/phase/hoist_up.h"

#include "mim/def.h"
#include "mim/phase.h"

#include "fe/vector.h"

using namespace mim;
using namespace mim::plug;
using namespace mim::plug::clos2;

const Def* HoistUp::hoistUp(const Lam* lam) {
    auto& w = new_world();

    auto fvset       = fvana_.free_vars(lam);
    auto fvs         = DefVec{fvset.begin(), fvset.end()};
    std::ranges::sort(fvs, GIDLt<const Def*>()); // this ensures that we rewrite/set ops in the correct order in the procedure type (for dependent types)
    auto environment = DefVec{fvs.size(), [&](auto i) { return rewrite(fvs[i]); }};

    log().i("hoistUp {}, free vars {} vs {}", lam, fvs, lam->free_vars());

    // we want to reuse the procedure (outerlam) if it was already created.
    // we cannot use the map/lookup machinery for this because we might have to use anoter environment in different places.
    if (auto it = outerlams_.find(lam); it != outerlams_.end()) {
        log().i("reuse {} ~> {}", lam, it->second);
        return annotate(w.app(it->second, environment), anno::closure);
    }

    // create pi for outer lambda
    auto outer_pi = w.mut_pi(w.type_pending(), false);

    // first set domain
    if (auto sig = w.tuple(environment)->type(); sig->is_closed()) // if sig is closed we can skip the rewrite in else
        outer_pi->set_dom(sig);
    else {
        // we have to create a type for environment where the dependency of entries on each other is correctly set.
        // this is also why we sorted the fvs at the start
        auto outer_sig = w.mut_sigma(w.type_pending(), fvs.size());
        auto subst = Rewriter(w);
        for (size_t i = 0; i < fvs.size(); i++) {
            outer_sig->set(i, subst.rewrite(environment[i]->type()));
            subst.map(environment[i], outer_sig->var(fvs.size(), i));
        }

        // note: this assert should always be the case as any var that can be referenced inside sig should be also in fvs
        // and thus also in the environment. which means thatthe above subst should always have rewritten something
        // resulting in outer_sig being mutable and not immutabilizable.
        assert(!outer_sig->is_immutabilizable());

        outer_pi->set_dom(outer_sig);
    }

    // rewrite codom then substitue free vars
    auto wrong_inner_pi = rewrite(lam->type())->as<Pi>();
    const Pi* codom;
    { // scope this to throw away the Rewriter directly afterwards
        auto subst = Rewriter(w);
        auto n = outer_pi->var();
        auto env_size = n->num_projs();
        log().d("env_size {} == environment.size() {}", env_size, environment.size());
        // TODO: I thought this must be the case
        // assert(env_size == environment.size() && "the environment and the outer_pi->var() should have the same arity");

        if (environment.size() == 1)
            subst.map(environment[0], n);
        else
            for (size_t i = 0; i < environment.size(); i++)
                subst.map(environment[i], n->proj(env_size, i));

        codom = subst.rewrite(wrong_inner_pi)->as<Pi>();
    }
    outer_pi->set_codom(codom);

    // create outer lam
    auto outer_lam = w.mut_lam(outer_pi);

    // now we can create the inner_lam
    auto inner_pi  = outer_pi->reduce(outer_lam->var())->as<Pi>();
    auto inner_lam = w.mut_lam(inner_pi);
    
    // set dbg keys
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

            for (size_t i = 0; i < num_doms; i++)
                inner_lam->var(num_doms, i)->set(mut->var(num_doms, i)->dbg_key());
        }
    }

    // we perform the rewrite of the body after the map/lookup scope of the free vars was destroyed.
    // the rewrite is being done in finalize. thus we have to add {lam, fvs} to the worklist.
    // the actual new lam can be obtained there by the outerlams_ map.
    worklist_.emplace(lam, fvs);
    outerlams_[lam] = outer_lam;

    log().i("hoistup {} ~> {}:{} with free vars {}", lam, outer_lam, outer_lam->type(), outer_lam->free_vars());

    // this checks that the type is now closed
    if (!outer_lam->type()->is_closed())
        outer_lam->blame("outer_lam's type is not closed, has free vars {}", outer_lam->type()->free_vars()).bail();

    return annotate(w.app(outer_lam, environment), anno::closure);
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
        if (!outer_lam->is_closed()) {
            outer_lam->dot("outer_lam.dot");
            outer_lam->blame("outer_lam is not closed, has free vars {}", outer_lam->free_vars()).bail();
        }
    }
}
