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

    log().d("hoistUp {}, free vars {} vs {}", lam, fvs, lam->free_vars());

    // we want to reuse the procedure (outerlam) if it was already created.
    // we cannot use the map/lookup machinery for this because we might have to use anoter environment in different places.
    if (auto it = outerlams_.find(lam); it != outerlams_.end()) {
        log().d("reuse {} ~> {}", lam, it->second);
        return annotate(w.app(it->second, environment), anno::closure);
    }

    // create pi for outer lambda
    auto outer_pi = w.mut_pi(w.type_pending(), false);

    // first set domain
    // if sig is closed or the environment has only one element we can skip the rewrite in else and just use the type of that
    if (auto sig = w.tuple(environment)->type(); environment.size() == 1 || sig->is_closed()) {
        if (environment.size() == 1) assert(sig->is_closed()); // all free vars are in the environment, thus size 1 implies closed
        outer_pi->set_dom(sig); // sig is environment->type() or a closed sigma type
    } else {
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

        if (environment.size() == 1)
            subst.map(environment[0], n);
        else {
            assert(n->num_projs() == environment.size() && "the environment and the outer_pi->var() should have the same arity");

            for (size_t i = 0; i < environment.size(); i++)
                subst.map(environment[i], n->proj(n->num_projs(), i));
        }

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
            assert(mut->num_doms() == inner_lam->num_doms() && "inner_lam and lam should have the same num_doms()");

            for (size_t i = 0; i < inner_lam->num_doms(); i++)
                inner_lam->var(inner_lam->num_doms(), i)->set(mut->var(mut->num_doms(), i)->dbg_key());
        }
    }

    // we perform the rewrite of the body after the map/lookup scope of the free vars was destroyed.
    // the rewrite is being done in finalize. thus we have to add {lam, fvs} to the worklist.
    // the actual new lam can be obtained there by the outerlams_ map.
    worklist_.emplace(lam, fvs);
    outerlams_[lam] = outer_lam;

    log().d("hoistup {} ~> {}:{} with free vars {}", lam, outer_lam, outer_lam->type(), outer_lam->free_vars());

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

        const auto& lam = stub.lam;
        const auto& fvs = stub.fvs;

        const auto outer_lam = outerlams_.at(lam);
        const auto inner_lam = outer_lam->body()->as_mut<Lam>();

        log().d("finalize {}", lam);

        // create a scope that binds anything that contains the passed environment, the var of the inner lambda or the free vars
        // thus pop will drop anything that contains any of those making sure that they will not be leaked to the next finalize loop.
        push(lam->free_vars());
        bind_old(lam->has_var());
        bind_new(outer_lam->var()->isa<Var>());
        bind_new(inner_lam->var()->isa<Var>());

        auto env = outer_lam->var();
        env->set("env");

        if (fvs.size() == 1) {
            env->set(fvs[0]->sym());
            map(fvs[0], env);
            log().d("mapping {} to {}", fvs[0], env);
        } else {
            assert(env->num_projs() == fvs.size() && "env and fvs should agree on their arity");
            for (size_t i = 0; i < fvs.size(); i++) {
                auto f = fvs[i];
                auto e = env->proj(fvs.size(), i);
                e->set(f->sym());
                map(f, e);
                log().d("mapping {} to {}", f, e);
            }
        }

        if (auto v = lam->has_var()) {
            auto n = inner_lam->var();
            map(v, n);
            log().d("mapping mut var {} to {}", v, n);
        }

        auto body = rewrite(lam->body());
        log().d("rewrote body of {}", lam);
        inner_lam->set(rewrite(lam->filter()), body);

        pop();

        // this checks that the body doesnt contain free vars
        if (!outer_lam->is_closed())
            outer_lam->blame("outer_lam is not closed, has free vars {}", outer_lam->free_vars()).bail();
    }
}
