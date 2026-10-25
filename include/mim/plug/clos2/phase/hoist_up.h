#pragma once

#include <cstdio>

#include <queue>

#include "mim/def.h"
#include "mim/lam.h"
#include "mim/phase.h"

#include "mim/plug/clos2/autogen.h"
#include "mim/plug/clos2/fv.h"

namespace mim::plug::clos2 {

class HoistUp : public RWPhase {
public:
    HoistUp(World& world, flags_t annex)
        : RWPhase(world, annex) {}

private:
    const Def* hoistUp(const Lam* lam);
    const Def* annotate(const Def* def, anno a);

    // TODO: drop this
    const Def* rewrite(const Def* def) final {
        log().d("rewrite {}", def);

        auto new_def = RWPhase::rewrite(def);

        log().d("rewrite {} ~> {}", def, new_def);
        return new_def;
    }

    // TODO: drop this
    const Def* rewrite_imm_Var(const Var* var) final {
        log().d("rewrite {} has binder {}", var, var->binder());
        auto new_binder = rewrite(var->binder());
        log().d("new binder {}", new_binder);
        // if (auto a = Axm::isa<anno>(new_binder)) {
        //     log().d("detected var binder to be a annotation");
        //     auto actual_binder = a->arg();
        //     log().d("actual binder {}", actual_binder);
        //     return new_world().var(actual_binder->as_mut());
        // }
        return RWPhase::rewrite_imm_Var(var);
    }

    const Def* rewrite_mut_Lam(Lam* lam) final {
        if (lam->is_external()) {
            // TODO : claude please check this comment if it is understandable to you
            // we dont want anything that depends on lam->var() to be inside the root scope
            // if we want to hoist up something inside of lam which is using `Idx n` where `n`
            // is the Var of `lam` then I want to rewrite `n` there to something else.
            // thus I must drop everything that depends on `n` before to force a correct rewrite
            push();
            bind_old(lam->has_var());
            auto new_mut = RWPhase::rewrite_mut_Lam(lam);
            pop();

            // NOTE: claude claims that the rewrite_stub of lam survives the pop(), I should check that
            return new_mut;
        }

        // TODO : claude check this comment
        // rewrite the type of lam and its free vars.
        // note that the body will be rewritten in finalize to work inside a scope where everything that depends on the free vars is already gone
        // the map then creates a mapping from lam to the application of hoisted_lam with environment inside of the scope where the free vars are bound
        // this way the mapping will be droped as soon as we leave the scope of those free_vars
        return map(lam, hoistUp(lam));
    }

    const Def* rewrite_imm_Lam(const Lam* lam) final {
        if (lam->is_external()) return RWPhase::rewrite_imm_Lam(lam);
        return hoistUp(lam);
    }

    // rewrite the body of hoisted up lambdas (from the worklist_)
    // this is being done to ensure that the rewrite of the body
    // is happening inside a scope where everything that depends on
    // the free_vars is already droped
    void finalize() final;

    // FIXME: for some reason I must rewrite first callee then arg. I should investigate that.
    // in the base function it rewrites them the other way around...
    // note: maybe this is gone now, I'll check
    const Def* rewrite_imm_App(const App* app) final {
        rewrite(app->callee());
        rewrite(app->arg());
        return RWPhase::rewrite_imm_App(app);
    }

private:
    // TODO: should I use fe::Queuelike instead?
    struct Stub {
        const Lam* lam;
        const DefVec fvs;
    };
    std::queue<Stub> worklist_ = {};
    DefMap<Lam*> outerlams_          = {};
    FVAnalysis fvana_                = {};
};

} // namespace mim::plug::clos2
