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
    // hoist up a lam and adds the lam to the worklist_ for finalize to rewrite the body
    const Def* hoistUp(const Lam* lam);

    // rewrite the body of hoisted up lambdas (from the worklist_)
    // this is being done to ensure that the rewrite of the body
    // is happening inside a scope where everything that depends on
    // the free_vars is already droped
    void finalize() final;

    // annotate a 'abstract' closure for later phases
    const Def* annotate(const Def* def, anno a) {
        auto& w = new_world();
        return w.call(a, def);
    }

    const Def* rewrite_mut_Lam(Lam* lam) final {
        if (lam->is_external()) {
            // we dont want anything that depends on lam->var() to be inside the root scope
            // if we want to hoist up something inside of lam which is using `Idx n` where `n`
            // is the Var of `lam` then I want to rewrite `n` there to something else.
            // thus I must drop everything that depends on `n` before rewriting the body of that lam
            // (the one we want to hoistup inside of the body of `lam`)
            // which is done after returning from this function thanks to the finalize machinery.
            push();
            bind_old(lam->has_var());
            auto new_mut = RWPhase::rewrite_mut_Lam(lam);
            pop();
            return new_mut;
        }

        // rewrite the type of lam and its free vars.
        // note that the body will be rewritten in finalize to work inside a scope where everything that depends on the free vars is already gone
        // the map then creates a mapping from lam to the application of hoisted_lam with environment inside of the scope where the free vars of lam
        // (those that are also rewritten into environment) are owned
        // this way the mapping will be droped as soon as we leave the scope of those free_vars
        return map(lam, hoistUp(lam));
    }

    const Def* rewrite_imm_Lam(const Lam* lam) final {
        if (lam->is_external()) return RWPhase::rewrite_imm_Lam(lam);
        // see comment on hoistUp inside rewrite_mut_Lam
        return hoistUp(lam);
    }

    // FIXME: for some reason I must rewrite first callee then arg. I should investigate that.
    // in the base function it rewrites them the other way around...
    // note: maybe this is gone now, I'll check
    const Def* rewrite_imm_App(const App* app) final {
        rewrite(app->callee());
        rewrite(app->arg());
        return RWPhase::rewrite_imm_App(app);
    }

private:
    struct Stub {
        const Lam* lam;
        const DefVec fvs;
    };
    std::queue<Stub> worklist_ = {};
    DefMap<Lam*> outerlams_    = {};
    FVAnalysis fvana_          = {};
};

} // namespace mim::plug::clos2
