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

    // FIXME: this is currently not used. but I should use it to mark for the following phases which delate applications
    // should be eliminated to closures
    const Def* annotate(const Def* def, anno a);

    const Def* rewrite_mut_Lam(Lam*) final;
    const Def* rewrite_imm_Lam(const Lam*) final;

    void finalize() final;

    // FIXME: for some reason I must rewrite first callee then arg. I should investigate that.
    // in the base function it rewrites them the other way around...
    const Def* rewrite_imm_App(const App* app) final {
        rewrite(app->callee());
        rewrite(app->arg());
        return RWPhase::rewrite_imm_App(app);
    }

private:
    // TODO: should I use fe::Queuelike instead?
    std::queue<const Lam*> worklist_ = {};
    DefMap<Lam*> outerlams_          = {};
    FVAnalysis fvana_                = {};
};

} // namespace mim::plug::clos2
