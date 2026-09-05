#pragma once
#include "mim/def.h"
#include "mim/lam.h"
#include "mim/phase.h"

#include "mim/util/types.h"

#include "mim/plug/clos2/fv.h"

namespace mim::plug::clos2 {

class ClosConv : public RWPhase {
public:
    ClosConv(World& world, flags_t annex)
        : RWPhase(world, annex) {}

private:
    bool analyze() final;
    const Def* rewrite_imm_App(const App*) final;
    const Def* rewrite_imm_Lam(const Lam*) final;
    const Def* rewrite_mut_Lam(Lam*) final;

    const Def* get_closure(const Lam*);

    FVAnalysis fvana_{};
    DefSet convertable_{};
    DefSet closureCallsites_{};
    Def2Def closures_{};
};

} // namespace mim::plug::clos2
