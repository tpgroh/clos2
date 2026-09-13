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
    const Pi* create_fn_type(const Pi*, const DefVec&, const Def*);
    const Def* rewrite_lam_to_clos(const Lam*);

    bool analyze() final;
    void rewrite_external(Def*) final;
    const Def* rewrite_mut_Lam(Lam*) final;
    const Def* rewrite_imm_Lam(const Lam*) final;

    FVAnalysis fvana_{};
};

} // namespace mim::plug::clos2
