#pragma once
#include "mim/lam.h"
#include "mim/phase.h"

#include "mim/util/types.h"

#include "mim/plug/clos2/fv.h"

namespace mim::plug::clos2 {

struct Closure {
    const Def* env;
    const Def* code;
};

/// for now I want to closure convert everything.

class ClosConv : public RWPhase {
public:
    ClosConv(World& world, flags_t annex)
        : RWPhase(world, annex) {}

private:
    const Def* rewrite_imm_App(const App*) final;

    const Def* create_closure(Lam*);

    FVAnalysis fvana_{};
};

} // namespace mim::plug::clos2
