#pragma once
#include "mim/phase.h"

#include "mim/util/types.h"

#include "mim/plug/clos2/fv.h"

// TODO: how do I detect first class use of functions?
//
// TODO: currently I want a closure to be a pair of a function and the environment
// the type would be (E->A->B, E)
//
// TODO: my current idea is that I create the closure at the location where the original function apeared.
// then I create an apply function lam x:A.c#ff c#tt

namespace mim::plug::clos2 {

class ClosConv : public RWPhase {
public:
    ClosConv(World& world, flags_t annex)
        : RWPhase(world, annex) {}

private:
    bool analyze() final;

    FVAnalysis fvana_ = {};
    bool analyzed_    = false;

    /// list of Lam's that should be converted
    DefSet toBeConverted_ = {};
};

} // namespace mim::plug::clos2
