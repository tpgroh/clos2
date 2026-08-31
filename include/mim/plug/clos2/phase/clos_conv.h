#pragma once
#include "mim/phase.h"

#include "mim/util/types.h"

namespace mim::plug::clos2 {

class ClosConv : public RWPhase {
public:
    ClosConv(World& world, flags_t annex)
        : RWPhase(world, annex) {}
};

} // namespace mim::plug::clos2
