#pragma once

#include "mim/def.h"
#include "mim/phase.h"
#include "mim/plug/clos2/autogen.h"

namespace mim::plug::clos2 {

class AbsClosSjLj : public RWPhase {
public:
    AbsClosSjLj(World& world, flags_t annex)
        : RWPhase(world, annex) {}
private:
};

}
