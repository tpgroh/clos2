#pragma once

#include "mim/plug/clos2/autogen.h"

namespace mim::plug::clos2 {

class Closure {
public:
    const Def* type() const;

private:
    const Def* environment;
    const Def* procedure;
};

} // namespace mim::plug::clos2
