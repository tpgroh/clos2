#pragma once

#include "mim/lam.h"

#include "mim/plug/clos2/autogen.h"

namespace mim::plug::clos2 {

struct Closure {
    /// returns the type of a closure with a procedure that takes @p as a domain
    static const Def* closure_type(const Def* dom);

    /// unpack closure @p clos and apply the procedure to the environment and the argument @p arg
    static const Def* closure_apply(const Def* clos, const Def* arg);

    /// create a representation of this abstract closure
    static const Def* pack(Lam* procedure, const Def* environment, const Def* dom);
};

} // namespace mim::plug::clos2
