#include "mim/world.h"

#include "mim/plug/clos2/clos2.h"

namespace mim::plug::clos2 {

const Def* normalize_const(const Def* type, const Def*, const Def* arg) {
    auto& world = type->world();
    return world.lit(world.type_idx(arg), 42);
}

MIM_clos2_NORMALIZER_IMPL

} // namespace mim::plug::clos2
