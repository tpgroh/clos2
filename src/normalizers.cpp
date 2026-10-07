#include "mim/plug/clos2/autogen.h"

using namespace mim;
using namespace mim::plug;

namespace mim::plug::clos2 {
template<anno a>
const Def* normalize_anno(const Def*, const Def*, const Def*) {
    return nullptr; // always decline
}

MIM_clos2_NORMALIZER_IMPL

} // namespace mim::plug::clos2
