#include "mim/plug/clos2/clos2.h"

#include <mim/phase.h>
#include <mim/plugin.h>

using namespace mim;

/// Registers normalizers as well as Phase%s and Pass%es for the Axm%s of this Plugin.
extern "C" MIM_EXPORT Plugin mim_get_plugin() {
    return {"clos2", MIM_VERSION, plug::clos2::register_normalizers, nullptr};
}
