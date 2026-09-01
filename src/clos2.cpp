#include "mim/plug/clos2/clos2.h"

#include <mim/phase.h>
#include <mim/plugin.h>

#include "mim/plug/clos2/phase/clos_conv.h"

using namespace mim;
using namespace mim::plug;

void reg_phases(Flags2Phases& phases) { Phase::hook<clos2::clos_conv, clos2::ClosConv>(phases); }

/// Registers normalizers as well as Phase%s and Pass%es for the Axm%s of this Plugin.
extern "C" MIM_EXPORT Plugin mim_get_plugin() {
    return {"clos2", MIM_VERSION, nullptr, reg_phases};
}
