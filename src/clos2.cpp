#include "mim/plug/clos2/clos2.h"

#include <mim/phase.h>
#include <mim/plugin.h>

#include "mim/plug/clos2/phase/hoist_up.h"
#include "mim/plug/clos2/phase/absclos_elim.h"

using namespace mim;
using namespace mim::plug;

void reg_phases(Flags2Phases& phases) {
    Phase::hook<clos2::hoist_up, clos2::HoistUp>(phases);
    Phase::hook<clos2::absclos_elim, clos2::AbsClosElim>(phases);
}

MIM_PLUGIN_ENTRY(clos2) {
    plugin.register_phases      = reg_phases;
    plugin.register_normalizers = clos2::register_normalizers;
}
