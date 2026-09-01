#include "mim/plug/clos2/phase/clos_conv.h"

using namespace mim;
using namespace mim::plug;
using namespace mim::plug::clos2;

/// this function analysis the old world and decides what should be closure converted.
/// TODO: later I also want it to decide what should be converted in which way.
bool ClosConv::analyze() {
    if (analyzed_) return false;
    analyzed_ = true;

    DefSet done{};

    // visit all def's from the old world and decide what ClosConv will do to it
    auto visit = [&](auto visit, const Def* def) {
        if (!done.emplace(def).second) return;

        // for now we want to closure convert everything with a function type
        if (auto lam = def->isa<Lam>(); lam && lam->type()->isa<Pi>() && !fvana_.is_closed(lam)) {
            log().d("found function which will be closure converted {}", lam);
            toBeConverted_.emplace(def);
        } else
            for (auto dep : def->deps())
                visit(visit, dep);
    };

    for (auto def : old_world().roots())
        visit(visit, def);

    return false;
}
