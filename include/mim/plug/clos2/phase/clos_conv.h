#pragma once

#include <queue>

#include "mim/def.h"
#include "mim/lam.h"
#include "mim/phase.h"

#include "mim/util/types.h"

#include "mim/plug/clos2/clos2.h"
#include "mim/plug/clos2/fv.h"

namespace mim::plug::clos2 {

class ClosConv : public RWPhase {
public:
    ClosConv(World& world, flags_t annex)
        : RWPhase(world, annex) {}

private:
    const Def* rewrite_procedure(Axm::IsA<anno, App> app);

    const Def* rewrite_mut_Pi(Pi*) final;
    const Def* rewrite_imm_Pi(const Pi*) final;
    
    const Def* rewrite_imm_Lam(const Lam* d) final {
        auto old_pi = d->type();
        auto new_type   = (old_pi->isa_mut() ? RWPhase::rewrite_mut_Pi(old_pi->as_mut<Pi>()) : RWPhase::rewrite_imm_Pi(old_pi))->as<Pi>();
        auto new_filter = rewrite(d->filter());
        auto new_body   = rewrite(d->body());
        return new_world().lam(new_type, new_filter, new_body);
    }

    const Def* rewrite_mut_Lam(Lam* d) final {
        auto old_pi = d->type();
        const Pi* new_pi = (old_pi->isa_mut() ? RWPhase::rewrite_mut_Pi(old_pi->as_mut<Pi>()) : RWPhase::rewrite_imm_Pi(old_pi))->as<Pi>();
        return rewrite_stub(d, new_world().mut_lam(new_pi));
    }


    // abstract closure elim and closure application
    const Def* rewrite_imm_App(const App* app) {
        if (auto a = Axm::isa<anno>(app)) return rewrite_procedure(a);

        auto new_arg = rewrite(app->arg());
        auto new_callee = rewrite(app->callee());

        // if the callee is not a Pi then it is a closure
        if (!new_callee->type()->isa<Pi>())
            return Closure::closure_apply(new_callee, new_arg);

        return RWPhase::rewrite_imm_App(app);
    }

    FVAnalysis fvana_{};
};

} // namespace mim::plug::clos2
