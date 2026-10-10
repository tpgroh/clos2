#pragma once

#include "mim/def.h"
#include "mim/lam.h"
#include "mim/phase.h"

#include "mim/plug/clos2/autogen.h"
#include "mim/plug/clos2/fv.h"

namespace mim::plug::clos2 {

class LamLiftType : public RWPhase {
public:
    LamLiftType(World& world, flags_t annex)
        : RWPhase(world, annex) {}

private:
    // get deterministic ordering of free vars in @p type
    DefVec getFreeTypeVars(const Def* type);

    const Def* lift_lam(const Lam*);
    const Def* lift_pi(const Pi*);
    const Def* lift_app(const App*);

    // I have to detect if a lam is from the curryed application of a closure or not.
    // currently I'm assuming that we are working with a CPS world thus every lam which is not a continuation was introduced by the previous phase and thus 
    // it is a lam that comes from curryed application.

    const Def* rewrite_imm_Lam(const Lam* lam) final {
        if (is_bootstrapping() || !Pi::isa_cn(lam->type()) return RWPhase::rewrite_imm_Lam(lam);

        return lift_lam(lam);
    }

    const Def* rewrite_mut_Lam(Lam* lam) final {
        if (is_bootstrapping() || !Pi::isa_cn(lam->type()) return RWPhase::rewrite_mut_Lam(lam);

        return lift_lam(lam);
    }

    const Def* rewrite_mut_Pi(Pi* pi) final {
        if (is_bootstrapping() || pi->is_closed() || !Pi::isa_cn(pi)) return RWPhase::rewrite_mut_Pi(pi);
        return map(pi, lift_pi(pi));
    }

    const Def* rewrite_imm_Pi(const Pi* pi) final {
        if (is_bootstrapping() || pi->is_closed() || !Pi::isa_cn(pi)) return RWPhase::rewrite_imm_Pi(pi);
        return lift_pi(pi);
    }

    const Def* rewrite_imm_App(const App* app) final {
        if (is_bootstrapping() || app->is_closed()) return RWPhase::rewrite_imm_App(app);

        // skip annotation
        if (auto a = Axm::isa<anno>(app)) return RWPhase::rewrite_imm_App(app);

        return lift_app(app);
    }

private:
    FVAnalysis fvana_ = {};
};

} // namespace mim::plug::clos2
