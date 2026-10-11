#pragma once

#include "mim/def.h"
#include "mim/lam.h"
#include "mim/phase.h"

#include "mim/plug/clos2/fv.h"
#include "mim/plug/clos2/autogen.h"

namespace mim::plug::clos2 {

class LamLiftType : public RWPhase {
public:
    LamLiftType(World& world, flags_t annex)
        : RWPhase(world, annex) {}

private:
    // get deterministic ordering of free vars in @p type
    DefVec getFreeTypeVars(const Def* type);

    const Def* lift_lam(Lam*);
    const Def* lift_pi(const Pi*);
    const Def* lift_app(const App*);

    // the only lambdas that we have to modify are nested in a procedure lam.
    // we detect those using by checking that the type is not a continuation Pi.
    const Def* rewrite_mut_Lam(Lam* lam) final {
        if (is_bootstrapping() || Pi::isa_cn(lam->type())) return RWPhase::rewrite_mut_Lam(lam);
        return lift_lam(lam);
    }

    // to skip the Pi type of procedures Im just checking if the pi is a continuation.
    // before this plugin Im running the cps conversion phase thus the only pi types remaining should be those that I
    // introduced with the last phase.
    // TODO: if this is not correct I would add a new annotation for the type of procedures to detect and skip those here
    const Def* rewrite_mut_Pi(Pi* pi) final {
        if (is_bootstrapping() || pi->is_closed() || !Pi::isa_cn(pi)) return RWPhase::rewrite_mut_Pi(pi);
        return map(pi, lift_pi(pi));
    }

    const Def* rewrite_imm_Pi(const Pi* pi) final {
        if (is_bootstrapping() || pi->is_closed() || !Pi::isa_cn(pi)) return RWPhase::rewrite_imm_Pi(pi);
        return lift_pi(pi);
    }

    // here I can skip every application that is closed and those that come from the partial application 
    const Def* rewrite_imm_App(const App* app) final {
        if (is_bootstrapping() || !Pi::isa_cn(app->callee_type())) return RWPhase::rewrite_imm_App(app);

        log().i("rewrite app ({}:{})({}:{})", app->callee(), app->callee_type(), app->arg(), app->arg()->type());

        // skip annotation
        if (auto a = Axm::isa<anno>(app))
            return RWPhase::rewrite_imm_App(app);

        return lift_app(app);
    }

private:
    FVAnalysis fvana_ = {};
};

} // namespace mim::plug::clos2
