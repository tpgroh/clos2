#pragma once

#include "mim/def.h"
#include "mim/lam.h"
#include "mim/phase.h"

#include "mim/util/types.h"

#include "mim/plug/clos2/fv.h"

namespace mim::plug::clos2 {

class ClosConv : public RWPhase {
public:
    ClosConv(World& world, flags_t annex)
        : RWPhase(world, annex) {}

private:
    void map_fvs_to_ext(const DefVec& fvs, const Def* env);

    const Def* get_environment_type(const DefVec& fvs);

    const Def* get_environment(const DefVec& fvs);
    const Def* get_procedure(const DefVec& fvs, const Def* env_type, const Lam* old_lam);
    const Def* clos_type(const Pi*);
    const Def* closure_pack(const Lam* old_lam);
    const Def* closure_apply(const Def* clos, const Def* arg);

    bool analyze() final;
    void rewrite_external(Def*) final;
    const Def* rewrite_mut_Lam(Lam*) final;
    const Def* rewrite_imm_Lam(const Lam*) final;
    const Def* rewrite_mut_Pi(Pi*) final;
    const Def* rewrite_imm_Pi(const Pi*) final;
    const Def* rewrite_imm_App(const App*) final;

    FVAnalysis fvana_{};
};

} // namespace mim::plug::clos2
