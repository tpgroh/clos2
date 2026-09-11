#pragma once
#include <queue>

#include "mim/def.h"
#include "mim/lam.h"
#include "mim/phase.h"

#include "mim/util/gid.h"
#include "mim/util/types.h"

#include "mim/plug/clos2/fv.h"

namespace mim::plug::clos2 {

class ClosConv : public RWPhase {
public:
    ClosConv(World& world, flags_t annex)
        : RWPhase(world, annex) {}

private:
    /// TODO:
    /// I'm now trying to move the rewrite of the code_body to the end when all closures are already created.
    /// hopefully this makes stuff simpler

    struct Stub {
        DefVec fvs;

        const Def* fn_type;
        const Def* env;
        Lam* procedure;

        const Def* pack() const;
        static std::tuple<const Def*, const Def*, const Def*> unpack(const Def*);
        static const Def* isa_closure(const Def*);
        static const Def* clos_type(const Pi*);
        static const Def* apply(const Def*, const Def*);
    };

    const Stub* get_Stub(const Lam*);
    const Def* rewrite_body(Stub&, const Lam*);

    bool analyze() final;
    void rewrite_external(Def*) final;
    const Def* rewrite_mut_Lam(Lam*) final;
    const Def* rewrite_imm_Lam(const Lam*) final;
    const Def* rewrite_imm_App(const App*) final;
    const Def* rewrite_imm_Pi(const Pi*) final;
    const Def* rewrite_mut_Pi(Pi*) final;
    void finalize() final;

    FVAnalysis fvana_{};
    DefSet convertable_{};
    DefSet closureCallsites_{};

    GIDNodeMap<const Lam*, Stub> closures_{};
    std::queue<const Lam*> worklist_{};
};

} // namespace mim::plug::clos2
