#pragma once
#include <optional>
#include <queue>
#include <utility>

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

        const Def* env;
        Lam* code;

        const Def* pack();
        static std::optional<std::pair<const Lam*, const Def*>> isa_closure(const Def*);
    };

    const Stub& get_Stub(const Lam*);
    const Def* rewrite_body(Stub&, const Lam*);

    bool analyze() final;
    const Def* rewrite_imm_App(const App*) final;

    FVAnalysis fvana_{};
    DefSet convertable_{};
    DefSet closureCallsites_{};

    GIDNodeMap<const Lam*, Stub> closures_{};
    std::queue<const Lam*> worklist_{};
};

} // namespace mim::plug::clos2
