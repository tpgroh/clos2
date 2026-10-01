#pragma once

#include "mim/def.h"
#include "mim/lam.h"
#include "mim/phase.h"

#include "mim/plug/clos2/fv.h"

// NOTE:
// This phase should lambda lift free vars in types of lambdas.
// for this to work I require a deterministic and unambiguous way to order free vars. (TODO)
// some notes I made before I started implementing. (require rewrite an such)
// in general this is not usable for closures, as there the environment also contains free vars that might not
// appear in the type. the typical example of `use` + `get` functions where `use` takes a function (with the same
// type as `get`) shows why this cannot be deterministic. `use` cannot know which function will be passed to it.
// thus we cannot make any assumptions about the ordering of the environment in the type of the procedure of `use`.
// actually this example also shows that there is no possible closure transformation based on existentials of `use
// get` when we say `get:Idx n -> bot` where `n` is free. here we would not know where `n` would be in the
// environment of the given closure of the `get` like function. the solution I'm proposing is, that we lambda lift
// the free vars of the type before the closure conversion. this eliminates both above mentioned problems but it
// most likely limits us in when we can do this

namespace mim::plug::clos2 {

class HoistUp : public RWPhase {
public:
    HoistUp(World& world, flags_t annex)
        : RWPhase(world, annex) {}

private:
    // get deterministic ordering of free vars in @p type
    DefVec getFreeTypeVars(const Def* type);

    // TODO: currently the template vars are not required. I should just remove them after cleaning up the code

    // lambda lift @p lam
    template<bool ismut>
    const Def* hoistUp(const Lam* lam);

    // add extra domain vars to @p pi to make free vars in the type explicit
    template<bool ismut>
    const Def* hoistUp(const Pi* pi);

    const Def* rewrite_mut_Pi(Pi*) final;
    const Def* rewrite_imm_Pi(const Pi*) final;
    const Def* rewrite_mut_Lam(Lam*) final;
    const Def* rewrite_imm_Lam(const Lam*) final;
    const Def* rewrite_imm_App(const App*) final;

private:
    FVAnalysis fvana_ = {};
};

} // namespace mim::plug::clos2
