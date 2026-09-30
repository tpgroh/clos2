#include "mim/plug/clos2/phase/hoist_up.h"

#include "mim/def.h"
#include "mim/phase.h"

using namespace mim;
using namespace mim::plug;
using namespace mim::plug::clos2;

DefVec HoistUp::getFreeTypeVars(const Def* type) {
    // TODO: order the free vars in a deterministic way which only depends on the type.
    // For example the order in which they would appear in the written version of the IL

    auto fvset = fvana_.free_vars(type);
    auto fvs   = DefVec{fvset.begin(), fvset.end()};

    return fvs;
}

template<bool ismut>
const Def* HoistUp::hoistUp(const Lam* lam) {
    // Lam (x:A).e ~> Lam (n_i:T_i ...) (x:{z_i->n_i...}A) . {z_i->n_i..}e
    // z_i are the free variables of A,B in a deterministic and unambiguous order
    //
    // TODO: implement this transformation

    return nullptr;
}

template<bool ismut>
const Def* HoistUp::hoistUp(const Pi* pi) {
    // Pi x:A.B ~> Pi [n_i:T_i ..., x:{z_i -> n_i ...}A] . {z_i -> n_i ...}B
    // z_i are the free variables of A,B in a deterministic and unambiguous order
    //
    // TODO: implement this transformation

    return nullptr;
}

const Def* HoistUp::rewrite_imm_App(const App* app) {
    // foo bar ~> foo' (z_i..., bar')
    //
    // TODO: if the callee has free vars in its type we have to get those, rewrite them an apply them as the first
    // arguments before app->arg()
    return RWPhase::rewrite_imm_App(app);
}

const Def* HoistUp::rewrite_mut_Pi(Pi* pi) {
    if (is_bootstrapping() || pi->is_closed()) return RWPhase::rewrite_mut_Pi(pi);

    return hoistUp<true>(pi);
}

const Def* HoistUp::rewrite_imm_Pi(const Pi* pi) {
    if (is_bootstrapping() || pi->is_closed()) return RWPhase::rewrite_imm_Pi(pi);

    return hoistUp<false>(pi);
}

const Def* HoistUp::rewrite_imm_Lam(const Lam* old_lam) {
    if (is_bootstrapping() || old_lam->type()->is_closed()) return RWPhase::rewrite_imm_Lam(old_lam);

    return hoistUp<false>(old_lam);
}

const Def* HoistUp::rewrite_mut_Lam(Lam* old_lam) {
    if (is_bootstrapping() || old_lam->type()->is_closed()) return RWPhase::rewrite_mut_Lam(old_lam);

    return hoistUp<true>(old_lam);
}
