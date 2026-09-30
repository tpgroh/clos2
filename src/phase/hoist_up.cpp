#include "mim/plug/clos2/phase/hoist_up.h"

#include "mim/def.h"
#include "mim/phase.h"

using namespace mim;
using namespace mim::plug;
using namespace mim::plug::clos2;

DefVec HoistUp::getFreeTypeVars(const Def* type) {
    auto fvset = fvana_.free_vars(type);
    // TODO: order the free vars in a deterministic way which only depends on the type.
    // For example the order in which they would appear in the written version of the IR
    auto old_fvs = DefVec{fvset.begin(), fvset.end()};
    auto fvs     = DefVec{fvset.size(), [&](auto i) { return rewrite(old_fvs[i]); }};

    return fvs;
}

template<bool ismut>
const Def* HoistUp::hoistUp(const Lam* lam) {
    auto& w = new_world();

    push();

    // select the free vars to lambda lift
    auto fvset = fvana_.free_vars(lam->type());
    log().i("HoistUp {} with free type vars {}", lam, fvset);
    auto old_fvs = DefVec{fvset.begin(), fvset.end()};
    auto fvs     = DefVec{fvset.size(), [&](auto i) { return rewrite(old_fvs[i]); }};

    auto environment = w.tuple(fvs);

    log().i("HoistUp {} environment {}", lam, environment);

    // get the type universe level of the outer lambda
    auto umax_set = fvset;
    umax_set.insert(lam);
    auto outer_pi_type = old_world().umax<UMax::Term>(umax_set);

    // create the pi type of the outer lambda
    auto outer_pi = w.mut_pi(rewrite(outer_pi_type));
    outer_pi->set_dom(environment->type());
    auto N = outer_pi->var();

    if (fvs.size() == 1)
        map(old_fvs[0], N);
    else
        for (size_t i = 0; i < fvs.size(); i++)
            map(old_fvs[i], w.extract(N, i));

    // create outer lambda
    log().i("outer lam doms {}", outer_pi->doms());
    auto outer_lam = w.mut_lam(outer_pi);

    if (fvs.size() == 1)
        map(old_fvs[0], outer_lam->var());
    else
        for (size_t i = 0; i < fvs.size(); i++)
            map(old_fvs[i], outer_lam->var(outer_lam->num_doms(), i));

    // use RWPhase to get the inner lambda
    const Def* body;
    if constexpr (ismut)
        body = RWPhase::rewrite_mut_Lam(lam->as_mut<Lam>());
    else
        body = RWPhase::rewrite_imm_Lam(lam);

    outer_pi->set_codom(body->type());
    log().i("outer lam codom {}", outer_pi->codom());
    outer_lam->set(false, body);

    pop();

    return map(lam, w.app(outer_lam, environment));
}

template<bool ismut>
const Def* HoistUp::hoistUp(const Pi* pi) {
    // TODO: implement
    return nullptr;
}

const Def* HoistUp::rewrite_imm_App(const App* app) {
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
