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
    auto& w = new_world();

    push();

    // Pi x:A.B ~> Pi [n_i:T_i ..., x:{z_i -> n_i ...}A] . {z_i -> n_i ...}B
    // z_i are the free variables of A,B in a deterministic and unambiguous order

    auto old_fvs = getFreeTypeVars(pi);

    // create new mutable sigma for the new domain
    auto num_doms = old_fvs.size() + pi->num_doms();
    auto sig_type = rewrite(old_world().umax<UMax::Type>({old_world().tuple(old_fvs)->type(), pi->dom()}));
    auto sig      = w.mut_sigma(sig_type, num_doms);

    // first come the lambda lifted free vars
    for (size_t i = 0; i < old_fvs.size(); i++) {
        auto f = old_fvs[i];
        auto t = f->type();
        // if this is not the case I have to make sure that the free vars here reference the domain which replaces those
        // free vars. this should be possible using VarRewriter
        assert(t->is_closed());

        sig->set(i, rewrite(t));
        auto v = sig->var(num_doms, i);
        v->set(f->sym());
        map(f, v);
    }

    // then the old doms
    for (size_t i = old_fvs.size(); i < num_doms; i++) {
        auto j = i - old_fvs.size();
        auto t = pi->dom(pi->num_doms(), j);
        sig->set(i, rewrite(t));

        // if the old dom is a mutable sigma also remap it's vars
        if (auto dom = pi->dom()->isa_mut<Sigma>()) map(dom->var(pi->num_doms(), j), sig->var(num_doms, i));
    }

    // create pi
    auto pi_type = rewrite(old_world().umax<UMax::Type>({old_world().tuple(old_fvs)->type(), pi}));
    Pi* new_pi   = w.mut_pi(pi_type, pi->is_implicit());
    new_pi->set_dom(sig);

    // TODO: I have to check if all remaps are already above.

    auto codom = rewrite(pi->codom());
    new_pi->set_codom(codom);

    pop();

    log().i("{} ~> {}", pi, new_pi);

    return new_pi;
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

    return map(pi, hoistUp<true>(pi));
}

const Def* HoistUp::rewrite_imm_Pi(const Pi* pi) {
    if (is_bootstrapping() || pi->is_closed()) return RWPhase::rewrite_imm_Pi(pi);

    // this will be maped by rewrite_immutable
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
