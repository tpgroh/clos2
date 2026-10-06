#include "mim/plug/clos2/phase/lam_lift_type.h"

#include "mim/def.h"
#include "mim/phase.h"

using namespace mim;
using namespace mim::plug;
using namespace mim::plug::clos2;

DefVec LamLiftType::getFreeTypeVars(const Def* type) {
    // TODO: order the free vars in a deterministic way which only depends on the type.
    // For example the order in which they would appear in the written version of the IL

    auto fvset = fvana_.free_vars(type);
    auto fvs   = DefVec{fvset.begin(), fvset.end()};

    return fvs;
}

template<bool ismut>
const Def* LamLiftType::hoistUp(const Lam* lam) {
    auto& w = new_world();

    push();

    // Lam (x:A).e ~> Lam (n_i:T_i ...) (x:{z_i->n_i...}A) . {z_i->n_i..}e
    // z_i are the free variables of A,B in a deterministic and unambiguous order

    auto fvs = getFreeTypeVars(lam->type());

    // create new_lam
    auto lam_type = rewrite(lam->type())->as<Pi>();
    auto new_lam  = w.mut_lam(lam_type);

    // remap free vars
    for (size_t i = 0; i < fvs.size(); i++) {
        auto f = fvs[i];
        auto n = new_lam->var(new_lam->num_vars(), i);
        n->set(f->sym());
        map(f, n);
    }
    if constexpr (ismut) {
        auto mlam = lam->as_mut<Lam>();
        for (size_t j = 0; j < mlam->num_vars(); j++) {
            auto i = j + fvs.size();
            auto a = mlam->var(mlam->num_vars(), j);
            auto n = new_lam->var(new_lam->num_vars(), i);
            n->set(a->sym());
            map(a, n);
        }
    }

    auto body = rewrite(lam->body());
    new_lam->set(rewrite(lam->filter()), body);

    // TODO: check if I want this
    if (new_lam->is_immutabilizable()) new_lam->immutabilize();

    pop();

    log().d("{} ~> {}", lam, new_lam);

    return new_lam;
}

// TODO: if I limit this for continuations I can make the transformation simpler
template<bool ismut>
const Def* LamLiftType::hoistUp(const Pi* pi) {
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

    // TODO: check if I want this
    if (new_pi->is_immutabilizable()) new_pi->immutabilize();

    pop();

    log().d("{} ~> {}", pi, new_pi);

    return new_pi;
}

const Def* LamLiftType::rewrite_imm_App(const App* app) {
    auto& w = new_world();

    // foo bar ~> foo' (z_i..., bar')

    // TODO: detect curried application.
    // currently done by checking if the callee is an App. maybe this is not the correct way
    if (is_bootstrapping() || app->callee()->isa<App>() || app->callee_type()->is_closed())
        return RWPhase::rewrite_imm_App(app);

    log().d("app {}:{} = ({}:{}) ({}:{}) ", app, app->type(), app->callee(), app->callee_type(), app->arg(),
            app->arg()->type());

    // rewrite free vars first
    auto fvs = getFreeTypeVars(app->callee_type());
    DefVec new_arg{fvs.size(), [&](auto i) { return rewrite(fvs[i]); }};
    for (size_t i = 0; i < fvs.size(); i++)
        log().d("push fv {} ~> {} as the {}'th argument'", fvs[i], new_arg[i], i);

    // and the arguments. which are preceded by the lambda lifted free vars
    for (auto a : app->args())
        new_arg.emplace_back(rewrite(a));

    // now rewrite callee
    auto new_callee = rewrite(app->callee());

    log().d("app {}", app);
    log().d("  callee {}:{}", new_callee, new_callee->type());
    auto new_args = w.tuple(new_arg);
    log().d("  args {}:{}", new_args, new_args->type());

    auto new_app = w.app(new_callee, new_arg);

    log().d("{} ~> {}", app, new_app);

    return new_app;
}

const Def* LamLiftType::rewrite_mut_Pi(Pi* pi) {
    if (is_bootstrapping() || pi->is_closed()) return RWPhase::rewrite_mut_Pi(pi);

    return map(pi, hoistUp<true>(pi));
}

const Def* LamLiftType::rewrite_imm_Pi(const Pi* pi) {
    if (is_bootstrapping() || pi->is_closed()) return RWPhase::rewrite_imm_Pi(pi);

    // this will be maped by rewrite_immutable
    return hoistUp<false>(pi);
}

const Def* LamLiftType::rewrite_imm_Lam(const Lam* old_lam) {
    if (is_bootstrapping() || old_lam->type()->is_closed()) return RWPhase::rewrite_imm_Lam(old_lam);

    return hoistUp<false>(old_lam);
}

const Def* LamLiftType::rewrite_mut_Lam(Lam* old_lam) {
    if (is_bootstrapping() || old_lam->type()->is_closed()) return RWPhase::rewrite_mut_Lam(old_lam);

    return map(old_lam, hoistUp<true>(old_lam));
}
