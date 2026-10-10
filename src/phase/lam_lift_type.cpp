#include "mim/plug/clos2/phase/lam_lift_type.h"

#include "mim/def.h"
#include "mim/phase.h"

using namespace mim;
using namespace mim::plug;
using namespace mim::plug::clos2;

// clang-format off
    // Lam (x:A).e ~> Lam (n_i:T_i ...) (x:{z_i->n_i...}A) . {z_i->n_i..}e
    // z_i are the free variables of A,B in a deterministic and unambiguous order
    //
    // Pi x:A.B ~> Pi [n_i:T_i ..., x:{z_i -> n_i ...}A] . {z_i -> n_i ...}B
    // z_i are the free variables of A,B in a deterministic and unambiguous order

    // foo bar ~> foo' (z_i..., bar')
// clang-format on

DefVec LamLiftType::getFreeTypeVars(const Def* type) {
    // TODO: order the free vars in a deterministic way which only depends on the type.
    // For example the order in which they would appear in the written version of the IL

    auto fvset = fvana_.free_vars(type);
    auto fvs   = DefVec{fvset.begin(), fvset.end()};

    return fvs;
}

const Def* LamLiftType::lift_pi(const Pi* pi) {
    auto& w = new_world();

    assert(Pi::isa_cn(pi));

    push();

    auto old_fvs = getFreeTypeVars(pi);

    // create new mutable sigma for the new domain
    auto num_doms = old_fvs.size() + pi->num_doms();
    auto sig_type = rewrite(old_world().umax<UMax::Type>({old_world().tuple(old_fvs)->type(), pi->dom()}));
    auto sig      = w.mut_sigma(sig_type, num_doms);

    // first come the lambda lifted free vars
    for (size_t i = 0; i < old_fvs.size(); i++) {
        auto f = old_fvs[i];
        auto t = f->type();
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
    Pi* new_pi   = w.mut_pi(pi_type, pi->is_implicit()); // TODO: does this implicit make sence?
    new_pi->set_dom(sig);

    // TODO: I have to check if all remaps are already above.
    new_pi->set_codom(w.type_bottom());

    if (new_pi->is_immutabilizable()) new_pi->immutabilize();

    pop();

    log().d("{} ~> {}", pi, new_pi);

    return new_pi;
}

const Def* LamLiftType::lift_app(const App* app) {
    auto& w = new_world();

    // foo bar ~> foo' (z_i..., bar')

    auto callee = rewrite(app->callee());
    auto fvs = getFreeTypeVars(callee->type());

    DefVec new_args{};
    new_args.reserve(app->num_args() + fvs.size());

    for (auto f : fvs) new_args.push_back(rewrite(f));
    for (auto a : app->args()) new_args.push_back(rewrite(a));

    return w.app(callee, new_args)->set(app->dbg_key());
}
