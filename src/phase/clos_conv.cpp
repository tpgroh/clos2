#include "mim/plug/clos2/phase/clos_conv.h"

#include <format>

#include "mim/def.h"
#include "mim/lattice.h"
#include "mim/phase.h"

using namespace mim;
using namespace mim::plug;
using namespace mim::plug::clos2;

bool ClosConv::analyze() {
    auto& w = old_world();

    log().i("this is what reached clos2");
    w.dump();
    // w.dot("middle.dot", {.all_annexes = true});

    return false;
}

// create fn type
const Pi* ClosConv::create_fn_type(const Pi* old_lam_type, const DefVec& old_fvs, const Def* n) {
    auto& w = n->world();

    // use new scope to prevent leaking
    push();

    // rewrite domain A with let [x_i...] = n in A
    if (old_fvs.size() == 1)
        map(old_fvs[0], n->set(old_fvs[0]->dbg_key())->debug_prefix("env_"));
    else
        for (size_t i = 0; i < old_fvs.size(); i++)
            map(old_fvs[i], n->proj(i)->set(old_fvs[i]->dbg_key())->debug_prefix(std::format("env_ext_{}_", i)));
    auto new_dom = rewrite(old_lam_type->dom());

    // rewrite codomain B with let [x_i...] = n in B while allowing B to depend on A and construct the possbily mutable
    // pi
    const Pi* fn_pi;
    if (auto old_pi = old_lam_type->isa_mut<Pi>()) {
        auto pi = w.mut_pi(rewrite(old_pi->type()), old_pi->is_implicit());
        pi->set_dom(new_dom);
        map(old_pi->var(), pi->var()); // B might depend on x
        auto new_codom = rewrite(old_lam_type->codom());
        pi->set_codom(new_codom);

        fn_pi = pi;
    } else {
        auto new_codom = rewrite(old_lam_type->codom());

        fn_pi = w.pi(new_dom, new_codom, old_lam_type->is_implicit());
    }

    // leave scope to prevent leaking
    pop();

    return fn_pi;
}

// (Lam x : A . e)+    :=    (procedure, env)
// where procedure  =  Lam (n:Sigma (free vars of e and A)) (x : let [x_i...] = n in (A)+)   . let [x_i...] = n in (e)+
// where env        =  [x_i...]
// NOTE: I'm using curried application of the procedure with the env given by the CC-CC to CC translation (M-CLO)
//

const Def* ClosConv::rewrite_lam_to_clos(const Lam* old_lam) {
    auto& w = new_world();

    // get free vars
    auto fvs_set = fvana_.free_vars(old_lam);

    // construct environment
    // TODO: to prevent problems in case the order changes while working with this set. No Idea if that is even possible
    DefVec old_fvs{fvs_set.begin(), fvs_set.end()};
    DefVec new_fvs;
    new_fvs.reserve(old_fvs.size());
    for (size_t i = 0; i < old_fvs.size(); i++)
        new_fvs.push_back(rewrite(old_fvs[i])->set<true>(old_fvs[i]->dbg_key())->debug_prefix("environment_"));
    const Def* environment = w.tuple(new_fvs);
    if (old_fvs.size() > 1) environment->debug_prefix("environment_");

    // create procedure type
    // BUG: to enforce the colling convention I should use ⦃ environment ⦄ instead of env_type - as a reminder
    // I have to provide a proof that the procedure is only called with the environment which was created for it.
    auto env_type     = environment->type();
    auto old_lam_type = old_lam->type();

    // NOTE: I'm using umax to find the right universe level on which this pi has to live.
    // I'm quite sure that it has to live one universe above env_type and old_lam_type,
    // TODO: I have to check that
    // BUG: the rewrite of old_lam_type leaks environemnt. thus I do that in a new scope to clean that up.
    // if possible I should do this any other way... for example get the universe level and rewrite that.
    push();
    auto p_pi_type = w.umax<UMax::Type>(Defs{env_type, rewrite(old_lam_type)});
    // TODO: add assert for p_pi_type to be * or □
    pop();

    // create procedure type
    auto p_pi = w.mut_pi(p_pi_type, false);
    p_pi->set_dom(env_type);
    p_pi->set_codom(create_fn_type(old_lam_type, old_fvs, p_pi->var()));

    // setup the outer lambda
    // BUG: if old_lam was immutable, does the inner lambda also have to be immutable?
    // or is it OK to use mut_lam.
    auto procedure = w.mut_lam(p_pi);
    auto fn        = w.mut_lam(create_fn_type(old_lam_type, old_fvs, procedure->var()));
    procedure->set(old_lam->dbg_key())->debug_prefix("procedure_");
    auto env = procedure->var()->set("env");
    auto arg = fn->var()->set("arg");
    procedure->set(false, fn);

    // create new environment to prevent leaking stuff
    push();

    // setup the inner lambda
    if (old_fvs.size() == 1)
        map(old_fvs[0], env);
    else
        for (size_t i = 0; i < old_fvs.size(); i++)
            map(old_fvs[i], env->proj(i)->set(std::format("env_ext_{}", i)));
    if (auto mut = old_lam->isa_mut<Lam>()) map(mut->var(), arg);

    // now rewrite the body
    auto body   = rewrite(old_lam->body());
    auto filter = rewrite(old_lam->filter());
    fn->set(filter, body);

    // cleanup the environment to prevent leaking stuff
    pop();

    assert(procedure->is_closed());

    // use partial application with @ff filter to delay it
    // NOTE:this is the CC-CC to CC translation of a closure
    return map(old_lam, w.app(procedure, environment));
}

const Def* ClosConv::rewrite_imm_Lam(const Lam* old_lam) {
    // BUG: hotfix
    if (old_lam->sym() == "main") return RWPhase::rewrite_imm_Lam(old_lam);

    return rewrite_lam_to_clos(old_lam);
}

const Def* ClosConv::rewrite_mut_Lam(Lam* old_lam) {
    // BUG: hotfix
    if (old_lam->sym() == "main") return RWPhase::rewrite_mut_Lam(old_lam);

    return rewrite_lam_to_clos(old_lam);
}

void ClosConv::rewrite_external(Def* old_mut) {
    auto new_def = rewrite_root(old_mut);

    if (auto app = new_def->isa_imm<App>()) {
        auto proc = app->callee();
        proc->as_mut()->externalize();
    } else
        new_def->as_mut()->externalize();
}
