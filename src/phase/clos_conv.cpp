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

void ClosConv::map_fvs_to_ext(const DefVec& fvs, const Def* env) {
    // TODO: set sym

    if (fvs.size() == 1) {
        map(fvs[0], env);
        return;
    }

    for (size_t i = 0; i < fvs.size(); i++)
        map(fvs[i], env->proj(i));
}

// (Lam x : A . e)+    :=    (procedure, env)
// where procedure  =  Lam (n:Sigma (free vars of e and A)) (x : let [x_i...] = n in (A)+)   . let [x_i...] = n in (e)+
// where env        =  [x_i...]
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
    Pi* proc_pi;
    {
        // BUG: to enforce the calling convention I should use ⦃ environment ⦄ instead of env_type - as a reminder
        // I have to provide a proof that the procedure is only called with the environment which was created for it.
        auto env_type     = environment->type();
        auto old_lam_type = old_lam->type();

        // get the type level sig has to live on
        // NOTE: I'm using umax to find the right universe level on which this pi has to live.
        // I'm quite sure that it has to live one universe above env_type and old_lam_type,
        // TODO: check if those are correct. this can be check by testing examples, the type checker will do the work
        // BUG: the rewrite can leak stuff, as a hotfix I'm doing this in a new scope which I delete directly afterwards
        // TODO: I should be able to remove the push pop here when first unrolling old_dom to a universe before
        // rewriting
        push();
        auto p_type   = w.umax<UMax::Type>({env_type, rewrite(old_lam_type)});
        auto sig_type = w.umax<UMax::Type>({env_type, rewrite(old_lam_type->dom())});
        pop();

        proc_pi = w.mut_pi(p_type, false);

        // create sigma type for domain
        push();
        auto sig = w.mut_sigma(sig_type, 2);   // domain must be a dependant pair
        sig->set(0, env_type);                 // first entry is the environment
        map_fvs_to_ext(old_fvs, sig->proj(0)); // the argument type might depend on the environment
        auto arg_type = rewrite(old_lam_type->dom());
        sig->set(1, arg_type); // the second entry is the argument
        proc_pi->set_dom(sig);

        // BUG: maybe not possible if the old_lam was immutable -> has no var
        //      In this case I would expect the arg to be bottom
        auto [env, arg] = proc_pi->vars<2>();
        map_fvs_to_ext(old_fvs, env); // the codom might depend on the environment
        if (auto m_old_pi = old_lam_type->isa_mut<Pi>())
            map(m_old_pi->var(), arg); // the codom might depend on the argument
        auto new_codom = rewrite(old_lam_type->codom());
        proc_pi->set_codom(new_codom);

        pop();
    }

    // setup the outer lambda
    auto procedure = w.mut_lam(proc_pi);
    procedure->set(old_lam->dbg_key())->debug_prefix("procedure_");
    // BUG: maybe not possible if old_lam was immutable thus has no var
    auto [env, arg] = procedure->vars<2>();

    // create new scope to prevent leaking stuff
    push();

    // the body can depend on the environment and on the argument
    map_fvs_to_ext(old_fvs, env);
    if (auto mut_old_lam = old_lam->isa_mut<Lam>()) map(mut_old_lam->var(), arg);

    // now rewrite the body
    auto body = rewrite(old_lam->body());
    procedure->set(false, body);

    // cleanup the environment to prevent leaking stuff
    pop();

    assert(procedure->is_closed());

    // use partial application with @ff filter to delay it
    // NOTE:this is the CC-CC to CC translation of a closure
    // BUG: this is not allowed : procedure requires a tuple (env, arg)
    // this will be solved by having a real closure representation and modifying the call site
    return map(old_lam, w.app(procedure, environment));
}

const Def* ClosConv::rewrite_imm_Lam(const Lam* old_lam) {
    // dont close axioms
    if (is_bootstrapping()) return RWPhase::rewrite_imm_Lam(old_lam);

    // BUG: hotfix
    if (old_lam->sym() == "main") return RWPhase::rewrite_imm_Lam(old_lam);

    return rewrite_lam_to_clos(old_lam);
}

const Def* ClosConv::rewrite_mut_Lam(Lam* old_lam) {
    // dont close axioms
    if (is_bootstrapping()) return RWPhase::rewrite_mut_Lam(old_lam);

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
