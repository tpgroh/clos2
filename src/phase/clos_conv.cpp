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

    w.dump();
    w.dot("middle.dot", {.all_annexes = true});

    return false;
}

// (Lam x : A . e)+    :=    (procedure, env)
// where procedure  =  Lam (n:Sigma (free vars of e and A)) (x : let [x_i...] = n in (A)+)   . let [x_i...] = n in (e)+
// where env        =  [x_i...]
// TODO: for now I will also pack the type of the environment into the closure.
// I have to think about how I can remove that
// TODO: I'm using a curried application of the procedure with the env given by the CC-CC to CC translation (M-CLO)
//

const Def* ClosConv::rewrite_lam_to_clos(const Lam* old_lam) {
    // log().d("closure converting {}", old_lam); // TODO: remove debug log
    auto& w = new_world();

    // get free vars
    auto fvs_set = fvana_.free_vars(old_lam);

    // log().d("CC {} free vars {}", old_lam, fvs_set); // TODO: remove debug log

    // construct environment
    DefVec old_fvs{fvs_set.begin(), fvs_set.end()};
    DefVec new_fvs;
    new_fvs.reserve(old_fvs.size());
    for (size_t i = 0; i < old_fvs.size(); i++)
        new_fvs.push_back(rewrite(old_fvs[i])->set<true>(old_fvs[i]->dbg_key())->debug_prefix("environment_"));
    const Def* environment = w.tuple(new_fvs);
    if (old_fvs.size() > 1) environment->debug_prefix("environment_");

    // log().d("CC {} environemt {} of type {}", old_lam, environment, environment->type()); // TODO: remove debug log

    // create new scope to prevent leaking the environment
    push();

    // create procedure type
    auto env_type     = environment->type();
    auto old_lam_type = old_lam->type();

    // create fn type
    // NOTE: I'm using umax to find the right universe level on which this pi has to live.
    // I'm quite sure that it has to live one universe above env_type and old_lam_type,
    // TODO: I have to check that
    // BUG: the rewrite of old_lam_type leaks environemnt. thus I do that in a new scope to clean that up.
    // if possible I should do this any other way... for example get the universe level and rewrite that.
    push();
    auto p_pi = w.mut_pi(w.umax<UMax::Type>(Defs{env_type, rewrite(old_lam_type)}), false);
    pop();
    p_pi->set_dom(env_type);
    auto n = p_pi->var();

    // rewrite domain A with let [x_i...] = n in A
    if (old_fvs.size() == 1) {
        auto v1 = old_fvs[0];
        auto v2 = n->set(old_fvs[0]->dbg_key())->debug_prefix("env_");
        // log().d("mapping {} to {}", v1, v2); // TODO: remove debug log
        map(v1, v2);
    } else
        for (size_t i = 0; i < old_fvs.size(); i++) {
            auto v1 = old_fvs[i];
            auto v2 = n->proj(i)->set(old_fvs[i]->dbg_key())->debug_prefix(std::format("env_ext_{}_", i));
            // log().d("mapping {} to {}", v1, v2); // TODO: remove debug log
            map(v1, v2);
        }
    auto new_dom = rewrite(old_lam_type->dom());

    // log().d("CC {} fn dom is {}", old_lam, new_dom); // TODO: remove debug log

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

    // log().d("CC {} final fn Pi is {} was {}", old_lam, fn_pi, old_lam_type); // TODO: remove debug log

    // set codomain of procedure's pi
    p_pi->set_codom(fn_pi);

    // log().d("CC {} final procedure Pi is {}", old_lam, p_pi); // TODO: remove debug log

    // setup the outer lambda
    auto procedure = w.mut_lam(p_pi);
    auto fn        = w.mut_lam(fn_pi); // BUG: does this keep right if old_lam is immutable? I would think so.
                                       // I think of a imm Lam as a mut Lam which gets an empty tuple ()
                                       // and the var() is never used
    procedure->set(old_lam->dbg_key())->debug_prefix("procedure_");
    fn->set(old_lam->dbg_key())->debug_prefix("fn_");
    auto env = procedure->var()->set("env");
    auto arg = fn->var()->set("arg");
    procedure->set(false, fn);

    // log().d("CC {} rewrite body {}", old_lam, old_lam->body()); // TODO: remove debug log

    // cleanup env
    // BUG: I think that if I do everything right this should not be needed. but to make sure that I dont leak
    // environment in any way I'll keep it for now
    pop();
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

    // log().d("CC {} set body to {} of type {}", old_lam, body, body->type()); // TODO: remove debug log
    // log().d("CC {} set filter to {}", old_lam, filter); // TODO: remove debug log
    fn->set(filter, body);

    // log().d("CC {} fn was set to {}", old_lam, fn->body()); // TODO: remove debug log

    // cleanup the environment to prevent leaking stuff
    pop();

    // BUG: every procedure should be closed.
    if (!procedure->is_closed()) {
        log().e("CC {} procedure {} is not closed, free_vars {}", old_lam, procedure, procedure->free_vars());
        procedure->dot(std::format("dot/{}.dot", procedure->sym()));
    }

    // use partial application with @ff filter to delay it
    return map(old_lam, w.app(procedure, environment));
}

const Def* ClosConv::rewrite_imm_Lam(const Lam* old_lam) { return rewrite_lam_to_clos(old_lam); }
const Def* ClosConv::rewrite_mut_Lam(Lam* old_lam) { return rewrite_lam_to_clos(old_lam); }

void ClosConv::rewrite_external(Def* old_mut) {
    log().i("rewrite external {}", old_mut);
    auto new_def = rewrite_root(old_mut);

    if (auto app = new_def->isa_imm<App>()) {
        auto proc = app->callee();
        log().e("procedure {} is closed {}, free vars {}", proc, proc->is_closed(), proc->free_vars());
        proc->as_mut()->externalize();
    } else
        new_def->as_mut()->externalize();

    // BUG: I still need to externalize, but not the closures because they are not mutable thus cannot be externalized
    return;
}

// (Pi _ : A . B)+   :=   Pi _ : (A)+ . (B)+
const Def* ClosConv::rewrite_imm_Pi(const Pi* pi) { return RWPhase::rewrite_imm_Pi(pi); }

// (Pi x : A . B)+   :=   Pi x : (A)+ . (B)+
const Def* ClosConv::rewrite_mut_Pi(Pi* pi) { return RWPhase::rewrite_mut_Pi(pi); }

// also no change thanks to the partial application of the environment
const Def* ClosConv::rewrite_imm_App(const App* old_app) { return RWPhase::rewrite_imm_App(old_app); }
