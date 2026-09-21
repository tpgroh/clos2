#include "mim/plug/clos2/phase/clos_conv.h"

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

const Def* ClosConv::rewrite_lam_to_clos(const Lam* old_lam) {
    auto& w = new_world();

    log().i("CC {} closing", old_lam);

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

    // BUG: to enforce the calling convention I should use ⦃ environment ⦄ instead of env_type - as a reminder
    // I have to provide a proof that the procedure is only called with the environment which was created for it.
    auto env_type     = environment->type();
    auto old_lam_type = old_lam->type();
    assert(Pi::isa_cn(old_lam_type));

    // get the type level sig has to live on
    // NOTE: I'm using umax to find the right universe level on which this pi has to live.
    // I'm quite sure that it has to live one universe above env_type and old_lam_type,
    // TODO: check if those are correct. this can be check by testing examples, the type checker will do the work
    // BUG: the rewrite can leak stuff, as a hotfix I'm doing this in a new scope which I delete directly afterwards
    // TODO: I should be able to remove the push pop here when first unrolling old_dom to a universe before
    // rewriting

    // push();
    auto sig_type = w.type(); // w.umax<UMax::Type>({env_type->type(), rewrite(old_lam_type->dom()->type())});
    // pop();

    // create sigma type for domain
    push();
    auto sig = w.mut_sigma(sig_type, 2);   // domain must be a dependant pair
    sig->set(0, env_type);                 // first entry is the environment
    map_fvs_to_ext(old_fvs, sig->proj(0)); // the argument type might depend on the environment
    auto arg_type = DefVec{old_lam_type->num_doms(), [&](auto i) {
                               auto r = i == old_lam_type->num_doms() - 1 && Pi::isa_returning(old_lam_type) && false
                                          ? w.cn(rewrite(old_lam_type->ret_dom()))
                                          : rewrite(old_lam_type->dom(i));
                               log().i("CC {} dom {}  {} ~> {}", old_lam, i, old_lam_type->dom(i), r);
                               return r;
                           }};
    log().i("CC {} num_doms {}", old_lam, old_lam_type->num_doms());
    log().i("CC {} isa_retu {}", old_lam, Pi::isa_returning(old_lam_type) != nullptr);
    log().i("CC {} new arg_type {}", old_lam, arg_type);
    sig->set(1, w.sigma(arg_type)); // the second entry is the argument
    pop();

    // setup the outer lambda
    auto procedure = w.mut_con(sig);
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

    log().i("CC {} environment {} : {}", old_lam, environment, environment->type());
    log().i("CC {} procedure {} : {}", old_lam, procedure, procedure->type());

    auto ct   = clos_type(old_lam_type);
    auto clos = w.tuple(ct, {env_type, environment, procedure});
    log().w("CC {} clos {}:{}:{}", old_lam, clos, clos->type(), clos->type()->type());
    return clos;
}

const Def* ClosConv::rewrite_imm_Lam(const Lam* old_lam) {
    // dont close axioms
    if (is_bootstrapping()) return RWPhase::rewrite_imm_Lam(old_lam);

    // BUG: hotfix
    // if (old_lam->sym() == "main") return RWPhase::rewrite_imm_Lam(old_lam);

    return rewrite_lam_to_clos(old_lam);
}

const Def* ClosConv::rewrite_mut_Lam(Lam* old_lam) {
    // dont close axioms
    if (is_bootstrapping()) return RWPhase::rewrite_mut_Lam(old_lam);

    // BUG: hotfix
    // if (old_lam->sym() == "main") return RWPhase::rewrite_mut_Lam(old_lam);

    return rewrite_lam_to_clos(old_lam);
}

const Def* ClosConv::clos_type(const Pi* old_pi) {
    assert(Pi::isa_cn(old_pi));

    auto& w = new_world();

    log().i("CT {}", old_pi);

    auto new_doms = DefVec{old_pi->num_doms(), [&](auto i) {
                               auto r = i == old_pi->num_doms() - 1 && Pi::isa_returning(old_pi) && false
                                          ? w.cn(rewrite(old_pi->ret_dom()))
                                          : rewrite(old_pi->dom(i));
                               log().i("CT {} dom {}  {} ~> {}", old_pi, i, old_pi->dom(i), r);
                               return r;
                           }};

    log().i("CT {} num_doms {}", old_pi, old_pi->num_doms());
    log().i("CT {} isa_returning {}", old_pi, Pi::isa_returning(old_pi) != nullptr);
    log().i("CT {} new_doms {}", old_pi, new_doms);

    // BUG: the type level of N is in general wrong and requires impredicativity
    // auto sig = w.mut_sigma(w.umax<UMax::Type>(new_doms), 3);
    auto sig = w.mut_sigma(w.type<1>(), 3);
    sig->set(0, w.type());
    auto N = sig->var(0);
    N->set("N");
    sig->set(1, N);
    sig->set(2, w.cn({N, w.sigma(new_doms)}, old_pi->is_implicit()));

    log().i("CT {} rewrite to {}", old_pi, sig);

    return sig;
}

const Def* ClosConv::rewrite_mut_Pi(Pi* pi) {
    log().i("Pi {} (mut)", pi);
    if (!is_bootstrapping() && Pi::isa_cn(pi)) return clos_type(pi);
    log().i("Pi {} (mut) with map", pi);
    return RWPhase::rewrite_mut_Pi(pi);
}

const Def* ClosConv::rewrite_imm_Pi(const Pi* pi) {
    log().i("Pi {} (imm)", pi);
    if (!is_bootstrapping() && Pi::isa_cn(pi)) return clos_type(pi);
    log().i("Pi {} (imm) with map", pi);
    return RWPhase::rewrite_imm_Pi(pi);
}

void ClosConv::rewrite_external(Def* old_mut) {
    if (is_bootstrapping()) return RWPhase::rewrite_external(old_mut);

    auto new_def = rewrite_root(old_mut);

    // TODO: clos detection
    if (auto tup = new_def->isa_imm<Tuple>()) {
        auto [_, _, proc] = tup->projs<3>();
        proc->as_mut()->externalize();
    } else
        new_def->as_mut()->externalize();
}

const Def* ClosConv::rewrite_imm_App(const App* app) {
    if (is_bootstrapping()) return RWPhase::rewrite_imm_App(app);

    auto callee = app->callee();
    auto arg    = app->arg();

    log().i("APP {} callee {}:{} arg {}:{}", app, callee, callee->type(), arg, arg->type());

    callee = rewrite(callee);
    arg    = rewrite(arg);

    log().i("APP {} callee {}:{} arg {}:{}", app, callee, callee->type(), arg, arg->type());

    if (!callee->type()->isa<Pi>()) {
        log().i("callee {} does not have a Pi type, thus it is a closure", callee);
        auto [_, env, proc] = callee->projs<3>();
        log().i("prc {}:{}", proc, proc->type());
        log().i("env {}:{}", env, env->type());
        log().i("arg {}:{}", arg, arg->type());
        new_world().tuple({callee, arg})->dot("app.dot", {.follow_types = true});
        return new_world().app(proc, {env, arg});
    }

    return RWPhase::rewrite_imm_App(app);
}
