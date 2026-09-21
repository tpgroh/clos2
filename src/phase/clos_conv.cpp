#include "mim/plug/clos2/phase/clos_conv.h"

#include "mim/def.h"
#include "mim/lattice.h"
#include "mim/phase.h"

using namespace mim;
using namespace mim::plug;
using namespace mim::plug::clos2;

// FIXME: This is currently only used to get the new gid's of Def's after the cleanup phase.
// Either do something useful or remove it
bool ClosConv::analyze() {
    auto& w = old_world();

    log().i("this is what reached clos2");
    w.dump();
    // w.dot("middle.dot", {.all_annexes = true});

    return false;
}

// map given fvs to extractions of env
void ClosConv::map_fvs_to_ext(const DefVec& fvs, const Def* env) {
    // TODO: maybe set sym

    if (fvs.size() == 1) {
        map(fvs[0], env);
        return;
    }

    for (size_t i = 0; i < fvs.size(); i++)
        map(fvs[i], env->proj(i));
}

const Def* ClosConv::get_environment(const DefVec& fvs) {
    auto& w = new_world();

    // TODO: maybe also set sym using ->set<true> (fvs[i]->dbg_key())->debug_prefix("environment_")
    DefVec new_fvs{fvs.size(), [&](auto i) { return rewrite(fvs[i]); }};
    const Def* environment = w.tuple(new_fvs);
    // TODO: maybe set sym
    // if (fvs.size() > 1) environment->debug_prefix("environment_");

    return environment;
}

const Def* ClosConv::get_procedure(const DefVec& fvs, const Def* env_type, const Lam* old_lam) {
    log().i("CC {} closing", old_lam);

    auto& w           = new_world();
    auto old_lam_type = old_lam->type();
    assert(Pi::isa_cn(old_lam_type));

    log().i("CC {} env_type {}:{}", old_lam, env_type, env_type->type());

    // create sigma type for domain
    push();
    auto sig = w.mut_sigma(w.type<1>(), 2);        // domain must be a dependant pair
    sig->set(0, env_type);                         // first argument is the environment
    map_fvs_to_ext(fvs, sig->proj(0));             // the actual arguments type might depend on the environment
    auto arg_type = rewrite(old_lam_type->doms()); // rewrite the actual arguments
    sig->set(1, w.sigma(arg_type));                // the second entry is the actual argument
    pop();

    // setup the outer lambda
    auto procedure = w.mut_con(sig);
    procedure->set(old_lam->dbg_key())->debug_prefix("procedure_");
    // BUG: maybe not possible if old_lam was immutable thus has no var
    auto [env, arg] = procedure->vars<2>();

    // rewrite body
    push();
    map_fvs_to_ext(fvs, env);
    if (auto mut_old_lam = old_lam->isa_mut<Lam>()) map(mut_old_lam->var(), arg);
    auto body = rewrite(old_lam->body());
    procedure->set(false, body);
    log().w("CC {} prc has fvs {}", old_lam, procedure->free_vars());
    // assert(procedure->is_closed());
    pop();

    return procedure;
}

const Def* ClosConv::closure_pack(const Lam* old_lam) {
    auto& w = new_world();

    // create the environment
    auto fvset = fvana_.free_vars(old_lam);
    DefVec fvs;
    for (auto v : fvset)
        fvs.push_back(v);

    // get the environment
    auto environment      = get_environment(fvs);
    auto environment_type = w.uniq(environment);
    auto procedure        = get_procedure(fvs, environment_type, old_lam);

    auto clostype = w.mut_sigma(w.type<1>(), 3); // FIXME:
    clostype->set(0, w.type());
    clostype->set(1, clostype->var(0));
    clostype->set(2, w.cn(clostype->var(0), procedure->type()->as<Pi>()->dom(1)));

    return w.tuple(clostype, {environment_type, environment, procedure});
}
const Def* ClosConv::closure_apply(const Def* clos, const Def* arg) {
    auto [_, env, proc] = clos->projs<3>();

    log().i("prc {}:{}", proc, proc->type());
    log().i("env {}:{}", env, env->type());
    log().i("arg {}:{}", arg, arg->type());

    return new_world().app(proc, {env, arg});
}

const Def* ClosConv::rewrite_imm_Lam(const Lam* old_lam) {
    // dont close axioms
    if (is_bootstrapping()) return RWPhase::rewrite_imm_Lam(old_lam);

    return closure_pack(old_lam);
}

const Def* ClosConv::rewrite_mut_Lam(Lam* old_lam) {
    // dont close axioms
    if (is_bootstrapping()) return RWPhase::rewrite_mut_Lam(old_lam);

    return closure_pack(old_lam);
}

const Def* ClosConv::clos_type(const Pi* old_pi) {
    assert(Pi::isa_cn(old_pi));

    auto& w = new_world();

    auto new_doms = DefVec{old_pi->num_doms(), [&](auto i) { return rewrite(old_pi->dom(i)); }};

    auto sig = w.mut_sigma(w.type<1>(), 3);
    sig->set(0, w.type());
    auto N = sig->var(0);
    N->set("N");
    sig->set(1, N);
    sig->set(2, w.cn({N, w.sigma(new_doms)}, old_pi->is_implicit()));

    return sig;
}

const Def* ClosConv::rewrite_mut_Pi(Pi* pi) {
    if (!is_bootstrapping() && Pi::isa_cn(pi)) return clos_type(pi);
    return RWPhase::rewrite_mut_Pi(pi);
}

const Def* ClosConv::rewrite_imm_Pi(const Pi* pi) {
    if (!is_bootstrapping() && Pi::isa_cn(pi)) return clos_type(pi);
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
        return closure_apply(callee, arg);
    }

    return RWPhase::rewrite_imm_App(app);
}
