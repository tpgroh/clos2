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
    w.dot("middle.dot");

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
        map(fvs[i], new_world().extract(env, i));
}

const Def* ClosConv::get_procedure(const DefVec& fvs, const Def* env_type, const Lam* old_lam) {
    log().i("CC {} closing", old_lam);

    auto& w           = new_world();
    auto old_lam_type = old_lam->type();

    log().i("CC {} env_type {}:{}", old_lam, env_type, env_type->type());

    // create sigma type for domain
    push();
    // TODO: rewrite(old_world().umax<UMax::Type>({old_lam_type->dom(), old_world().type()}));
    auto sig = w.mut_sigma(2);                     // domain must be a dependant pair
    sig->set(0, env_type);                         // first argument is the environment
    map_fvs_to_ext(fvs, w.unwrap(sig->var(2, 0))); // the actual arguments type might depend on the environment
    sig->set(1, rewrite(old_lam_type->dom()));     // the second entry is the actual argument
    pop();

    log().i("CC {} procedure domain type {}:{}", old_lam, sig, sig->type());

    // setup procedure lamda
    auto procedure = w.mut_con(sig);
    procedure->set(old_lam->dbg_key())->debug_prefix("procedure_");
    auto [env, arg] = procedure->vars<2>();

    // rewrite body
    push();
    map_fvs_to_ext(fvs, w.unwrap(env));
    if (auto mut_old_lam = old_lam->isa_mut<Lam>()) {
        log().i("mapping  {} to {}", mut_old_lam->var(), arg);
        map(mut_old_lam->var(), arg);
    }
    auto body = rewrite(old_lam->body());
    procedure->set(false, body);
    if (!procedure->is_closed()) log().e("CC {} prc has fvs {}", old_lam, procedure->free_vars());
    procedure->dot("crash.dot", {.follow_types = true});
    // FIXME: using singletons for environment this fails because something from the singleon's value gets included in
    // the type of things assert(procedure->is_closed()); ();
    //

    return procedure;
}

const Def* ClosConv::closure_pack(const Lam* old_lam) {
    auto& w = new_world();

    // create the environment
    auto fvset = fvana_.free_vars(old_lam);
    DefVec fvs;
    for (auto v : fvset)
        fvs.push_back(v);

    log().i("CP {} with fvset {}", old_lam, fvset);

    // create the environment
    DefVec new_fvs{fvs.size(), [&](auto i) { return rewrite(fvs[i]); }};
    const Def* environment = w.wrap(w.tuple(new_fvs));
    auto environment_type  = environment->type();
    log().i("CP {} environment {}:{}", old_lam, environment, environment_type);
    auto procedure = get_procedure(fvs, environment_type, old_lam);

    // FIXME: use clos_type function to prevent defining closure representation in two places
    auto clos = w.tuple(/* clostype, */ {environment_type, environment, procedure})
                    ->set(old_lam->sym())
                    ->debug_prefix("closure_");

    log().i("PK {} env_type {}", old_lam, environment_type);
    log().i("PK {} environment {}", old_lam, environment);
    log().i("PK {} procedure_type {}", old_lam, procedure->type());
    log().i("PK {} as {}:{}", old_lam, clos, clos->type());

    return clos;
}
const Def* ClosConv::closure_apply(const Def* clos, const Def* arg) {
    auto& w             = new_world();
    auto [_, env, proc] = clos->projs<3>();

    log().i("UP {}", clos);
    log().i("prc {}:{}", proc, proc->type());
    log().i("env {}:{}", env, env->type());
    log().i("arg {}:{}", arg, arg->type());

    w.tuple({clos, arg})->dot("crash.dot", {.follow_types = false});

    return w.app(proc, {env, arg});
}

const Def* ClosConv::rewrite_imm_Lam(const Lam* old_lam) {
    // dont close axioms
    if (is_bootstrapping()) return RWPhase::rewrite_imm_Lam(old_lam);

    return map(old_lam, closure_pack(old_lam));
}

const Def* ClosConv::rewrite_mut_Lam(Lam* old_lam) {
    // dont close axioms
    if (is_bootstrapping()) return RWPhase::rewrite_mut_Lam(old_lam);

    return map(old_lam, closure_pack(old_lam));
}

const Def* ClosConv::procedure_type(const Pi* pi, const Def* env_type) {
    auto& w = new_world();

    // TODO: move the stuff from clos_pack here

    return w.cn({env_type, rewrite(pi->dom())});
}

const Def* ClosConv::clos_type(const Pi* pi) {
    auto& w = new_world();

    auto sig = w.mut_sigma(3);
    sig->set(0, w.type());
    auto N = sig->var(3, 0);
    N->set("N");
    sig->set(1, N);
    sig->set(2, procedure_type(pi, N));

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
        auto proc = tup->proj(3, 2);
        proc->as_mut<Lam>()->externalize();
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
