#include "mim/plug/clos2/phase/clos_conv.h"

#include "mim/def.h"
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
    // w.dot("middle.dot");

    return false;
}

Lam* ClosConv::get_procedure(const DefVec& fvs, const Def* env_type, const Lam* old_lam) {
    log().i("CC {} closing", old_lam);

    auto& w           = new_world();
    auto old_lam_type = old_lam->type();

    log().i("CC {} env_type {}:{}", old_lam, env_type, env_type->type());

    // create sigma type for domain
    push();
    auto sig = w.mut_sigma(2);
    sig->set(0, env_type);
    auto env = sig->var(2, 0)->set("env");
    if (fvs.size() == 1) {
        env->set(fvs[0]->dbg_key());
        map(fvs[0], env);
    } else
        for (size_t i = 0; i < fvs.size(); i++) {
            auto f = fvs[i];
            auto v = w.extract(env, i);
            v->set(f->dbg_key());
            map(f, v);
        }
    sig->set(1, rewrite(old_lam_type->dom())); // the second entry is the actual argument
    pop();

    log().i("CC {} procedure domain type {}:{}", old_lam, sig, sig->type());

    // setup procedure lamda
    auto procedure = w.mut_con(sig);
    procedure->set(old_lam->dbg_key())->debug_prefix("procedure_");

    // register body rewrite for finalize
    worklist_.push(old_lam);

    return procedure;
}

void ClosConv::rewrite_procedure_body(const Lam* old_lam) {
    auto& closure = closures_.at(old_lam);

    auto& w        = new_world();
    auto& fvs      = closure.fvs;
    auto procedure = closure.procedure;

    auto [env, arg] = procedure->vars<2>();
    env->set("env");
    arg->set("arg");

    push();
    if (fvs.size() == 1)
        map(fvs[0], env);
    else
        for (size_t i = 0; i < fvs.size(); i++)
            map(fvs[i], w.extract(env, i));
    if (auto mut_old_lam = old_lam->isa_mut<Lam>()) map(mut_old_lam->var(), arg);
    auto body = rewrite(old_lam->body());
    procedure->set(false, body);
    pop();

    // TODO: we always want to externalize procedures
    if (!procedure->is_closed())
        log().e("CC {} prc has fvs {}", old_lam, procedure->free_vars());
    else if (old_lam->is_external())
        procedure->externalize();
}

const Def* ClosConv::get_closure(const Lam* old_lam) {
    if (auto it = closures_.find(old_lam); it != closures_.end()) return it->second.pack();
    auto& w = new_world();

    // create the environment
    auto fvset = fvana_.free_vars(old_lam);
    DefVec fvs;
    for (auto v : fvset)
        fvs.push_back(v);

    log().i("CP {} with fvset {} libmim fvs {}", old_lam, fvset, old_lam->free_vars());

    // create the environment
    DefVec new_fvs{fvs.size(), [&](auto i) { return rewrite(fvs[i]); }};
    const Def* environment = w.tuple(new_fvs);
    auto environment_type  = environment->type();
    log().i("CP {} environment {}:{}", old_lam, environment, environment_type);
    auto procedure = get_procedure(fvs, environment_type, old_lam);

    closures_.try_emplace(old_lam, fvs, environment, procedure);
    auto clos = closures_[old_lam].pack();

    return clos;
}

const Def* ClosConv::rewrite_imm_Lam(const Lam* old_lam) {
    // dont close axioms
    if (is_bootstrapping()) return RWPhase::rewrite_imm_Lam(old_lam);

    return map(old_lam, get_closure(old_lam));
}

const Def* ClosConv::rewrite_mut_Lam(Lam* old_lam) {
    // dont close axioms
    if (is_bootstrapping()) return RWPhase::rewrite_mut_Lam(old_lam);

    return map(old_lam, get_closure(old_lam));
}

const Def* ClosConv::rewrite_mut_Pi(Pi* pi) {
    if (!is_bootstrapping() && Pi::isa_cn(pi)) return Closure::closure_type(rewrite(pi->dom()));
    return RWPhase::rewrite_mut_Pi(pi);
}

const Def* ClosConv::rewrite_imm_Pi(const Pi* pi) {
    if (!is_bootstrapping() && Pi::isa_cn(pi)) return Closure::closure_type(rewrite(pi->dom()));
    return RWPhase::rewrite_imm_Pi(pi);
}

void ClosConv::rewrite_external(Def* old_mut) {
    if (is_bootstrapping()) return RWPhase::rewrite_external(old_mut);

    auto new_def = rewrite_root(old_mut);

    // if new_def is a tuple, then it is a closure. thus it will be externalized by its rewrite
    if (!new_def->isa_imm<Tuple>()) new_def->as_mut()->externalize();
}

const Def* ClosConv::rewrite_imm_App(const App* app) {
    if (is_bootstrapping()) return RWPhase::rewrite_imm_App(app);

    auto callee = app->callee();
    auto arg    = app->arg();

    log().i("APP {} callee {}:{} arg {}:{}", app, callee, callee->type(), arg, arg->type());

    callee = rewrite(callee);
    arg    = rewrite(arg);

    log().i("APP {} callee {}:{} arg {}:{}", app, callee, callee->type(), arg, arg->type());

    if (!callee->type()->isa<Pi>()) return Closure::closure_apply(callee, arg);
    return RWPhase::rewrite_imm_App(app);
}

void ClosConv::finalize() {
    while (!worklist_.empty()) {
        auto old_lam = worklist_.front();
        worklist_.pop();

        rewrite_procedure_body(old_lam);
    }
}
