#include "mim/plug/clos2/phase/clos_conv.h"

#include "mim/def.h"
#include "mim/phase.h"

using namespace mim;
using namespace mim::plug;
using namespace mim::plug::clos2;

/*
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

*/

const Def* ClosConv::rewrite_mut_Pi(Pi* pi) {
    if (Pi::isa_cn(pi)) return Closure::closure_type(rewrite(pi->dom()));
    return RWPhase::rewrite_mut_Pi(pi);
}

const Def* ClosConv::rewrite_imm_Pi(const Pi* pi) {
    if (Pi::isa_cn(pi)) return Closure::closure_type(rewrite(pi->dom()));
    return RWPhase::rewrite_imm_Pi(pi);
}

const Def* ClosConv::rewrite_procedure(Axm::IsA<anno, App> annotated) {
    assert(annotated.id() == anno::closure);
    
    log().i("rewrite procedure {}", annotated);

    auto app = annotated->arg()->as<App>();
    auto& w = new_world();
    auto old_proc = app->callee()->as_mut<Lam>();
    auto old_lam = old_proc->body()->as<Lam>();
    auto old_env = app->arg();

    log().i("proc {}:{}", old_proc, old_proc->type());
    log().i("lam {}:{}", old_lam, old_lam->type());
    log().i("env {}:{}", old_env, old_env->type());

    Lam* proc;
    if (auto it = procedures_.find(old_proc); it != procedures_.end())
        proc = it->second;
    else {
        auto dom = w.mut_sigma(rewrite(old_proc->type()->type()), 2);
        dom->set(0, rewrite(old_proc->dom()));
        dom->set(1, rewrite(old_lam->dom()));
        proc = w.mut_con(dom);
        proc->set(old_proc->dbg_key());

        procedures_[old_proc] = proc;

        push();
        map(old_proc->var(), proc->var(2,0));
        if (auto mlam = old_lam->isa_mut<Lam>())
            map(mlam->var(), proc->var(2,1));
        proc->set(rewrite(old_lam->filter()), rewrite(old_lam->body()));
        pop();
    }

    return Closure::pack(proc, rewrite(old_env), rewrite(old_lam->dom()));
}
