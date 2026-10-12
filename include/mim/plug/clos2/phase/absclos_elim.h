#pragma once

#include <queue>

#include "mim/def.h"
#include "mim/lam.h"
#include "mim/phase.h"

#include "mim/util/types.h"

#include "mim/plug/clos2/clos2.h"

namespace mim::plug::clos2 {

namespace Closure {

inline const Def* closure_type(const Def* dom) {
    auto& w = dom->world();

    auto sig = w.mut_sigma(3);
    sig->set(0, w.type());
    auto N = sig->var(3, 0);
    sig->set(1, N);
    sig->set(2, w.cn({N, dom}));

    // to help with debugging
    sig->var(3, 0)->set("N");
    sig->var(3, 1)->set("n");
    sig->var(3, 2)->set("p");
    //sig->set("closure");

    return sig;
}

inline const Def* pack(Lam* procedure, const Def* environment, const Def* environment_type, const Def* dom) {
    auto& w       = procedure->world();
    auto clostype = closure_type(dom);
    auto clos     = w.tuple(clostype, {environment_type, environment, procedure});
    clos->set("closure");
    return clos;
}

inline const Def* closure_apply(const Def* clos, const Def* arg) {
    auto& w             = clos->world();
    auto [_, env, proc] = clos->projs<3>();

    w.log().i("UP {}", clos);
    w.log().i("prc {}:{}", proc, proc->type());
    w.log().i("env {}:{}", env, env->type());
    w.log().i("arg {}:{}", arg, arg->type());

    return w.app(proc, {env, arg});
}
}

class AbsClosElim : public RWPhase {
public:
    AbsClosElim(World& world, flags_t annex) : RWPhase(world, annex) {}

private:
    Lam* rewrite_procedure(Lam*);
    const Def* rewrite_mut_Pi(Pi*) final;
    const Def* rewrite_imm_Pi(const Pi*) final;

    const Def* create_closure(Axm::IsA<anno, App> a) {
        log().i("create closure {}", a);
        
        auto app = a->arg()->as<App>();
        auto old_proc = app->callee()->as_mut<Lam>();
        auto old_env_type = old_proc->dom();
        auto old_env = app->arg();

        auto new_proc = rewrite_procedure(old_proc);
        auto environment = rewrite(old_env);
        auto dom = rewrite(app->type()->as<Pi>()->dom());
        auto new_env_type = rewrite(old_env_type);

        return Closure::pack(new_proc, environment, new_env_type, dom);
    }

    // abstract closure elim and closure application
    const Def* rewrite_imm_App(const App* app) {
        if (auto a = Axm::isa<anno>(app)) return create_closure(a);

        auto new_arg = rewrite(app->arg());
        auto new_callee = rewrite(app->callee());

        // if the callee is not a Pi then it is a closure
        if (!new_callee->type()->isa<Pi>()) {
            log().i("detected callee {} to be a closure", new_callee->type());
            return Closure::closure_apply(new_callee, new_arg);
        }

        return RWPhase::rewrite_imm_App(app);
    }

    /* currently I'm rewriting every Pi but I have to skip the Pi of a lambda */
    const Def* rewrite_imm_Lam(const Lam* d) final {
        auto old_pi = d->type();
        auto new_type   = (old_pi->isa_mut() ? RWPhase::rewrite_mut_Pi(old_pi->as_mut<Pi>()) : RWPhase::rewrite_imm_Pi(old_pi))->as<Pi>();
        auto new_filter = rewrite(d->filter());
        auto new_body   = rewrite(d->body());
        return new_world().lam(new_type, new_filter, new_body);
    }
    const Def* rewrite_mut_Lam(Lam* d) final {
        if (!Pi::isa_cn(d->type())) return map(d, rewrite_procedure(d));
        auto old_pi = d->type();
        const Pi* new_pi = (old_pi->isa_mut() ? RWPhase::rewrite_mut_Pi(old_pi->as_mut<Pi>()) : RWPhase::rewrite_imm_Pi(old_pi))->as<Pi>();
        return rewrite_stub(d, new_world().mut_lam(new_pi));
    }

private:
    DefMap<Lam*> procedures_{};
};


} // namespace mim::plug::clos2
