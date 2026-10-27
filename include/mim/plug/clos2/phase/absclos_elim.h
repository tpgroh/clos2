#pragma once

#include <queue>

#include "mim/def.h"
#include "mim/lam.h"
#include "mim/phase.h"

#include "mim/util/types.h"

#include "mim/plug/clos2/clos2.h"

/// Notes on the requirements for the FCC paper's optimizations
/// - Requirement 1:
///   > A typed closure abstraction must hide the type of the environment.
///   **Why?** The reason for this requirement is simply that two closures with different env types still have to be interchangeable if the
///   closed lambda had the same types.
/// - Requirement 2:
///   > A typed closure abstraction must enforce the calling convention:
///   > the code pointer is called with its packaged environment.
///   **Why?** This gives us a proof that the transformation obayed the calling convention instead of having to verify that it will always do
///   this right.
/// - Requirement 3:
///   > A typed closure abstraction should support the efficient flat closure representation and introduce no overhead.
///   **Why?** The flat closure representation reduces the number of closure allocations.
///   and as closures are slow we dont want to add additional overhead.
/// - Requirement 4:
///   > Procedures (including recursive) are directly callable through their code pointer.
///   
/// - Requirement 5:
///   > Procedures must have unrestricted signatures.
///   **Why?** This is required for well known closure optimization. It allows us calling the procedure directly without going through
///   the code pointer.
/// - Requirement 6:
///   > The IL must satisfy subject reduction.
/// - Requirement 7:
///   > A typed closure representation must enable (mutually) recursive calls without reallocating the closure.
///   **Why?** also to prevent overhead. this is enabled by requirement 3 (flat closure representation)
///
///
/// TODO:
/// - Im missing some of the requirements
///     * requirement 2: this should be possible
///     * requirement 3: here Im missing the flat closure representation
///         this should also enable requirement 7
/// - I also still have the problem of free vars accuring inside the type. in this case after hoistup the type of the argument would depend on the environment which gets
/// cast away
///   here my idea was to kep the vars free. inside the procedure's type this dependency is fine, as the type does not get thrown away there.
///   but in the actual closure type I want to inline the environment inside the type to which we cast the procedure

namespace mim::plug::clos2 {

namespace Closure {

/// create closure type `rec alpha . [Cn [alpha, dom], Env]`
inline const Def* closure_type(const Def* dom) {
    auto& w = dom->world();

    auto alpha = w.mut_sigma(dom->type(), 2);
    alpha->set("clos_type");
    alpha->set(0, w.cn({alpha, dom}));
    alpha->set(1, w.annex<clos2::Env>());
    return alpha;
}

inline const Sigma* isa_closure_type(const Def* def) {
    auto env = def->world().annex<Env>();

    // TODO: I should add more checks
    if (auto sigma = def->isa<Sigma>(); sigma && sigma->num_ops() == 2 && sigma->op(1) == env)
        return sigma;

    return nullptr;
}

inline const Def* pack(const Lam* procedure, const Def* environment, const Def* clos_t) {
    auto& w       = procedure->world();
    w.log().d("pack {} with {}", procedure, environment);

    // check that the calling convention holds until here
    auto procedure_pi = procedure->type()->isa<Pi>();
    assert(procedure_pi && procedure_pi->num_doms() == 2 && "procedure domain should have arity 2");
    auto [c, _] = procedure_pi->doms<2>();
    auto [_, e] = c->projs<2>();
    auto env = Check::coerce(e, environment);
    assert(env && "procedure does not accept env as its first argument");

    auto [code_t, env_t] = clos_t->projs<2>();
    w.log().d("casting {}:{} to code_t {}", procedure->type(), procedure->type()->unfold_type(), code_t);
    w.log().d("casting {}:{} to env_t {}", env->type(), env->type()->unfold_type(), env_t);
    return w.tuple({
        w.call<clos2::unsafe_cast>(code_t, procedure),
        w.call<clos2::unsafe_cast>(env_t, env)
    });
}

inline const Def* closure_apply(const Def* clos, const Def* arg) {
    auto& w          = clos->world();
    auto [proc, env] = clos->projs<2>(); // this enforces the calling convention, by construction

    w.log().d("UP {}", clos);
    w.log().d("prc {}:{}", proc, proc->type());
    w.log().d("env {}:{}", env, env->type());
    w.log().d("arg {}:{}", arg, arg->type());

    return w.app(proc, {clos, arg});
}
}

class AbsClosElim : public RWPhase {
public:
    AbsClosElim(World& world, flags_t annex) : RWPhase(world, annex) {}

private:
    Lam* rewrite_procedure(Lam*);

    void rewrite_external (Def* mut) final {
        auto new_mut = rewrite(mut);
        log().d("rewrite_external {}", mut);
        auto fvs = new_mut->free_vars();
        log().d("new_mut has fvs {}", fvs);
        for (auto v : fvs)
            log().d("{} binded by {}", v, v->binder());
        RWPhase::rewrite_external(mut);
    }

    const Def* create_closure(Axm::IsA<anno, App> a) {
        log().d("create closure {}", a);

        auto app = a->arg()->as<App>();
        auto old_proc = app->callee()->as_mut<Lam>();
        auto new_proc = rewrite_procedure(old_proc);
        auto environment = rewrite(app->arg());
        auto old_pi = a->type()->as<Pi>();
        assert(Pi::isa_cn(old_pi) && "the Pi type of a closure should be a Cn");
        auto clos_t = rewrite(a->type());
        return Closure::pack(new_proc, environment, clos_t);
    }

    // abstract closure elim and closure application
    const Def* rewrite_imm_App(const App* app) {
        log().d("rewrite_imm_App {}", app);
        if (auto a = Axm::isa<anno>(app)) return create_closure(a);

        auto new_arg = rewrite(app->arg());
        auto new_callee = rewrite(app->callee());

        // if the callee is not a Pi then it is a closure
        if (Closure::isa_closure_type(new_callee->type()))
            return Closure::closure_apply(new_callee, new_arg); // this enforces that we use the calling convention
        
        log().d("rewrite_imm_App {}  ~>", app);
        log().d("new_callee {}:{}", new_callee, new_callee->type());
        log().d("new_arg {}:{}", new_arg, new_arg->type());

        return new_world().app(new_callee, new_arg);
    }

    /* currently I'm rewriting every Pi but I have to skip the Pi of a lambda */
    const Def* rewrite_imm_Lam(const Lam* d) final {
        log().d("rewrite_imm_Lam {}", d);
        auto old_pi = d->type();
        auto new_type   = (old_pi->isa_mut() ? RWPhase::rewrite_mut_Pi(old_pi->as_mut<Pi>()) : RWPhase::rewrite_imm_Pi(old_pi))->as<Pi>();
        auto new_filter = rewrite(d->filter());
        auto new_body   = rewrite(d->body());
        return new_world().lam(new_type, new_filter, new_body);
    }
    const Def* rewrite_mut_Lam(Lam* d) final {
        log().d("rewrite_mut_Lam {}", d);
        if (!Pi::isa_cn(d->type())) return map(d, rewrite_procedure(d));
        auto old_pi = d->type();
        const Pi* new_pi = (old_pi->isa_mut() ? RWPhase::rewrite_mut_Pi(old_pi->as_mut<Pi>()) : RWPhase::rewrite_imm_Pi(old_pi))->as<Pi>();
        return rewrite_stub(d, new_world().mut_lam(new_pi));
    }

    const Def* rewrite_mut_Pi(Pi* pi) final {
        if (Pi::isa_cn(pi)) return Closure::closure_type(rewrite(pi->dom()));
        return RWPhase::rewrite_mut_Pi(pi);
    }

    const Def* rewrite_imm_Pi(const Pi* pi) final {
        if (Pi::isa_cn(pi)) return Closure::closure_type(rewrite(pi->dom()));
        return RWPhase::rewrite_imm_Pi(pi);
    }


private:
    DefMap<Lam*> procedures_{};
};


} // namespace mim::plug::clos2
