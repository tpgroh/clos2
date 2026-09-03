#include "mim/plug/clos2/phase/clos_conv.h"

#include "mim/phase.h"

using namespace mim;
using namespace mim::plug;
using namespace mim::plug::clos2;

const Def* ClosConv::create_closure(Lam* old_lam) {
    auto new_lam = rewrite(old_lam)->set(old_lam->dbg_key());
    map(old_lam, new_lam); // we dont want to create a closure only once

    auto env  = new_world().tuple();
    auto code = new_world().mut_lam(env->type(), new_lam->type());
    code->var()->set("env");
    code->set(false, new_lam);
    code->set("code");

    auto closure = new_world().tuple({code, env});
    closure->set("closure");

    log().d("packed closure {} of lam {}", closure, old_lam);

    return closure;
}

const Def* ClosConv::rewrite_imm_App(const App* old_app) {
    auto old_callee = old_app->callee();
    auto old_arg    = old_app->arg();
    auto lam        = old_callee->isa_mut<Lam>();
    if (!lam) {
        auto new_app = RWPhase::rewrite_imm_App(old_app);
        return new_app->set(old_app->dbg_key());
    }

    // create closure of lam
    const Def* clos = create_closure(lam);

    // create argument
    auto new_arg = rewrite(old_arg)->set(old_arg->dbg_key());

    // use the calling convention for closures
    auto [code, env] = clos->projs<2>();
    log().d("unpacked closure {}", clos);
    log().d("code : {} , env : {}", code, env);
    auto new_callee = new_world().app(code, env);
    new_callee->set(old_callee->dbg_key());

    log().d("now reapply arg {} to {}", new_arg, new_callee);

    // reapply the argument
    auto new_app = new_world().app(new_callee, new_arg);
    new_app->set(old_app->dbg_key());

    return new_app;
}
