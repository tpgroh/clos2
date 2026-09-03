#include "mim/plug/clos2/phase/clos_conv.h"

#include "mim/phase.h"

// TODO: in the creation of a recursive closure I'm currently messing up.
// I want to overwrite the rewrite_*_Lam methods to directly overwrite the lam 'allocation' with the closure.
// for that to work I have to take a look at code_body's creation. there I dont want to just place down the closure.
// instead I want to do the rewrite_*_Lam method from RWPhase. (for some reason that didn't work before. maybe now
// because I'm smarter...) then rewrite_imm_App just has to enforce the calling convetion of closures instead of also
// creating them.

using namespace mim;
using namespace mim::plug;
using namespace mim::plug::clos2;

bool ClosConv::analyze() {
    DefSet done{};

    // find all lambdas that we have to convert
    auto visit = [&](auto&& visit, const Def* def) {
        if (!done.insert(def).second) return;

        if (auto app = def->isa_imm<App>())
            if (auto lam = app->callee()->isa<Lam>(); lam && !lam->is_external()) convertable_.insert(lam);

        for (auto dep : def->deps())
            visit(visit, dep);
    };

    for (auto root : old_world().roots())
        visit(visit, root);

    log().d("the following lambda where found to be closure convertable {}", convertable_);

    return false;
}

const Def* ClosConv::get_closure(const Lam* old_lam) {
    if (auto it = closures_.find(old_lam); it != closures_.end()) return it->second;

    old_world().dot("middle.dot");

    // get the free vars
    auto fvset = fvana_.free_vars(old_lam); // TODO: we can skip if old_lam->is_closed()
    log().d("free vars of {} are {} vs {}", old_lam, fvset, old_lam->free_vars());
    DefVec fvs{fvset.begin(), fvset.end()};
    DefVec new_fvs{};
    new_fvs.reserve(fvs.size());

    // create env from free vars
    for (auto v : fvs)
        new_fvs.emplace_back(rewrite(v));
    auto environment = new_world().tuple(new_fvs)->set(old_lam->dbg_key())->debug_prefix("environment_");

    // create code lambda
    auto code_codom = map(old_lam->type(), rewrite(old_lam->type()));
    auto code       = new_world().mut_lam(environment->type(), code_codom);
    code->set(old_lam->dbg_key())->debug_prefix("closed_");
    push(); // TODO: maybe I want to push before mapping old_lam->type() ?
    auto env = code->var();
    env->set(old_lam->dbg_key())->debug_prefix("code_env_");

    // to make recursive closures work I'm creating the closure
    // before completing the creation of the code lambda
    auto closure = new_world().tuple({code, environment});
    closure->set(old_lam->dbg_key())->debug_prefix("closure_of_");
    closures_[old_lam] = closure;

    // map free vars to corresponding extractions of env
    auto env_size = new_fvs.size();
    if (env_size == 1)
        map(fvs[0], env);
    else if (env_size > 1)
        for (size_t i = 0; i < env_size; i++)
            map(fvs[i], env->proj(env_size, i));

    // now create code body taking advantage of the lookup machinery
    auto code_body = rewrite(old_lam);
    pop();

    code->set(false, code_body);
    // code->externalize(); // TODO: uncomment as soon as possible

    log().d("packed closure {} of lam {} with free vars {}", closure, old_lam, fvset);

    return closure;
}

const Def* ClosConv::rewrite_imm_App(const App* old_app) {
    auto old_callee = old_app->callee();
    auto old_arg    = old_app->arg();
    auto lam        = old_callee->isa<Lam>();
    if (!lam || lam->is_external()) {
        auto new_app = RWPhase::rewrite_imm_App(old_app);
        return map(old_app, new_app->set(old_app->dbg_key()));
    }

    // create closure of lam
    assert(convertable_.contains(lam));
    const Def* clos = get_closure(lam);

    // create argument
    auto new_arg = rewrite(old_arg)->set(old_arg->dbg_key());

    // use the calling convention for closures
    auto [code, env] = clos->projs<2>();
    log().d("unpacked closure {} to code {} and environment {}", clos, code, env);
    auto new_callee = new_world().app(code, env);
    new_callee->set(old_callee->dbg_key());

    log().d("now reapply argument {} to {}", new_arg, new_callee);

    // reapply the argument
    auto new_app = new_world().app(new_callee, new_arg);
    new_app->set(old_app->dbg_key());

    return map(old_app, new_app);
}
