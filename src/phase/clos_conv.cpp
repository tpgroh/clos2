#include "mim/plug/clos2/phase/clos_conv.h"

#include "mim/phase.h"
#include "mim/tuple.h"

// TODO: in the creation of a recursive closure I'm currently messing up.
// I want to overwrite the rewrite_*_Lam methods to directly overwrite the lam 'allocation' with the closure.
// for that to work I have to take a look at code_body's creation. there I dont want to just place down the closure.
// instead I want to do the rewrite_*_Lam method from RWPhase. (for some reason that didn't work before. maybe now
// because I'm smarter...) then rewrite_imm_App just has to enforce the calling convetion of closures instead of also
// creating them.

using namespace mim;
using namespace mim::plug;
using namespace mim::plug::clos2;

static inline const Lam* isa_convertableLam(const Def* def) {
    auto lam = def->isa<Lam>();
    return lam && !lam->is_external() ? lam : nullptr;
}

bool ClosConv::analyze() {
    DefSet done{};

    old_world().dump();
    old_world().dot("middle.dot");

    // find all lambdas that we have to convert
    auto visit = [&](auto&& visit, const Def* def) {
        if (!done.insert(def).second) return;

        if (auto app = def->isa_imm<App>()) {
            if (auto lam = isa_convertableLam(app->callee())) {
                convertable_.insert(lam);
                closureCallsites_.insert(app);
            }

            // TODO: this is a complete hack...
            // what I actually want to do is to check if any of the projs has to be converted.
            // if so I want to convert those and all the other ones have to be converted into a dummy closure.
            // dummy closure meaning [lam, ()] without closing old lam
            else if (auto br = app->callee()->isa<Extract>())
                for (auto b : br->tuple()->projs())
                    if (auto lam = isa_convertableLam(b)) {
                        log().d("found application on an extraction {}", b);
                        convertable_.insert(lam);
                        closureCallsites_.insert(app);
                    }
        }

        for (auto dep : def->deps())
            visit(visit, dep);
    };

    for (auto root : old_world().roots())
        visit(visit, root);

    log().d("the following lambda where found to be closure convertable {}", convertable_);

    return false;
}

const Def* ClosConv::get_closure(const Lam* old_lam) {
    if (auto it = closures_.find(old_lam); it != closures_.end()) {
        log().d("detected use of the already created closure {} of {}", it->second, old_lam);
        return it->second;
    }

    log().d("creating closure for {}", old_lam);

    // get the free vars
    auto fvset = fvana_.free_vars(old_lam); // TODO: we can skip if old_lam->is_closed()
    log().d("free vars of {} are {} vs {}", old_lam, fvset, old_lam->free_vars());
    DefVec fvs{fvset.begin(), fvset.end()};
    DefVec new_fvs{};
    new_fvs.reserve(fvs.size());

    // create environment from free vars
    for (auto v : fvs)
        new_fvs.emplace_back(rewrite(v));
    auto environment = new_world().tuple(new_fvs)->set(old_lam->dbg_key())->debug_prefix("environment_");

    // create code lambda
    push(); // TODO: maybe I want to push after mapping old_lam->type() ?
    auto code_codom = map(old_lam->type(), rewrite(old_lam->type()));
    auto code       = new_world().mut_lam(environment->type(), code_codom);
    code->set(old_lam->dbg_key())->debug_prefix("closed_");
    auto env = code->var();
    env->set(old_lam->dbg_key())->debug_prefix("code_env_");

    // to make recursive closures work I'm creating the closure
    // before completing the creation of the code lambda
    auto closure = new_world().tuple({code, environment});
    closure->set(old_lam->dbg_key())->debug_prefix("closure_of_");
    closures_[old_lam] = closure;

    // map free vars to corresponding extractions of env
    auto env_size = new_fvs.size();
    if (env_size == 1) {
        log().d("mapping {} -> {}", fvs[0], env);
        map(fvs[0], env);
    } else if (env_size > 1)
        for (size_t i = 0; i < env_size; i++) {
            log().d("mapping {} -> {}#{}", fvs[i], env, i);
            map(fvs[i], env->proj(i));
        }

    // now create code body taking advantage of the lookup machinery
    log().d("creating body of {}", code);
    const Def* code_body;
    if (!old_lam->is_mutable())
        code_body = RWPhase::rewrite_imm_Lam(old_lam);
    else { // essentially rewrite_mut_Lam but without the maps because we do not want to map old_lam to code_body!
        code_body    = RWPhase::rewrite_mut_Lam(old_lam->as_mut<Lam>());
        auto old_mut = old_lam->as_mut<Lam>();
        Def* new_mut = new_world().mut_lam(code_codom->as<Pi>());

        assert(old_mut->is_set());
        auto _ = enter(old_mut);
        for (size_t i = 0, e = old_mut->num_ops(); i != e; ++i)
            new_mut->set(i, rewrite(old_mut->op(i)));

        code_body = new_mut;
    }

    pop();

    code->set(false, code_body);
    // code->externalize(); // TODO: uncomment as soon as possible

    log().d("packed closure {} of lam {}", closure, old_lam);

    return closure;
}

// closure 'allocation'
const Def* ClosConv::rewrite_imm_Lam(const Lam* old_lam) {
    if (convertable_.contains(old_lam)) return get_closure(old_lam);
    return RWPhase::rewrite_imm_Lam(old_lam);
}

const Def* ClosConv::rewrite_mut_Lam(Lam* old_lam) {
    if (convertable_.contains(old_lam)) {
        auto _ = enter(old_lam); // TODO: ??
        return get_closure(old_lam);
    }
    return RWPhase::rewrite_mut_Lam(old_lam);
}

// enforce closure calling convention
const Def* ClosConv::rewrite_imm_App(const App* old_app) {
    if (!closureCallsites_.contains(old_app)) {
        auto new_app = RWPhase::rewrite_imm_App(old_app);
        return new_app->set(old_app->dbg_key());
    }

    auto old_callee = old_app->callee();
    auto old_arg    = old_app->arg();
    log().d("I expect the following rewrite of {} to return a closure", old_callee);

    // create closure of lam
    const Def* clos = rewrite(old_callee);
    assert(clos);
    log().d("and got {}", clos);

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
    return new_app->set(old_app->dbg_key());
}
