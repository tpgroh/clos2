#include "mim/plug/clos2/phase/clos_conv.h"

#include <format>
#include <optional>

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

    // TODO: I'm doing this because to be able to debug with the names of nodes after the cleanup_ phase
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

const ClosConv::Stub& ClosConv::get_Stub(const Lam* old_lam) {
    if (auto it = closures_.find(old_lam); it != closures_.end()) {
        log().d("reuse stub for {}", old_lam);
        return it->second;
    }

    log().d("creating stub for {}", old_lam);

    // get the free vars
    auto fvset = fvana_.free_vars(old_lam); // TODO: we can skip if old_lam->is_closed()
    log().d("free vars of {} are {} vs {}", old_lam, fvset, old_lam->free_vars());
    DefVec fvs{fvset.begin(), fvset.end()};
    DefVec new_fvs{};
    new_fvs.reserve(fvs.size());
    for (auto v : fvs)
        new_fvs.emplace_back(rewrite(v));

    // create the environment
    // NOTE: we create the environment as a singleton to enforce the requirement:
    // the code procedure gets exactly the environment which was created for it
    auto& w          = new_world();
    auto environment = w.uniq(w.tuple(new_fvs))->set(old_lam->dbg_key())->debug_prefix("environment_");

    // create the code lam
    // TODO: for dependant types I'll have to make the codom to depend on the argument
    auto dom   = rewrite(old_lam->type()->dom());
    auto codom = rewrite(old_lam->type()->codom());
    auto code  = w.mut_lam(w.tuple(Defs{environment->type(), dom}), codom);

    // put the stub in the closure list and insert the old_lam into the work list.
    // the body of code will be rewritten in finalize
    worklist_.emplace(old_lam);
    closures_[old_lam] = {.fvs = fvs, .env = environment, .code = code};

    return closures_[old_lam];
}

const Def* ClosConv::rewrite_body(ClosConv::Stub& stub, const Lam* old_lam) {
    auto& w   = new_world();
    auto code = stub.code;

    log().d("rewriting body for stub closure of {}", old_lam);

    // TODO: maybe there is something different if the old_lam is not mutable. I'll see when I get there
    auto [env, arg] = code->vars<2>();

    push();

    // mapping free vars to extractions of env
    if (stub.fvs.size() == 1) {
        log().d("mapping single free var directly to env");
        map(stub.fvs[0], env);
    } else
        for (size_t i = 0; i < stub.fvs.size(); i++) {
            auto v = stub.fvs[i];
            auto e = w.extract(env, i)->set(v->dbg_key())->debug_prefix(std::format("env_ext_{}_", i));
            log().d("mapping {} to env#{}", v, i);
            map(v, e);
        }
    if (auto v = old_lam->has_var()) {
        log().d("mapping argument of old_lam to arg");
        map(v, arg);
    }

    // rewrite code
    // TODO: to allow for recursion I have to make sure that I already map old_lam to (code env)
    code->set(Lam::Filter{rewrite(old_lam->filter())}, rewrite(old_lam->body()));

    pop();

    return code;
}

const Def* ClosConv::Stub::pack() {
    auto& w = code->world();

    auto s = w.sigma({code, env})->set("closure");
    return s;
}

std::optional<std::pair<const Lam*, const Def*>> ClosConv::Stub::isa_closure(const Def* def) {
    auto sig = def->isa_imm<Sigma>();
    if (!sig) return {};
    return std::pair{sig->proj(2, 0)->as<Lam>(), sig->proj(2, 1)};
}

// enforce closure calling convention
const Def* ClosConv::rewrite_imm_App(const App* old_app) {
    auto new_callee = rewrite(old_app->callee());
    auto new_arg    = rewrite(old_app->arg());

    auto clos = Stub::isa_closure(new_callee);
    if (!clos) return new_world().app(new_callee, new_arg)->set(old_app->dbg_key());

    auto [code, env] = *clos;

    return new_world().app(code, {env, new_arg});
}
