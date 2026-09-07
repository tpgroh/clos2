#include "mim/plug/clos2/phase/clos_conv.h"

#include <format>
#include <optional>

#include "mim/lattice.h"
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

bool ClosConv::analyze() {
    DefSet done{};

    // TODO: I'm doing this because to be able to debug with the names of nodes after the cleanup_ phase
    old_world().dump();
    old_world().dot("middle.dot", {.follow_types = true});

    // find all lambdas that we have to convert
    auto visit = [&](auto&& visit, const Def* def) {
        if (!done.insert(def).second) return;

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
        new_fvs.emplace_back(rewrite(v)->set(v->dbg_key()));

    // create the environment
    // NOTE: we create the environment as a singleton to enforce the requirement:
    // the code procedure gets exactly the environment which was created for it
    auto& w          = new_world();
    auto environment = w.tuple(new_fvs)->set(old_lam->dbg_key())->debug_prefix("environment_");

    log().d("created environment {}. Now creating code lambda", environment);

    // create the code lam
    // TODO: for dependant types I'll have to make the codom to depend on the argument
    auto dom      = rewrite(old_lam->type()->dom());
    auto codom    = rewrite(old_lam->type()->codom());
    auto env_type = environment->type(); // TODO: I think I want to use uniq at this point. but I didnt get that to work
    auto code     = w.mut_lam({env_type, dom}, codom);
    code->set(old_lam->dbg_key())->debug_prefix("closed_");

    // put the stub in the closure list and insert the old_lam into the work list.
    // the body of code will be rewritten in finalize
    worklist_.emplace(old_lam);
    closures_[old_lam] = {.fvs = fvs, .env = environment, .code = code};

    log().d("creation done. Code has type {}", code->type());

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

    // TODO: there must be a better way to type closures.
    // maybe annotate the tuple with some special tag?
    // @see also TODO in isa_closure
    auto clos = w.tuple({code, env})->as<Tuple>()->set("closure");
    w.log().d("packed closure  {}", clos);
    return clos;
}

std::optional<std::pair<const Lam*, const Def*>> ClosConv::Stub::isa_closure(const Def* def) {
    // TODO: there must be a better way to detect closure types.
    // maybe annotate the tuple with some special tag?
    auto tup = def->isa_imm<Tuple>();
    if (!tup) return {};
    auto pair = std::pair{tup->proj(2, 0)->as<Lam>(), tup->proj(2, 1)};
    tup->world().log().d("unpacked closure {{.code={}, .env={}}}", pair.first, pair.second);
    return pair;
}

const Def* ClosConv::rewrite_imm_Lam(const Lam* old_lam) {
    if (old_lam->is_external()) return RWPhase::rewrite_imm_Lam(old_lam);
    // if (!convertable_.contains(old_lam)) return RWPhase::rewrite_imm_Lam(old_lam);

    // create stub and return the closure.
    log().d("closure convert imm lam {}", old_lam);
    auto stub = get_Stub(old_lam);
    if (old_lam->is_external()) {
        assert(stub.fvs.size() == 0);
        return stub.code;
    }
    return map(old_lam, stub.pack());
}

const Def* ClosConv::rewrite_mut_Lam(Lam* old_lam) {
    if (old_lam->is_external()) return RWPhase::rewrite_mut_Lam(old_lam);
    // if (!convertable_.contains(old_lam)) return RWPhase::rewrite_mut_Lam(old_lam);

    // create stub and return the closure.
    log().d("closure convert mut lam {}", old_lam);
    auto stub = get_Stub(old_lam);
    if (old_lam->is_external()) {
        assert(stub.fvs.size() == 0);
        return stub.code;
    }
    return map(old_lam, stub.pack());
}

void ClosConv::rewrite_external(Def* old_mut) {
    auto new_def = rewrite_root(old_mut);
    if (auto clos = Stub::isa_closure(new_def)) return;

    auto new_mut = rewrite_root(old_mut)->as_mut();
    if (old_mut->is_external()) new_mut->externalize();
}

// enforce closure calling convention
const Def* ClosConv::rewrite_imm_App(const App* old_app) {
    auto& w         = new_world();
    auto new_callee = rewrite(old_app->callee());
    auto new_arg    = rewrite(old_app->arg());

    auto clos = Stub::isa_closure(new_callee);
    if (!clos) {
        log().d("the callee was not detected as a closure. old_app:{}, new_callee:{}, new_arg:{}", old_app, new_callee,
                new_arg);
        return w.app(new_callee, new_arg)->set(old_app->dbg_key());
    }

    auto [code, env] = *clos;

    log().d("detected application of closure with code={} environment={} and argument {}", code, env, new_arg);

    return w.app(code, {env, new_arg});
}

void ClosConv::finalize() {
    while (!worklist_.empty()) {
        auto old_lam = worklist_.front();
        worklist_.pop();

        auto& stub = closures_.at(old_lam);

        // rewrite old_lam to code_body
        push();
        rewrite_body(stub, old_lam);
        pop();
    }
}
