#include "mim/plug/clos2/phase/clos_conv.h"

#include <format>
#include <tuple>

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

/// TODO: this analysis is currently not used. I'm just using it to dump the old_world just before the start of this
/// Phase. this is needed because previously Phases already rewrite the world and thus the names from the dump before
/// world::optimize() are no longer correct
bool ClosConv::analyze() {
    auto& w = old_world();

    w.dump();
    w.dot("middle.dot", {.all_annexes = true});

    return false;
}

const ClosConv::Stub* ClosConv::get_Stub(const Lam* old_lam) {
    if (auto it = closures_.find(old_lam); it != closures_.end()) {
        log().d("reuse stub for {}", old_lam);
        return &it->second;
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
    auto dom   = rewrite(old_lam->type()->dom());
    auto codom = rewrite(old_lam->type()->codom());
    // TODO: I must create a mut_pi if the old_lam->type() is a mut pi
    auto fn_type  = w.pi(dom, codom, old_lam->type()->is_implicit());
    auto env_type = environment->type(); // TODO: I think I want to use uniq at this point. but I didnt get that to work
    auto procedure = w.mut_lam(env_type, fn_type);
    procedure->set(false, w.mut_lam(fn_type))->set(old_lam->dbg_key())->debug_prefix("procedure_");

    // put the stub in the closure list and insert the old_lam into the work list.
    // the body of code will be rewritten in finalize
    worklist_.emplace(old_lam);
    closures_[old_lam] = {.fvs = fvs, .fn_type = fn_type, .env = environment, .procedure = procedure};

    log().d("creation done. Code has type {}", procedure->type());

    return &closures_[old_lam];
}

const Def* ClosConv::rewrite_body(ClosConv::Stub& stub, const Lam* old_lam) {
    auto& w        = new_world();
    auto procedure = stub.procedure;
    auto fn_body   = procedure->body()->as_mut<Lam>();

    log().e("rewriting body for stub closure of {}", old_lam);

    // TODO: maybe there is something different if the old_lam is not mutable. I'll see when I get there
    auto env = procedure->var();
    auto arg = fn_body->var();

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
    auto filter = rewrite(old_lam->filter());
    auto body   = rewrite(old_lam->body());
    log().d("rewrote filter to {}", filter);
    log().d("rewrote body to {} of type {}", body, body->type());
    fn_body->set(filter, body);

    // TODO: externalize procedure
    // currently I cannot do that in every case. in the clos2-example I have to pack the closure of loop into the
    // environment of body. in general I dont want to closure convert this but keep it as a loop. llvm understand free
    // vars in loops. thus I use this workaround for now.
    // NOTE: I still have do decide how I want to do recursion and mutual recusion for closure procedures...
    log().d("procedure is extern : {} ; fvs : {}", procedure->is_external(), procedure->free_vars());
    if (procedure->free_vars().empty()) procedure->externalize();

    pop();

    return procedure;
}

const Def* ClosConv::Stub::pack() const {
    auto& w = procedure->world();

    auto clos = w.tuple({env->type(), env, procedure})->as<Tuple>()->set("closure");
    w.log().i("packed closure  {}", clos);
    return clos;
}

std::tuple<const Def*, const Def*, const Def*> ClosConv::Stub::unpack(const Def* tup) {
    auto [env_type, env, procedure] = tup->projs<3>();
    return {env_type, env, procedure}; // TODO: I actually expect procedure to be a mut Lam, because I'm currently
                                       // rewriting the return continuations I cannot do that.
}

// TODO: write an actual check
const Def* ClosConv::Stub::isa_closure(const Def* def) {
    if (def->isa<Tuple>()) return def;
    if (def->type()->isa_mut<Sigma>()) return def;
    return nullptr;
}

const Def* ClosConv::Stub::clos_type(const Pi* fn_type) {
    auto& w  = fn_type->world();
    auto sig = w.mut_sigma(3);
    w.log().d("calculate closure type of {}", fn_type);

    // keep the env type abstract of type *
    sig->set(0, w.type());
    auto T = sig->var(0);

    // env of type T
    sig->set(1, T);

    // procedure type
    auto procedure_type = w.pi(T, fn_type);
    sig->set(2, procedure_type);

    w.log().i("clos_type of {} is {}", fn_type, sig);

    return sig;
}

const Def* ClosConv::Stub::apply(const Def* clos, const Def* arg) {
    auto& w = clos->world();

    auto [_, env, procedure] = unpack(clos);

    return w.app(w.app(procedure, env), arg);
}

const Def* ClosConv::rewrite_imm_Lam(const Lam* old_lam) { return RWPhase::rewrite_imm_Lam(old_lam); } // TODO: delete

const Def* ClosConv::rewrite_mut_Lam(Lam* old_lam) {
    if (!Lam::isa_cn(old_lam)) return RWPhase::rewrite_mut_Lam(old_lam);

    // create stub and return the closure.
    auto stub = get_Stub(old_lam);
    assert(stub);
    log().i("closure convert mut lam {}", old_lam);
    return map(old_lam, stub->pack());
}

void ClosConv::rewrite_external(Def* old_mut) {
    log().i("rewrite external {}", old_mut);
    auto new_def = rewrite_root(old_mut);
    if (Stub::isa_closure(new_def)) return; // TODO: externalize the code lambda from the closure

    if (old_mut->is_external()) new_def->as_mut()->externalize();
}

// BUG: I think I dont want to rewrite dependent types...
// for example of Idx which is Nat -> *

const Def* ClosConv::rewrite_imm_Pi(const Pi* pi) {
    if (!Pi::isa_cn(pi)) {
        log().d("imm Pi {} is not a continuation", pi);
        return RWPhase::rewrite_imm_Pi(pi);
    }

    auto new_pi    = RWPhase::rewrite_imm_Pi(pi)->as<Pi>();
    auto clos_type = Stub::clos_type(new_pi);
    log().d("rewritten mut pi {} : {}  to  {} : {}", pi, pi->type(), clos_type, clos_type->type());
    return clos_type;
}

const Def* ClosConv::rewrite_mut_Pi(Pi* pi) {
    if (!Pi::isa_cn(pi)) {
        log().d("mut Pi {} is not a continuation", pi);
        return RWPhase::rewrite_mut_Pi(pi);
    }

    auto new_pi    = RWPhase::rewrite_mut_Pi(pi)->as<Pi>();
    auto clos_type = Stub::clos_type(new_pi);
    log().d("rewritten mut pi {} : {}  to  {} : {}", pi, pi->type(), clos_type, clos_type->type());
    return clos_type;
}

// enforce closure calling convention
const Def* ClosConv::rewrite_imm_App(const App* old_app) {
    auto& w         = new_world();
    auto new_callee = rewrite(old_app->callee());
    auto new_arg    = rewrite(old_app->arg());

    auto clos = Stub::isa_closure(new_callee);
    if (!clos) {
        log().d("the callee was not detected as a closure. old_app:{}, new_callee {}:{}, new_arg {}:{}", old_app,
                new_callee, new_callee->type(), new_arg, new_arg->type());
        return w.app(new_callee, new_arg)->set(old_app->dbg_key());
    }

    log().d("detected application of closure {} with arg {}", clos, new_arg);

    return Stub::apply(clos, new_arg);
}

void ClosConv::finalize() {
    log().i("finalize()");
    new_world().dot("before_crash.dot");
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
