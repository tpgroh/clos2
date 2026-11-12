#pragma once

#include "mim/def.h"
#include "mim/phase.h"
#include "mim/plug/clos2/autogen.h"

namespace mim::plug::clos2 {

/// This phase should do the following
///
/// - rewrites the body of lambdas in which we create closures by
///   setting the new body to one that does the following:
///   - allocate the jmp_buf and the return buffer
///     (here we have to make sure that we exclude memory state things from the type before calling RetCont
///     and that we use the new memory thing from setjmp in the call to return)
///   - call setjmp and switch on the returned int (tag)
///     - on 0 we have the rewrite of the original body
///     - otherwise we call the return continuation with the new memory thing and the loaded value of the
///       return buffer
/// - rewrite the packed environment to have the jmp buffer and the return buffer instead of the
///   return continuation
/// - rewrite the signature of closures / to have RetCont of the return type (removed mem thing) instead of
///   the return continuation type.
/// - rewrite the procedure of the closure to call store + longjmp instead of the return continuation
///
/// trickery parts I still need to dial down later:
/// - inside of the procedure I require a mem thing to be able to call store.
///   I dont think that I always have that!
/// - inside of the body where I call setjmp I must have a mem thing,
///   this I might be able to get using mem.fresh, I have to check
class AbsClosSjLj : public RWPhase {
public:
    AbsClosSjLj(World& world, flags_t annex)
        : RWPhase(world, annex) {}
private:
    void analyze(const Def* def, DefSet& done) {
        if (auto i = done.insert(def); !i.second) return;

        // if we find a captured return continuation annotation we store the binder
        if (auto ano = Axm::isa(anno::captured_ret, def)) {
            auto v = ano->arg();

            // get the var from the return continuation
            const Var* var = nullptr;
            if (auto ext = v->isa<Extract>()) var = ext->tuple()->isa<Var>();
            else                              var = v->isa<Var>();

            if (var)
                if (auto lam = var->binder()->as<Lam>(); lam && lam->ret_var() == v)
                    allocsites_.emplace(var->binder());
        }

        // recursive graph traversal
        for (auto d : def->deps()) analyze(d, done);
    }
    bool analyze() final {
        DefSet done{};

        for (auto root : old_world().externals().muts())
            analyze(root, done);

        log().d("found allocsites {}", allocsites_);
        
        return false;
    }

    const Def* rewrite_body2setjmp(Lam*);
    const Def* rewrite_hoist(Lam*, fe::Vector<nat_t>&);
    const Def* rewrite_hoist_capretcon(size_t i, const Def*, size_t&, fe::Vector<nat_t>&);
    const Def* rewrite_environment(const Def*, fe::Vector<nat_t>&);

    const Def* rewrite_mut_Lam(Lam* mut) {
        if (allocsites_.contains(mut)) return rewrite_body2setjmp(mut);
        return RWPhase::rewrite_mut_Lam(mut);
    }

    const Def* rewrite_imm_App(const App* app) {
        auto& w = new_world();

        if (auto ano = Axm::isa(anno::captured_ret, app)) {
            auto cr = ano->arg();
            auto new_retcon = retcons_[cr];
            assert(new_retcon && "captured return continuations should already be rewritten");
            return w.call(anno::captured_ret, new_retcon);
        }

        if (auto ano = Axm::isa(anno::absclos, app)) {
            auto clos = ano->arg()->isa<App>();
            assert(clos && "abclos could also be applied to something else than App");
            auto old_proc = clos->callee()->as_mut<Lam>();
            auto old_env =  clos->arg();

            // rewrite the procedure and the environment.
            // then just reconstruct the anotation of the closure from scratch
            // this way I dont have to rewrite the implicit type argument to the annotation

            fe::Vector<nat_t>idx;
            auto env  = rewrite_environment(old_env, idx);
            auto proc = rewrite_hoist(old_proc, idx);

            return w.call(anno::absclos, w.app(proc, env));
        }

        return RWPhase::rewrite_imm_App(app);
    }

private:
    DefSet allocsites_{};
    Def2Def retcons_{};
};

}
