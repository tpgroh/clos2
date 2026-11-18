#pragma once

#include "mim/def.h"
#include "mim/phase.h"
#include "mim/plug/clos2/autogen.h"
#include <set>

namespace mim::plug::clos2 {

class AbsClosSjLj : public RWPhase {
public:
    AbsClosSjLj(World& world, flags_t annex)
        : RWPhase(world, annex) {}
private:
    void analyze(const Def* def, DefSet& done) {
        if (auto i = done.insert(def); !i.second) return;

        // if we find a captured return continuation annotation we store the binder
        if (auto ano = Axm::isa(anno::captured_ret, def)) {
            found_captured_ret_ = true;
            auto v = ano->arg();

            // get the var from the return continuation
            const Var* var = nullptr;
            if (auto ext = v->isa<Extract>()) var = ext->tuple()->isa<Var>();
            else                              var = v->isa<Var>();

            if (var)
                if (auto lam = Lam::isa_mut_returning(var->binder()); lam && lam->ret_var() == v)
                    allocsites_.emplace(var->binder());
        }

        // find the indices in environment parameters of procedures where captured return continuations are.
        // this cannot get annotated inside the type of the procedure. thus we have to find it out here
        else if (auto ano = Axm::isa(anno::absclos, def))
            if (auto clos = ano->arg()->isa<App>()) { // if not self recursive call
                auto old_proc = clos->callee()->as_mut<Lam>();
                auto old_env =  clos->arg();

                if (old_env->num_projs() <= 1) {
                    // for single element environment 0 means the entire environment, not the first projection
                    if (auto ano = Axm::isa(anno::captured_ret, old_env))
                        retslots_[old_proc].emplace(0);
                } else {
                    auto n = old_env->num_projs();
                    for (size_t i = 0; i < n; i++)
                        if (auto ano = Axm::isa(anno::captured_ret, old_env->proj(n, i)))
                            retslots_[old_proc].emplace(i);
                }
            }

        // recursive graph traversal
        for (auto d : def->deps()) analyze(d, done);
    }

    void start() final {
        DefSet done{};
        for (auto root : old_world().externals().muts()) analyze(root, done);
        if (!found_captured_ret_) return;
        log().d("found allocsites {}", allocsites_);
        RWPhase::start();
    }

    const Def* rewrite_body2setjmp(Lam*);
    const Def* rewrite_hoist(Lam*);
    const Def* rewrite_hoist_capretcon(size_t i, const Def*, size_t&, fe::Vector<nat_t>&);

    const Def* rewrite_mut_Lam(Lam* mut) {
        if (allocsites_.contains(mut)) return rewrite_body2setjmp(mut);
        return RWPhase::rewrite_mut_Lam(mut);
    }

    const Def* rewrite_imm_App(const App* app) {
        auto& w = new_world();

        if (auto ano = Axm::isa(anno::captured_ret, app)) {
            auto cr = ano->arg();
            auto it = retcons_.find(cr);
            if (it == retcons_.end())
                cr->blame("captured return continuations should already be rewritten").bail();

            return it->second; // this annotation was only for this phase
        }

        if (auto ano = Axm::isa(anno::absclos, app)) {
            auto clos = ano->arg()->isa<App>();
            if (!clos) return RWPhase::rewrite_imm_App(app); // if procedure is self recursive call
            auto old_proc = clos->callee()->as_mut<Lam>();
            auto old_env =  clos->arg();

            auto env  = rewrite(old_env);
            auto proc = rewrite_hoist(old_proc);

            return w.call(anno::absclos, w.app(proc, env));
        }

        return RWPhase::rewrite_imm_App(app);
    }

private:
    bool found_captured_ret_ = false;
    DefSet allocsites_{};
    Def2Def retcons_{};
    GIDNodeMap<const Def*, std::set<nat_t>> retslots_{};
};

}
