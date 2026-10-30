#pragma once

#include <queue>

#include "mim/def.h"
#include "mim/lam.h"
#include "mim/phase.h"

#include "mim/plug/clos2/autogen.h"
#include "mim/plug/clos2/fv.h"

namespace mim::plug::clos2 {

class HoistUp : public RWPhase {
public:
    HoistUp(World& world, flags_t annex)
        : RWPhase(world, annex) {}

private:
    // hoist up a lam and adds the lam to the worklist_ for finalize to rewrite the body
    const Def* hoistUp(const Lam* lam);

    // rewrite the body of hoisted up lambdas (from the worklist_)
    // this is being done to ensure that the rewrite of the body
    // is happening inside a scope where everything that depends on
    // the free_vars is already droped
    void finalize() final;

    // TODO: add comments, adjust placement in the code
    enum Pos : u8 { None = 0, Known = 1, Ret = 2, Fst = 4 };

    void analyze_visit(const Def* def, Pos p) {
        if (auto f = Lam::eta_reduce(def)) return analyze_visit(f, p); // we treat eta wrap as transparent
        if (auto lam = def->isa<Lam>()) pos_[lam] = Pos(pos_[lam] | p);
        analyze(def);
    }

    void analyze(const Def* def) {
        // TODO: walk the entire program and store some information
        //   - which lambdas are return continuations.
        //   - downarg first class usage of lambdas (I think this can also be detected in rewrite_imm_App)
        // also check that all assumptions that I made are fulfilled
        //   - lambdas are comletely known or completely unknown (callsites)
        //   - no polymorphism

        if (auto [_, ins] = analyzed_.emplace(def); !ins) return;

        if (auto app = def->isa<App>()) {
            analyze_visit(app->type(), Fst);
            analyze_visit(app->callee(), Known);
            auto n = app->num_args();
            auto returning = Pi::isa_returning(app->callee_type());
            for (size_t i = 0; i < n; i++)
                analyze_visit(app->arg(n, i), returning && i == n-1 ? Ret : Fst);
        } else
            for (auto d : def->deps()) analyze_visit(d, Fst);
    }

    bool analyze() {
        for (auto r : old_world().externals().muts())
            analyze(r);

        // lets take a look at the result
        for (auto [lam, pos] : pos_) {
            log().d("lam {} has pos {}", lam, +pos);
        }
        return false;
    }

    // annotate a 'abstract' closure for later phases
    const Def* annotate(const Def* def, anno a) {
        auto& w = new_world();
        return w.call(a, def);
    }

    bool should_hoist(const Lam* lam) {
        if (lam->is_external()) return false; // we dont touch externals
        if (!pos_.contains(lam)) lam->blame("this lam was not analyzed").bail();

        auto p = pos_[lam];

        if ((p & Ret) && (p & Fst)) lam->blame("eta_conv should have made sure that every lam is eather Fst OR Ret, not both").bail();

        if (p & Fst) return true; // we have to hoist up lambdas with first class use
        return false;
    }

    const Def* rewrite_mut_Lam(Lam* lam) final {
        // rewrite the type of lam and its free vars.
        // note that the body will be rewritten in finalize to work inside a scope where everything that depends on the free vars is already gone
        // the map then creates a mapping from lam to the application of hoisted_lam with environment inside of the scope where the free vars of lam
        // (those that are also rewritten into environment) are owned
        // this way the mapping will be droped as soon as we leave the scope of those free_vars
        if (should_hoist(lam)) return map(lam, hoistUp(lam));


        // we dont want anything that depends on lam->var() to be inside the root scope
        // if we want to hoist up something inside of lam which is using `Idx n` where `n`
        // is the Var of `lam` then I want to rewrite `n` there to something else.
        // thus I must drop everything that depends on `n` before rewriting the body of that lam
        // (the one we want to hoistup inside of the body of `lam`)
        // which is done after returning from this function thanks to the finalize machinery.
        push();
        bind_old(lam->has_var());
        auto new_mut = RWPhase::rewrite_mut_Lam(lam);
        pop();
        return new_mut;
    }

    // TODO FIXME this should also be modified, I dont know how (yet)
    const Def* rewrite_imm_Lam(const Lam* lam) final {
        lam->blame("this should not be reachable").bail();
        return RWPhase::rewrite_imm_Lam(lam);
    }

private:
    struct Stub {
        const Lam* lam;
        const DefVec fvs; // I could loose this if I use a deterministic sorting of free vars. (currently it should be)
    };
    std::queue<Stub> worklist_ = {};
    DefMap<Lam*> outerlams_    = {};
    FVAnalysis fvana_          = {};
    DefMap<Pos> pos_           = {};
    DefSet analyzed_           = {};
};

} // namespace mim::plug::clos2
