#pragma once

// TODO refactor comments

#include "mim/def.h"
#include "mim/world.h"

#include "mim/util/util.h"

#include "mim/plug/clos2/ex.h"

namespace mim::plug::clos2 {

/// @name Free Variable Analysis
/// @{
/// This class provides a free variable analysis very similar to @see @ref mim::Def::free_vars.
/// The main difference is that this one extracts variables which wrap multiple arguments.
///
/// Free variables are cached.
///
/// TODO explain how this analysis works
///
/// TODO add an example
class FVAnalysis {
public:
    DefSet free_vars(const Def* def) {
        auto fex = free_extr(def);
        return fex.getSet();
    }

private:
    /// calculate the set of free variables
    EXAnalysis free_extr(const Def* def) {
        if (auto mut = def->isa_mut()) return free_extr(mut);

        /* NOTE:
         * the expression is immutable. Thus it doesn't introduce new vars.
         * this means that the free vars are the union of all vars reachable.
         * thus the union of the localvars of all reachable mutables.
         */
        auto fex = local_vars(def);
        for (auto mut : def->local_muts())
            fex.include(free_extr(mut));

        return fex;
    }

    EXAnalysis free_extr(Def* def) {
        auto& st = get_state(def);
        auto& w  = def->world();

        if (st.mark_ == 0) { /* use fixed-point iteration to recompute free vars */
            bool cyclic = false;
            /* first we need to do the initial run */
            w.next_run();
            free_extr<true>(cyclic, w.next_run(), def);

            /* now we can iterate to solve for the fixed-point */
            for (bool todo = cyclic; todo;) {
                todo = false;
                free_extr<false>(todo, w.next_run(), def);
            }
        }

        /* the free var set is stored in the state */
        return st.vars_;
    }

    template<bool init>
    EXAnalysis free_extr(bool& todo, uint32_t run, Def* expr) {
        /* NOTE: for an explanation on the algorithm behind this take a look at Def::free_vars */

        auto& st = get_state(expr);
        if (st.mark_ != 0 && st.mark_ != run - 1) {
            if constexpr (init) todo |= st.mark_ == run;
            return st.vars_;
        }

        st.mark_ = run;

        auto fex0 = st.vars_.getSet(); // create copy to check against later, see if the set changed
        auto fvs  = st.vars_;

        for (auto op : expr->deps()) {
            /* we start by adding all from dependencies reachable vars */
            if constexpr (init) fvs.include(local_vars(op));

            /* then add the free vars of every from op reachable mutable */
            for (auto mut : op->local_muts())
                fvs.include(free_extr<init>(todo, run, mut));
        }

        // FV(lam x.e) = FV(e) \ {x}
        if (auto var = expr->has_var()) fvs.drop(var);

        /* did smt change? */
        if constexpr (!init) todo |= fex0 != fvs.getSet();

        /* update free var cache of expr */
        return st.vars_ = fvs;
    }

private:
    struct FVState {
        u32 mark_        = 0;
        EXAnalysis vars_ = {}; ///< Mutable: local vars; Immutable: free vars.
    };

    GIDNodeMap<const Def*, FVState> state_;

    /// get the internal state of a Def (creates it if needed)
    FVState& get_state(const Def* def) {
        if (state_.contains(def)) return state_.at(def);

        // create new state empty state for def
        auto& st = state_[def]; // default initializes the state

        st.vars_.includeFromDef(def);

        return st;
    }

    /// Var%s reachable by following *immutable* deps().
    EXAnalysis local_vars(const Def* expr) { return expr->is_mutable() ? EXAnalysis{} : get_state(expr).vars_; }
};

} // namespace mim::plug::clos2
