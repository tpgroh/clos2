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
        if (auto mut = def->isa_mut()) return free_vars(mut);

        // run pre pass
        EXAnalysis exs{def};
        return free_vars(def, exs);
    }

    /// calculate the set of free variables
    DefSet free_vars(const Def* def, EXAnalysis& exs) {
        if (auto mut = def->isa_mut()) return free_vars(mut);

        /* NOTE:
         * the expression is immutable. Thus it doesn't introduce new vars.
         * this means that the free vars are the union of all vars reachable.
         * thus the union of the localvars of all reachable mutables.
         */
        auto fvs = local_vars(def);
        for (auto mut : def->local_muts())
            for (auto d : free_vars(mut, exs)) {
                auto cov = exs.getCovering(d);
                assert(cov);
                fvs.insert(*cov);
            }

        return fvs;
    }

    DefSet free_vars(Def* def) {
        auto& st = get_state(def);

        if (st.mark_ == 0) {
            EXAnalysis exs{def};
            return free_vars(def, exs);
        }

        return st.vars_;
    }

    DefSet free_vars(Def* def, EXAnalysis& exs) {
        auto& st = get_state(def);
        auto& w  = def->world();

        if (st.mark_ == 0) { /* use fixed-point iteration to recompute free vars */
            bool cyclic = false;
            /* first we need to do the initial run */
            w.next_run();
            free_vars<true>(cyclic, w.next_run(), def, exs);

            // TODO: because I'm now using the local_muts() from Def I don't think that I need this fixedpoint solving
            // algo anymore.

            // now we can iterate to solve for the fixed-point
            for (bool todo = cyclic; todo;) {
                todo = false;
                free_vars<false>(todo, w.next_run(), def, exs);
            }
        }

        // the free var set is stored in the state
        return st.vars_;
    }

    template<bool init>
    DefSet free_vars(bool& todo, uint32_t run, Def* expr, EXAnalysis& exs) {
        /* NOTE: for an explanation on the algorithm behind this take a look at Def::free_vars */

        auto& st = get_state(expr);
        if (st.mark_ != 0 && st.mark_ != run - 1) {
            if constexpr (init) todo |= st.mark_ == run;
            return st.vars_;
        }

        st.mark_ = run;

        auto fvs0 = st.vars_; // create copy to check against later, see if the set changed
        auto fvs  = fvs0;

        for (auto op : expr->deps()) {
            /* we start by adding all from dependencies reachable vars */
            if constexpr (init)
                for (auto d : local_vars(op)) {
                    auto c = exs.getCovering(d);
                    assert(c.has_value());
                    fvs.insert(*c);
                }

            /* then add the free vars of every from op reachable mutable */
            for (auto mut : op->local_muts()) {
                exs.include(mut);
                for (auto v : free_vars<init>(todo, run, mut, exs)) {
                    auto c = exs.getCovering(v);
                    assert(c);
                    fvs.insert(*c);
                }
            }
        }

        // by including var to exs the minimization in the next step will reduce all extractions of var to just var.
        // this way we can just drop var without another search for extractions of it
        if (auto var = expr->has_var()) exs.include(var);

        // minimize fvs (there might be entries which are covered by another extraction in exs)
        fvs = exs.getCovering(fvs);

        // FV(lam x.e) = FV(e) \ {x}
        if (auto var = expr->has_var()) fvs.erase(var);

        /* did smt change? */
        if constexpr (!init) todo |= fvs0 != fvs;

        /* update free var cache of expr */
        return st.vars_ = fvs;
    }

private:
    struct FVState {
        u32 mark_    = 0;
        DefSet vars_ = {}; ///< Mutable: local vars; Immutable: free vars.
    };

    GIDNodeMap<const Def*, FVState> state_;

    /// get the internal state of a Def (creates it if needed)
    FVState& get_state(const Def* def) {
        if (state_.contains(def)) return state_.at(def);

        // create new state empty state for def
        auto& st = state_[def]; // default initializes the state

        // TODO: init free vars

        if (def->isa<Var>())
            st.vars_.insert(def);
        else if (def->isa<Extract>())
            st.vars_.insert(def);
        else
            for (auto dep : def->deps())
                for (auto v : local_vars(dep))
                    st.vars_.insert(v);

        return st;
    }

    /// Var%s reachable by following *immutable* deps().
    DefSet local_vars(const Def* expr) { return expr->is_mutable() ? DefSet{} : get_state(expr).vars_; }
};

} // namespace mim::plug::clos2
