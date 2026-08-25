#pragma once

// TODO refactor comments

#include <algorithm>
#include <optional>

#include "mim/def.h"
#include "mim/tuple.h"
#include "mim/world.h"

#include "mim/util/util.h"

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
    /// calculate the set of free variables
    DefSet free_vars(const Def* def) {
        if (auto mut = def->isa_mut()) return free_vars(mut);

        /* NOTE:
         * the expression is immutable. Thus it doesn't introduce new vars.
         * this means that the free vars are the union of all vars reachable.
         * thus the union of the localvars of all reachable mutables.
         */
        auto fvs = local_vars(def);
        for (auto mut : def->local_muts())
            for (auto v : free_vars(mut))
                fvs.emplace(v);

        return fvs;
    }

    DefSet free_vars(Def* def) {
        auto& st = get_state(def);
        auto& w  = def->world();

        if (st.mark_ == 0) { /* use fixed-point iteration to recompute free vars */
            bool cyclic = false;
            /* first we need to do the initial run */
            w.next_run();
            free_vars<true>(cyclic, w.next_run(), def);

            /* now we can iterate to solve for the fixed-point */
            for (bool todo = cyclic; todo;) {
                todo = false;
                free_vars<false>(todo, w.next_run(), def);
            }
        }

        /* the free var set is stored in the state */
        return st.vars_;
    }

    template<bool init>
    DefSet free_vars(bool& todo, uint32_t run, Def* expr) {
        /* NOTE: the following comment was copied from the <>Def::free_vars function */
        // If init == true : todo flag detects cycle.
        // If init == false: todo flag keeps track whether sth changed.
        //
        // Recursively recompute free vars. If
        // * mark_ == 0:        Invalid - need to recompute.
        // * mark_ == run - 1:  Previous iteration - need to recompute.
        // * mark_ == run:      We are running in cycles within the *current* iteration of our fixed-point loop.
        // * otherwise:         Valid!

        /* NOTE: this function was written based on <bool init>Def::free_vars() */
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
                for (auto v : local_vars(op))
                    fvs.emplace(v);

            /* then add the free vars of every from op reachable mutable */
            for (auto mut : op->local_muts()) {
                /* add the free vars of the dependencies */
                for (auto v : free_vars<init>(todo, run, mut))
                    fvs.emplace(v);
            }
        }

        // FV(lam (x_1,...).e) = FV(e) \ {x_1,...}
        if (auto var = expr->has_var())
            for (auto v : var->tprojs())
                fvs.erase(v);

        /* did smt change? */
        if constexpr (!init) todo |= fvs0 != fvs;

        /* update free var cache of expr */
        return st.vars_ = fvs;
    }

    void get_extractions(const Def* def, DefMap<u64>& map) {
        // if def is a Var then every extraction of Var is in def
        if (def->isa<Var>()) map[def] = ~((u64)0);

        // if def is an Extract we have to check if the Index is constant and if so add it. otherwise the entire
        // Extract::tuple()
        else if (auto ext = def->isa<Extract>())
            if (auto idx = Lit::isa<u64>(ext->index()); idx && idx < threshold_)
                map[ext->tuple()] |= 1ull << idx.value();

            // add all extracts of ext->tuple()
            // using get_extractions will recurse and has the following effects dependent on what ext->tuple() is
            // - Var then add (ext->tuple(), 1111..1111) to the map meaning all extractions of it where found
            // - v#j then add (v, j) to the map
            // and so on.
            // The Idea is that we stop on our way down to var if the extraction was constant
            else
                get_extractions(ext->tuple(), map);

        // if both were not the case I'll have to go over the deps
        // TODO: maybe I'll always have to do that?
        else
            for (auto dep : def->deps())
                get_extractions(dep, map);

        // now we want to shrink the map because we might have
        // v#i and (v#i)#...#j in the map in which case we just want v#i
        // TODO: I currently don't know how this could be done
    }

private:
    struct FVState {
        u32 mark_    = 0;
        DefSet vars_ = {}; ///< Mutable: local vars; Immutable: free vars.
    };

    u64 threshold_ = 64; ///< The threshold at which arity we dont split up anymore

    GIDNodeMap<const Def*, FVState> state_;

    /// get the internal state of a Def (creates it if needed)
    FVState& get_state(const Def* def) {
        if (state_.contains(def)) return state_.at(def);

        // create new state empty state for def
        auto& st = state_[def]; // default initializes the state

        // if def is d#i I want to set vars_ as {def}
        // WARN: this is not correct
        if (def->isa<Extract>()) {
            // TODO: check if ext->index() is constant
            st.vars_.emplace(def);
            return st;
        }

        /* TODO: I made the assumption that the ops of def are already set. Is this allowed for this? */
        for (auto def : def->deps())
            for (auto v : local_vars(def))
                st.vars_.emplace(v);

        return st;
    }

    /// Var%s reachable by following *immutable* deps().
    DefSet local_vars(const Def* expr) { return expr->is_mutable() ? DefSet() : get_state(expr).vars_; }
};

} // namespace mim::plug::clos2
