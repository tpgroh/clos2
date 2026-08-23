#pragma once

// TODO refactor comments

#include <memory>

#include <mim/world.h>

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
        for (auto mut : local_muts(def))
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

        auto fvs0  = st.vars_; // create copy to check against later, see if the set changed
        auto fvs   = fvs0;
        auto& w    = expr->world();
        auto& muts = w.muts();

        for (auto op : expr->deps()) {
            /* we start by adding all from dependencies reachable vars */
            if constexpr (init)
                for (auto v : local_vars(op))
                    fvs.emplace(v);

            /* then add the free vars of every from op reachable mutable */
            for (auto mut : local_muts(op)) {
                if constexpr (init) {
                    /* add expr to list of users from mut */
                    auto& st_mut = get_state(mut);
                    st_mut.muts_ = muts.insert(st_mut.muts_, expr);
                }

                /* now we add the free vars of the dependencies */
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

private:
    struct FVState {
        u32 mark_    = 0;
        DefSet vars_ = {}; ///< Mutable: local vars; Immutable: free vars.
        Muts muts_   = {}; ///< Immutable: local_muts; Mutable: users;
    };

    DefMap<std::unique_ptr<FVState>> state_;

    /// get the internal state of a Def (creates it if needed)
    FVState& get_state(const Def* def) {
        if (state_.contains(def)) return *state_.at(def);

        // create new state empty state for def
        state_.emplace(def, std::make_unique<FVState>());
        auto& st = *state_.at(def);

        /* according to some comments this is per definition right */
        if (auto var = def->isa<Var>()) {
            /* unpack vars if possible */
            for (auto v : var->tprojs())
                st.vars_.emplace(v);

            return st;
        }

        // if def is d#i I want to set vars_ as {def}
        // TODO: I have to check if this is the correct way
        if (def->isa<Extract>()) {
            st.vars_.emplace(def);
            return st;
        }

        auto& muts = def->world().muts();

        /* TODO: I made the assumption that the ops of def are already set. Is this allowed for this? */
        for (auto def : def->deps()) {
            for (auto v : local_vars(def))
                st.vars_.emplace(v);
            st.muts_ = muts.merge(st.muts_, local_muts(def)); /* TODO maybe replace with def->local_muts() ? */
        }

        return st;
    }

    /// Var%s reachable by following *immutable* deps().
    DefSet local_vars(const Def* expr) { return expr->is_mutable() ? DefSet() : get_state(expr).vars_; }

    /// Mutables reachable by following *immutable* deps(); `local_muts(mut)` is by definition the set `{ mut }`.
    Muts local_muts(const Def* expr) {
        /* TODO relpace with expr->local_muts() ? */
        if (auto mut = expr->isa_mut()) return Muts(mut);
        return get_state(expr).muts_;
    }
};

} // namespace mim::plug::clos2
