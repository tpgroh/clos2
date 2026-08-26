#pragma once

// TODO refactor comments

#include <bit>
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

private:
    struct FVState {
        u32 mark_    = 0;
        DefSet vars_ = {}; ///< Mutable: local vars; Immutable: free vars.
        // TODO: cache the extractions in the state
    };

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

class EXAnalysis {
public:
    void get_extractions(const Def* def) {
        // if def is Var then set the extractions of def to be all of def
        if (auto var = def->isa<Var>()) {
            // clear extractions
            auto map = (state_[var] = DefMap<u64>{});

            // put var inside
            map[var] = -1ull;
        }

        // if def is Extract then add it to the state of the Var from which it extracts
        else if (auto ext = def->isa<Extract>()) {
            // find the enclosed Var
            const Def* tmp = ext->tuple();
            while (auto t = tmp->isa<Extract>())
                tmp = t->tuple();
            auto var = tmp->isa<Var>(); // NOTE: I now expect tmp to be a Var
            assert(var);                // TODO: could there be something other then Var?

            // add extract to state of var
            auto map = state_[var];

            // if extract is already covered I can stop
            //   this is the case if transitively at least one of tuple() is already in the state
            // if the index is constant and the arity is such that I can unpack and not all arity bits would be set
            // afterwards, then set index bit of ext->tuple()
            //   this can be done by seting the bit and then check the count of set bits against the tarity of tuple()
            //   where we maxout tarity at 64
            // otherwise all indices are reachable so we add all extractions of ext->tuple() to be reachable
            //   - if tuple() is a var we want to set all bits
            //   - if tuple() is v#i I want to add v with set index bit i to the state of var
            //   this can be done by removing tuple() from the state and then add it using recursion
            //
            // TODO: QUESTION: if any of the extractions in ext have arity over the global threshold or 64 should I
            // unpack ? for example v has arity 1000000 but the extractions reachable are only v#1 which has arity 4
            // should I set the reachable extractions to {v} or {v#1} I'm currently going for the second one
            //
            // TODO: if I add an extraction v#i but v#i#j is already in the map, then I have to remove v#i#j

            // check if index is constant
            u64 idx_map = get_extraction_idxMap(ext);

            { // check if extract is already covered
                const Def* tmp  = ext;
                auto tmp_idxMap = idx_map;
                do {
                    // get tuple
                    if (auto ext = tmp->isa<Extract>()) {
                        tmp        = ext->tuple();
                        tmp_idxMap = get_extraction_idxMap(ext);
                    } else
                        assert(tmp
                               == var); // NOTE: at the start to find var we already checked that this has to be true

                    if (auto it = map.find(tmp); (it != map.end()) && (it->second & tmp_idxMap)) goto covered;
                } while (tmp != var);
            }

            // now we know that ext is not already covered by any other extraction inside the state of var

            // set index bit(s) if we dont set all bits.
            // in that case we dont want to potentially add (ext->tuple(), -1ull) to the hashmap just to remove it again
            if (idx_map != -1ull) idx_map = (map[ext->tuple()] |= idx_map);

            // check count of set bits to find out if all num_tprojs() extractions from ext->tuple() are collected
            // NOTE: on modern cpus there is an instruction for that and a good compiler should use that here
            if (static_cast<nat_t>(std::popcount(idx_map)) >= ext->tuple()->num_tprojs()) {
                // if ext->tuple() was Var just mark all extractions of ext->tuple() as reachable
                if (ext->tuple()->isa<Var>()) {
                    assert(ext->tuple() == var);
                    map[ext->tuple()] = -1ull; // all extractions of var are reachable
                } else {
                    // remove ext->tuple() from the map if it was in the map (might not be if we skiped insertion above)
                    auto it = map.find(ext->tuple());
                    if (it != map.end()) map.erase(it);

                    // mark every extraction of ext->tuple() as reachable by using recursion
                    get_extractions(ext->tuple());
                }
            }

covered: // this label is used to skip the above code if the extraction was already covered by any other extraction in
         // the state of var
        }

        // def was not an Extract so we collect all extractions from all deps()
        else {
            for (auto dep : def->deps())
                get_extractions(dep);
        }

        // TODO: I'm currently not sure If I need to collect the extractions from def->type() in every case but I would
        // guess so.
    }

private:
    /// return a bitmask for the index of Extract
    /// returns -1ull if the index is not constant and in the valid range
    u64 get_extraction_idxMap(const Extract* ext) {
        assert(ext);

        // ext->tuple() should not be unpacked NOTE: I maxout at 64 because I use u64 bitmaps to store the extracted
        // indices
        if (auto i = ext->tuple()->num_tprojs(); i == 1 || i >= 64)
            return -1ull;
        else if (auto idx = Lit::isa(ext->index())) {
            assert(idx < 64); // TODO: QUESTION: is the nat_t value in Idx always the smallest in [0,m) where m is the
                              // modus of Idx?
            return 1ull << *idx;
        }

        return -1ull;
    }

private:
    GIDNodeMap<const Var*, DefMap<u64>> state_ = {};
};

} // namespace mim::plug::clos2
