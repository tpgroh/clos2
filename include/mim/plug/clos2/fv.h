#pragma once

// TODO refactor comments

#include "mim/def.h"

#include "mim/util/util.h"

#include "mim/plug/clos2/ex.h"

namespace mim::plug::clos2 {

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

        return exs.getCovering(fvs);
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

        if (!st.mark_) {
            // enforce local_muts to be calculated
            // TODO: can I assume that this is already the case?
            def->free_vars();

            for (auto op : def->deps()) {
                // include all local_vars reachable
                for (auto d : local_vars(op)) {
                    auto c = exs.getCovering(d);
                    assert(c);
                    st.vars_.insert(*c);
                }

                // and add the free vars of every from op reachable mutable
                for (auto mut : op->local_muts()) {
                    exs.include(mut);
                    for (auto v : free_vars(mut, exs)) {
                        auto c = exs.getCovering(v);
                        assert(c);
                        st.vars_.insert(*c);
                    }
                }
            }

            std::cout << "\nafter calculating free vars of " << def << "\n";
            exs.print();

            // by including var to exs the minimization in the next step will reduce all extractions of var to just var.
            // this way we can just drop var without another search for extractions of it
            if (auto var = def->has_var()) {
                exs.include(var);
                std::cout << "\nafter including var of " << def << "\n";
                exs.print();
            }

            // minimize vars_ (there might be entries which are covered by another extraction in exs)
            std::cout << "free vars before and after minimize\n{ ";
            for (auto v : st.vars_)
                std::cout << v << ", ";
            std::cout << "}\n{ ";
            st.vars_ = exs.getCovering(st.vars_);
            for (auto v : st.vars_)
                std::cout << v << ", ";
            std::cout << "}\n";

            // FV(lam x.e) = FV(e) \ {x}
            if (auto var = def->has_var()) st.vars_.erase(var);

            st.mark_ = true;
        }

        // the free var set is stored in the state
        return st.vars_;
    }

private:
    struct FVState {
        bool mark_   = 0;
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
