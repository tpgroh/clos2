#pragma once

#include "mim/def.h"

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
        if (auto mut = def->isa_mut()) return free_vars(mut, exs);

        auto fvs = local_vars(def);
        for (auto mut : def->local_muts()) {
            EXAnalysis exs2{mut};
            auto fvs2 = free_vars(mut, exs2);
            exs.include(exs2);

            for (auto v : exs.getCovering(fvs2))
                fvs.insert(v);
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
            for (auto op : def->deps()) {
                // include all local_vars reachable
                for (auto d : exs.getCovering(local_vars(op)))
                    st.vars_.insert(d);

                // and add the free vars of every from op reachable mutable
                for (auto mut : op->local_muts()) {
                    // I don't want to polute the extraction set of mut so I create a new one which I then include in
                    // the current one
                    EXAnalysis exs2{mut};
                    auto fvs2 = free_vars(mut, exs2);
                    exs.include(exs2);

                    for (auto v : exs.getCovering(fvs2))
                        st.vars_.insert(v);
                }
            }

            // by including var to exs the minimization in the next step will reduce all extractions of var to just var.
            // this way we can just drop var without another search for extractions of it
            if (auto var = def->has_var()) exs.include(var);

            // minimize vars_ (there might be entries which are covered by another extraction in exs)
            st.vars_ = exs.getCovering(st.vars_);

            // FV(lam x.e) = FV(e) \ {x}
            if (auto var = def->has_var()) st.vars_.erase(var);

            st.mark_ = true;
        }

        // the free var set is stored in the state
        return st.vars_;
    }

private:
    struct FVState {
        bool mark_   = false;
        DefSet vars_ = {}; ///< Mutable: local vars; Immutable: free vars.
    };

    GIDNodeMap<const Def*, FVState> state_;

    /// get the internal state of a Def (creates it if needed)
    FVState& get_state(const Def* def) {
        if (state_.contains(def)) return state_.at(def);

        // create new state empty state for def
        auto& st = state_[def]; // default initializes the state

        // init local vars
        if (def->isa<Var>())
            st.vars_.insert(def);
        else if (auto ext = def->isa<Extract>(); ext && EXAnalysis::getVarOfExt(ext))
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
