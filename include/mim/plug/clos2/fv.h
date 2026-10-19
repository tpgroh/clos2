#pragma once

#include "mim/def.h"

#include "mim/plug/clos2/ex.h"

namespace mim::plug::clos2 {

class FVAnalysis {
public:
    DefSet free_vars(const Def* def) {
        EXAnalysis exs{def};
        return free_vars(def, exs);
    }
    
    DefSet free_vars(Def* def) {
        EXAnalysis exs{def};
        return free_vars(def, exs);
    }

    DefSet free_vars(const Def* def, EXAnalysis& exs) {
        if (auto mut = def->isa_mut()) return free_vars(mut, exs);

        auto fvs = local_vars(def);
        for (auto mut : def->local_muts()) {
            assert(mut->is_set());

            EXAnalysis exs2{mut};
            auto fvs2 = free_vars(mut, exs2);
            exs.include(exs2);

            for (auto v : exs.getCovering<true>(fvs2))
                fvs.insert(v);
        }

        return exs.getCovering<false>(fvs);
    }

    DefSet free_vars(Def* def, EXAnalysis& exs) {
        // we cache free vars of mutables
        if (fvs_.contains(def)) return get_state(def);

        auto& st = get_state(def);

        for (auto op : def->deps()) {
            // include all local_vars reachable
            for (auto d : exs.getCovering(local_vars(op)))
                st.insert(d);

            // and add the free vars of every from op reachable mutable
            for (auto mut : op->local_muts()) {
                assert(mut->is_set());

                // I don't want to polute the extraction set of mut so I create a new one which I then include in
                // the current one
                EXAnalysis exs2{mut};
                auto fvs2 = free_vars(mut, exs2);
                exs.include(exs2);

                for (auto v : exs.getCovering<true>(fvs2))
                    st.insert(v);
            }
        }

        // by including var to exs the minimization in the next step will reduce all extractions of var to just var.
        // this way we can just drop var without another search for extractions of it
        if (auto var = def->has_var()) exs.include(var);

        // minimize vars_ (there might be entries which are covered by another extraction in exs)
        st = exs.getCovering<false>(st);

        // FV(lam x.e) = FV(e) \ {x}
        if (auto var = def->has_var()) st.erase(var);

        // the free var set is stored in the state
        return st;
    }

    constexpr auto is_closed(const Def* def) const { return def->is_closed(); }
    constexpr auto is_open(const Def* def) const { return def->is_open(); }

private:
    GIDNodeMap<const Def*, DefSet> fvs_;

    /// get the internal state of a Def (creates it if needed)
    DefSet& get_state(const Def* def) {
        if (fvs_.contains(def)) return fvs_.at(def);

        // create new state empty state for def
        auto& st = fvs_[def]; // default initializes the state

        // init local vars
        if (def->isa<Var>())
            st.insert(def);
        else if (auto ext = def->isa<Extract>(); ext && EXAnalysis::getVarOfExt(ext))
            st.insert(def);
        else
            for (auto dep : def->deps())
                for (auto v : local_vars(dep))
                    st.insert(v);

        return st;
    }

    /// Var%s reachable by following *immutable* deps().
    DefSet local_vars(const Def* expr) { return expr->is_mutable() ? DefSet{} : get_state(expr); }
};

} // namespace mim::plug::clos2
