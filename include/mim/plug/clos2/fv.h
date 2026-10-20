#pragma once

#include "mim/def.h"

#include "mim/plug/clos2/ex.h"

namespace mim::plug::clos2 {

class FVAnalysis {
private:
    using Cache = GIDNodeMap<const Def*, DefSet>;

public:
    DefSet free_vars(const Def* def) {
        EXAnalysis exs{def};
        Cache cache{};
        auto fvs = free_vars(def, exs, cache);
        fvs_[def] = fvs;
        return fvs;
    }
    
    DefSet free_vars(const Def* def, EXAnalysis& exs, Cache& cache) {
        if (auto mut = def->isa_mut()) return free_vars(mut, exs, cache);

        // if the free vars of this def where already computed use the cached one
        if (fvs_.contains(def)) return fvs_.at(def);

        auto fvs = local_vars(def, cache);
        for (auto mut : def->local_muts()) {
            assert(mut->is_set());

            EXAnalysis exs2{mut};
            auto fvs2 = free_vars(mut, exs2, cache);
            exs.include(exs2);

            for (auto v : exs.getCovering<true>(fvs2))
                fvs.insert(v);
        }

        return exs.getCovering<false>(fvs);
    }

    DefSet free_vars(Def* def, EXAnalysis& exs, Cache& cache) {
        // we cache free vars of mutables
        if (fvs_.contains(def)) return fvs_.at(def);
        if (cache.contains(def)) return cache.at(def);

        auto& st = get_state(def, cache);

        for (auto op : def->deps()) {
            // include all local_vars reachable
            for (auto d : exs.getCovering(local_vars(op, cache)))
                st.insert(d);

            // and add the free vars of every from op reachable mutable
            for (auto mut : op->local_muts()) {
                assert(mut->is_set());

                // I don't want to polute the extraction set of mut so I create a new one which I then include in
                // the current one
                EXAnalysis exs2{mut};
                auto fvs2 = free_vars(mut, exs2, cache);
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

private:
    Cache fvs_;

    /// Var%s reachable by following *immutable* deps().
    DefSet local_vars(const Def* expr, Cache& cache) { return expr->is_mutable() ? DefSet{} : get_state(expr, cache); }

    /// get the internal state of a Def (creates it if needed)
    DefSet& get_state(const Def* def, Cache& cache) {
        if (cache.contains(def)) return cache.at(def);
        if (fvs_.contains(def)) return fvs_.at(def);

        // create new state empty state for def
        auto& st = cache[def]; // default initializes the state

        // init local vars
        if (def->isa<Var>())
            st.insert(def);
        else if (auto ext = def->isa<Extract>(); ext && EXAnalysis::getVarOfExt(ext))
            st.insert(def);
        else
            for (auto dep : def->deps())
                for (auto v : local_vars(dep, cache))
                    st.insert(v);

        return st;
    }
};

} // namespace mim::plug::clos2
