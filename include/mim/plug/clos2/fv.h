#pragma once

#include "mim/def.h"

#include "mim/plug/clos2/ex.h"

namespace mim::plug::clos2 {

class FVAnalysis {
private:
    using Cache = GIDNodeMap<const Def*, DefSet>;

public:
    // calculate the set of free vars/var extractions
    DefSet free_vars(const Def* def) {
        EXAnalysis exs{def};
        Cache cache{};
        auto fvs = free_vars(def, exs, cache);
        fvs_[def] = fvs;
        return fvs;
    }

    // with fast set we can use getCovering in fast mode instead
    template<bool fast=false>
    DefSet free_vars(const Def* def, EXAnalysis& exs, Cache& cache) {
        if (auto mut = def->isa_mut()) return free_vars<fast>(mut, exs, cache);

        // if the free vars of this def where already computed use the cached one
        if (fvs_.contains(def)) return fvs_.at(def);

        auto fvs = local_extracts(def, cache);
        for (auto mut : def->local_muts()) {
            assert(mut->is_set());

            EXAnalysis exs2{mut};
            auto fvs2 = free_vars<true>(mut, exs2, cache);
            exs.include(exs2);

            for (auto v : exs.getCovering<true>(fvs2))
                fvs.insert(v);
        }

        return exs.getCovering<fast>(fvs);
    }

    // with fast set we can use getCovering in fast mode instead
    template<bool fast=false>
    DefSet free_vars(Def* def, EXAnalysis& exs, Cache& cache) {
        // use cached result if it exists
        if (fvs_.contains(def)) return fvs_.at(def);
        if (cache.contains(def)) return cache.at(def);

        // create cache because def is mutable (might appear down the line)
        auto& st = get_state(def, cache);

        for (auto op : def->deps()) {
            // include all local_extracts reachable
            for (auto d : exs.getCovering<true>(local_extracts(op, cache)))
                st.insert(d);

            // and add the free vars of every from op reachable mutable
            for (auto mut : op->local_muts()) {
                assert(mut->is_set());

                // I don't want to polute the extraction set of mut so I create a new one which I then include in
                // the current one
                EXAnalysis exs2{mut};
                auto fvs2 = free_vars<true>(mut, exs2, cache);
                exs.include(exs2);

                for (auto v : exs.getCovering<true>(fvs2))
                    st.insert(v);
            }
        }

        // by including var to exs the minimization in the next step will reduce all extractions of var to just var.
        // this way we can just drop var without another search for extractions of it
        if (auto var = def->has_var()) exs.include(var);

        // minimize vars_ (there might be entries which are covered by another extraction in exs)
        st = exs.getCovering<fast>(st);

        // FV(lam x.e) = FV(e) \ {x}
        if (auto var = def->has_var()) st.erase(var);

        // the free var set is stored in the state
        return st;
    }

private:
    // this cache stores computed free var sets (only after finished computation)
    Cache fvs_;

    // calculates a set of Vars and Var extractions that are found by following deps
    DefSet local_extracts(const Def* expr, Cache& cache) { return expr->is_mutable() ? DefSet{} : get_state(expr, cache); }

    // get the current state of a def or create a new one filled with the local_extracts of the def
    DefSet& get_state(const Def* def, Cache& cache) {
        if (cache.contains(def)) return cache.at(def);
        if (fvs_.contains(def)) return fvs_.at(def);

        // create new empty state for def
        auto& st = cache[def]; // default initializes the state

        // fill the state with collected Vars/Extracts of Var that are reachable by following deps()
        if (def->isa<Var>())
            st.insert(def);
        else if (auto ext = def->isa<Extract>(); ext && EXAnalysis::getVarOfExt(ext))
            st.insert(def);
        else
            for (auto dep : def->deps())
                for (auto v : local_extracts(dep, cache))
                    st.insert(v);

        return st;
    }
};

} // namespace mim::plug::clos2
