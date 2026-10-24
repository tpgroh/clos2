#pragma once

#include "mim/def.h"

#include "mim/plug/clos2/ex.h"

namespace mim::plug::clos2 {

class FVAnalysis {
private:
    // I have to use NodeMap because I require pointer/reference stability
    using Cache = GIDNodeMap<const Def*, DefSet>;

public:
    // calculate the set of free vars/var extractions
    DefSet free_vars(const Def* def) {
        EXAnalysis exs{def};

        // this temporary cache is used to break cycles.
        // it stores partial sets of local_extracts which might not be complete. (because of cycles)
        // note that the result of free_vars is a complete set, to use a single cache I must use fixedpoint solving
        Cache cache{};

        // calculate solution and store it in the permanant cache
        auto fvs = free_vars(def, exs, cache);
        fvs_[def] = fvs;

        return fvs;
    }

    DefSet free_vars(const Def* def, EXAnalysis& exs, Cache& cache) {
        // use cached result if it exists
        if (fvs_.contains(def)) return fvs_.at(def);
        if (cache.contains(def)) return cache.at(def);

        // collect inside of the temporary cache
        auto& fvs = cache[def];

        // first we have to collect all local_extractions
        // if def is immutable then we use local_extracts()
        // if def is mutable then we take the union of the local_extracts of all immutable deps
        if (def->isa_imm())
            fvs = local_extracts(def);
        else // for mutables I have to walk
            for (auto op : def->deps())
                if (op->isa_imm())
                    for (auto d : local_extracts(op))
                        fvs.insert(d);

        // if def is a Var or extract over a var I have to bail without walking the deps
        if (auto ext = def->isa<Extract>(); def->isa<Var>() || (ext && EXAnalysis::getVarOfExt(ext))) {
            // fvs can only contain def or an extract of it
            assert(fvs.size() == 1);
            return fvs;
        }

        // now we have to add the missing free_vars of reachable mutables. for this we can use local_muts()
        // I keep the loop over the deps because def might be a mutable itself
        for (auto op : def->deps()) {
            for (auto mut : op->local_muts()) {
                assert(mut->is_set()); // I use this phase only on already complete worlds which are frozen. thus mut is set

                // I don't want to polute the extraction set of mut so I create a new one which I then include in
                // the current one
                EXAnalysis exs2{mut};
                auto fvs2 = free_vars(mut, exs2, cache);
                exs.include(exs2);

                for (auto v : fvs2)
                    fvs.insert(v);
            }
        }

        // remove var if def has one and limit fvs to getCovering of it
        if (auto var = def->has_var()) {
            // by including var to exs the minimization in the next step will reduce all extractions of var to just var.
            // this way we can just drop var without another search for extractions of it
            exs.include(var);
            fvs = exs.getCovering(fvs);
            fvs.erase(var);
        } else
            fvs = exs.getCovering(fvs);

        return fvs;
    }

private:
    Cache fvs_, ///< stores computed free var sets (only after finished computation)
          exts_ ///< caches local_extracts
    ;

    // calculates a set of Vars and Var extractions that are found by following deps
    const DefSet& local_extracts(const Def* def) {
        assert(!def->isa_mut() && "local_extracts() does not take mutables, only immutables");

        if (exts_.contains(def)) return exts_.at(def);

        auto& exts = exts_[def];

        // collect Vars/Extracts of Vars that are reachable (by following immutable deps())
        if (def->isa<Var>())
            exts.insert(def);
        else if (auto ext = def->isa<Extract>(); ext && EXAnalysis::getVarOfExt(ext))
            exts.insert(def);
        else
            for (auto dep : def->deps()) {
                if (dep->isa_mut()) continue; // skip mutables, for those local_extracts is not callable and is per definition {}
                for (auto v : local_extracts(dep))
                    exts.insert(v);
            }

        return exts_[def];
    }
};

} // namespace mim::plug::clos2
