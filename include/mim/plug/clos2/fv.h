#pragma once

#include "mim/def.h"

#include "mim/plug/clos2/ex.h"

namespace mim::plug::clos2 {

class FVAnalysis {
private:
public:
    // calculate the set of free vars/var extractions
    DefSet free_vars(const Def* def) {
        EXAnalysis exs{def};

        // this is used to break cycles without having to implement fixed point solving
        // this allowes free_vars to keep track of what defs are currently on the call stack.
        // NOTE: this is used as FIFO thus there might be a faster datastructure
        DefSet active{};

        // calculate solution and store it in the permanant cache
        // the calculated set is correct because it is the union of all reachable free vars.
        // where the free var set we take the union over can only be missing free vars that are allready included
        // somewhere in another set
        auto [fvs, _] = free_vars(def, exs, active);
        fvs_[def] = fvs;

        return fvs;
    }

private:
    // calculate free_vars of def
    // note that this function must not write to fvs_, as fvs of a def here might be only a partial free var set
    // instead use the temporary cache, which we throw away after afterwards. this way I dont require fixed point
    // solving
    std::pair<DefSet, bool> free_vars(const Def* def, EXAnalysis& exs, DefSet& active) {
        // use cached result if it exists
        if (fvs_.contains(def)) return {fvs_.at(def), false};
        if (active.contains(def)) return {DefSet{}, true};

        // create fvs set and enqueue def to te active list
        auto fvs = DefSet{};
        active.insert(def);

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
            // here fvs is { def } which is the correct free vars set of def, thus no getCovering required
            assert(fvs.size() == 1);
            return {fvs, false};
        }

        // now we have to add the missing free_vars of reachable mutables. for this we can use local_muts()
        // I keep the loop over the deps because def might be a mutable itself
        bool tainted = false;
        for (auto op : def->deps()) {
            for (auto mut : op->local_muts()) {
                assert(mut->is_set()); // I use this phase only on already complete worlds which we dont modify. thus mut is set

                // I don't want to polute the extraction set of mut so I create a new one which I then include in
                // the current one
                // when free_vars returned early with tainted set then exs2 does not contain any new extractions
                // it should still be correct because the extractions that would have been added are allready somewhere down
                // the callstack and because tainted is set we throw away any results at least up to that def's free_vars call
                EXAnalysis exs2{mut};
                auto [fvs2, t] = free_vars(mut, exs2, active);
                tainted |= t; // if at least one free_vars call was tainted then this one is tainted as well
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

        // dequeue def from active
        active.erase(def);

        // if the result is not tainted than it is correct for the same reason as in the public facing free_vars
        // and we can store the result in the fvs_ cache
        if (!tainted) fvs_[def] = fvs;

        // if the result was tainted we propagete that down the call stack
        return {fvs, tainted};
    }

    // TODO: I should check if the following comment still holds, I think for fvs_ it is wrong
    // I have to use NodeMap because I require pointer/reference stability
    GIDNodeMap<const Def*, DefSet> fvs_, ///< stores computed free var sets (only after finished computation)
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

        return exts;
    }
};

} // namespace mim::plug::clos2
