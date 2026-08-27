#pragma once

// TODO refactor comments

#include <algorithm>

#include "mim/def.h"
#include "mim/tuple.h"

#include "mim/util/util.h"

namespace mim::plug::clos2::fv {

// TODO: I wanted to use the bitmap to speed up the union of results.
// maybe now with std::vector<bool> this is to slow to justyfy not just using a tree
// with a tree I could also fairly easy drop covored extractions from the state
// TODO: If the vector is to slow I could write my own dynamic bitmap which uses a vector of u64 bitmaps this way I
// loose the 64 while keeping the speed in union restriction

/// I want to use the result of this to get the free vars of a def
///
/// for a immutable def this means that I run this on every def of local_muts() and take the union of the results.
/// that is then the result for def.
///
/// from this I already get
/// TODO: I need a union function to combine the results
/// TODO: I need a function to retrieve the set of free vars
///
/// for mutable def I also need the union function
/// TODO: and a function to remove the extractions of a Var.
///
///

/// stores the extractions of a def by keeping track of all indices which are extracted
struct EXState {
    // TODO: use std::vector<u32> to speed up union

    u16 count                 = 0;  ///< the count of set bits
    std::vector<bool> idx_map = {}; ///< dynamic index bit map

    /// set all idx to true
    bool setAll() {
        if (idx_map.size() == 0) return false;

        count = 0;
        idx_map.resize(0);

        return true;
    }

    /// set an index and return whether it was not set before
    bool setIdx(nat_t idx) {
        if (isIdxSet(idx)) return false;

        if (idx_map.size() <= idx) idx_map.resize(idx + 1);
        idx_map[idx] = true;
        count++;
        return true;
    }

    // TODO: for union I'll need a function that or's two idx_map's
    bool unify(const EXState& other) {
        if (isAllSet()) return false;
        if (other.isAllSet()) return setAll(), true;

        if (idx_map.size() < other.idx_map.size()) idx_map.resize(other.idx_map.size());

        // TODO: use logical or to do this after transforming into vector<u32>
        for (size_t idx = 0; idx < other.idx_map.size(); idx++)
            idx_map[idx] = idx_map[idx] || other.idx_map[idx];

        // TODO: use popcount to recalculate count
        auto old_count = count;
        count          = std::ranges::count(idx_map, true);

        return count != old_count;
    }

    /// are all idx set
    bool isAllSet() const { return idx_map.size() == 0; }

    /// check if an index is already set
    bool isIdxSet(nat_t idx) const {
        if (idx_map.size() == 0) return true; // this is the same as all bits beeing set
        if (idx_map.size() <= idx) return false;
        return idx_map[idx];
    }
};

/// Analyse the extractions which are beeing made inside a Def
class EXAnalysis {
private:
    friend auto& getState(const EXAnalysis& other) { return other.state_; }

public:
    bool include(const EXAnalysis& other) {
        auto& ostate = getState(other);

        bool anychange = false;

        // iterate over all entries of others state
        for (const auto& [var, map] : ostate)
            for (const auto& [tuple, exstate] : map) {
                if (tuple->isa<Var>()) {
                    bool change = state_[var][var].unify(exstate);

                    // maybe we just added the last missing extraction.
                    if (change && state_[var][tuple].count >= tuple->num_tprojs()) state_[var][var].setAll();
                    anychange |= change;
                } else {
                    // if tuple is already covered then tuple#exstate is also covered
                    auto ext = tuple->isa<Extract>();
                    assert(ext); // TODO: is there some other possible case?
                    if (isExtCovered(ext, state_[var])) continue;

                    // tuple is not covered so tuple#exstate can be added to the state
                    bool change = state_[var][tuple].unify(exstate);

                    // maybe we just included all or collected the last missing extractions so peal one off
                    if (change && state_[var][tuple].count >= tuple->num_tprojs()) {
                        auto it = state_[var].find(tuple);
                        assert(it != state_[var].end());
                        state_[var].erase(it);
                        includeFromDef(tuple);
                    }
                    anychange |= change;
                }
            }

        // return if something changed
        return anychange;
    }

    void includeFromDef(const Def* def) {
        // if def is Var then set the extractions of def to be all of def
        if (auto var = def->isa<Var>()) {
            // clear extractions
            auto& map = (state_[var] = {});

            // put var inside
            map[var].setAll();
        }

        // if def is Extract then add it to the state of the Var from which it extracts
        else if (auto ext = def->isa<Extract>()) {
            // find the enclosed Var
            auto var = getVarOfExt(ext);

            // add extract to state of var
            auto& map = state_[var];

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

            if (isExtCovered(ext, map)) return;

            // check if index is constant
            auto idx = getConstIdx(ext);

            // set index bit(s) if we dont set all bits.
            // in that case we dont want to potentially add (ext->tuple(), -1ull) to the hashmap just to remove it again
            if (idx) map[ext->tuple()].setIdx(*idx);

            if (!idx || map[ext->tuple()].count >= ext->tuple()->num_tprojs()) {
                if (ext->tuple()->isa<Var>()) {
                    assert(ext->tuple() == var);
                    map[ext->tuple()].setAll(); // add var to map
                } else {
                    // remove ext->tuple() from the map if it was in the map (might not be if we skiped insertion above)
                    auto it = map.find(ext->tuple());
                    if (it != map.end()) map.erase(it);

                    // mark every extraction of ext->tuple() as reachable by using t-recursion
                    return includeFromDef(ext->tuple());
                }
            }
        }

        // def was not an Extract so we collect all extractions from it's deps()
        else
            // TODO: it could be that I dont want to do this or at least that I dont want to include the type. I have to
            // check later
            for (auto dep : def->deps())
                includeFromDef(dep);
    }

private: // helpers
    /// get the index if const otherwise nullopt
    std::optional<nat_t> getConstIdx(const Extract* ext) {
        auto a = Lit::isa(ext->index());
        auto i = ext->tuple()->num_tprojs();

        if (a && i > 1) {
            assert(*a < i); // TODO: this should always be the case so it should be save to removes this
            return a;
        }
        return {};
    }

    /// check if extract is already covered by any other extract in the state of var
    bool isExtCovered(const Extract* ext, const DefMap<EXState>& map) {
        auto idx = getConstIdx(ext);

        // if the tuple is a var we just have to check if it is already in the map
        if (auto v = ext->tuple()->isa<Var>()) {
            if (!map.contains(v)) return false;
            return (idx) ? map.at(v).isIdxSet(*idx) : map.at(v).isAllSet();
        }

        if (!idx || !map.contains(ext->tuple())) {
            ext = ext->tuple()->isa<Extract>(); // we expect an extract because the tuple() is not a Var
            assert(ext);                        // TODO: could there be anything else?
            return isExtCovered(ext, map);      // use t-recursion
        }

        return map.at(ext->tuple()).isIdxSet(*idx);
    }

    const Var* getVarOfExt(const Extract* ext) {
        const Def* tmp = ext->tuple();
        while (auto t = tmp->isa<Extract>())
            tmp = t->tuple();
        auto var = tmp->isa<Var>(); // NOTE: I now expect tmp to be a Var
        assert(var);                // TODO: could there be something other then Var?
        return var;
    }

private: // state
    GIDNodeMap<const Var*, DefMap<EXState>> state_ = {};
};

} // namespace mim::plug::clos2::fv
