#pragma once

// TODO refactor comments

#include <algorithm>

#include "mim/def.h"
#include "mim/tuple.h"
#include "mim/world.h"

#include "mim/util/util.h"

namespace mim::plug::clos2 {

// TODO: I chose bitmaps because I thought that I would perform many unions of EXAnalysis
// currently this is not the case. So maybe I have to rethink the data structure EXState.

/// stores the extractions of a def by keeping track of all indices which are extracted
struct EXState {
    // TODO: use std::vector<u32> to speed up union

    u16 count                 = 0;  ///< the count of set bits
    bool allSet               = 0;  ///< is all set
    std::vector<bool> idx_map = {}; ///< dynamic index bit map

    /// set all indices to true
    bool setAll() {
        if (isAllSet()) return false;

        count = 0;
        idx_map.resize(0);
        allSet = true;

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
    bool isAllSet() const { return allSet; }

    /// check if an index is already set
    bool isIdxSet(nat_t idx) const {
        if (isAllSet()) return true; // this is the same as all bits being set
        if (idx_map.size() <= idx) return false;
        return idx_map[idx];
    }

    std::optional<const Def*> get(const Def* tuple, std::optional<nat_t> idx) const {
        if (isAllSet()) return tuple;

        if (idx) {
            if (isIdxSet(*idx)) return tuple->world().extract(tuple, *idx);
            return {};
        }

        return {};
    }
};

/// Analyse the extractions which are being made inside a Def
class EXAnalysis {
private:
    friend auto& getState(const EXAnalysis& other) { return other.state_; }

public:
    /// create extraction analysis for def
    EXAnalysis(const Def* def) { include(def); }

    bool include(const EXAnalysis& other) {
        auto& ostate = getState(other);

        bool anychange = false;

        // iterate over all entries of others state
        for (const auto& [var, map] : ostate)
            for (const auto& [tuple, exstate] : map) {
                if (tuple->isa<Var>()) {
                    bool change = state_[var][tuple].unify(exstate);

                    // maybe we just added the last missing extraction.
                    if (change && state_[var][tuple].count >= tuple->num_tprojs()) {
                        std::cout << "collected all extractions of var " << tuple << "\n";
                        state_[var][tuple].setAll();
                    }
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
                        std::cout << "peal of from " << ext << "\n";
                        auto it = state_[var].find(tuple);
                        assert(it != state_[var].end());
                        state_[var].erase(it);
                        include(tuple);
                    }
                    anychange |= change;
                }
            }

        // return if something changed
        return anychange;
    }

    void include(const Def* def) {
        // if def is Var then set the extractions of def to be all of def
        if (auto var = def->isa<Var>()) {
            // clear extractions
            auto& map = (state_[var] = {});

            // put var inside
            map[var].setAll();
            std::cout << "added all extractions of var " << var << "\n";
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
            if (idx) {
                map[ext->tuple()].setIdx(*idx);
                std::cout << "setting idx " << *idx << " for " << ext->tuple() << "\n";
            }

            if (!idx || map[ext->tuple()].count >= ext->tuple()->num_tprojs()) {
                if (ext->tuple()->isa<Var>()) {
                    assert(ext->tuple() == var);
                    map[ext->tuple()].setAll(); // add var to map
                    std::cout << "setting all idx for " << ext->tuple() << "\n";
                } else {
                    std::cout << "peal of " << ext;
                    // remove ext->tuple() from the map if it was in the map (might not be if we skiped insertion above)
                    auto it = map.find(ext->tuple());
                    if (it != map.end()) map.erase(it);

                    // mark every extraction of ext->tuple() as reachable by using t-recursion
                    return include(ext->tuple());
                }
            }
        }

        // def was not an Extract so we collect all extractions from it's deps()
        else
            // TODO: it could be that I always want to include the type because of some special cases for def but I'm
            // not sure
            for (auto dep : def->deps())
                include(dep);
    }

    /// get highest covered extraction from def
    std::optional<const Def*> getCovering(const Def* def) const {
        if (auto var = def->isa<Var>()) {
            if (!state_.contains(var)) return {};
            if (!state_.at(var).contains(def)) return {};
            if (!state_.at(var).at(def).isAllSet()) return {};
            return def;
        }

        else if (auto ext = def->isa<Extract>()) {
            auto var = getVarOfExt(ext);
            if (!state_.contains(var)) return {};
            auto map = state_.at(var);
            return getCovering(ext, map);
        }

        return {};
    }

    std::optional<const Def*> getCovering(const Extract* ext, const DefMap<EXState>& map) const {
        auto idx = getConstIdx(ext);

        // if the tuple is a var we just have to check if it is already in the map
        if (auto v = ext->tuple()->isa<Var>()) {
            if (!map.contains(v)) return {};
            return map.at(v).get(ext->tuple(), idx);
        }

        if (!idx || !map.contains(ext->tuple())) {
            ext = ext->tuple()->isa<Extract>(); // we expect an extract because the tuple() is not a Var
            assert(ext);                        // TODO: could there be anything else?
            return getCovering(ext, map);       // use t-recursion
        }

        return map.at(ext->tuple()).get(ext->tuple(), idx);
    }

    /// create the smallest Covering of a DefSet
    DefSet getCovering(const DefSet& old) {
        DefSet set;

        for (auto d : old) {
            auto c = getCovering(d);
            assert(c);
            set.insert(*c);
        }

        return set;
    }

    void print() {
        std::cout << "print EXAnalysis state\n";
        for (auto& [var, _] : state_) {
            std::cout << "  extractions of " << var << "\n";
            for (auto& [tuple, _] : state_.at(var))
                std::cout << "    " << tuple << "#" << (state_.at(var).at(tuple).isAllSet() ? "ALL" : "???") << "\n";
        }
    }

private: // helpers
    /// get the index if const otherwise nullopt
    std::optional<nat_t> getConstIdx(const Extract* ext) const {
        auto a = Lit::isa(ext->index());
        auto i = ext->tuple()->num_tprojs();

        if (a && i > 1) {
            assert(*a < i); // TODO: this should always be the case so it should be save to removes this
            return a;
        }
        return {};
    }

    /// check if extract is already covered by any other extract in the state of var
    bool isExtCovered(const Extract* ext, const DefMap<EXState>& map) { return getCovering(ext, map).has_value(); }

    const Var* getVarOfExt(const Extract* ext) const {
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

} // namespace mim::plug::clos2
