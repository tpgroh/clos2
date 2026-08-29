#pragma once

#include <optional>

#include "mim/def.h"
#include "mim/tuple.h"
#include "mim/world.h"

#include "mim/util/util.h"

namespace mim::plug::clos2 {

/// stores the extractions of a def by keeping track of all indices which are extracted
/// Analyse the extractions which are being made inside a Def
class EXAnalysis {
private:
    struct EXState {
        static constexpr nat_t width = 32; ///< the width increment of bitmaps

        u16 count                               = 0;  ///< the count of set bits
        std::vector<std::bitset<width>> idx_map = {}; ///< dynamic index bit map

        /// set an index and return whether it was not set before
        bool setIdx(nat_t idx) {
            if (isIdxSet(idx)) return false;

            auto i = idx / width;
            if (idx_map.size() <= i) idx_map.resize(i + 1);
            idx_map[i][idx % width] = true;
            count++;
            return true;
        }

        /// check if an index is already set
        bool isIdxSet(nat_t idx) const {
            auto i = idx / width;
            if (idx_map.size() <= i) return false;
            return idx_map[i][idx % width];
        }

        /// unify with other state
        bool unify(const EXState& other) {
            if (idx_map.size() < other.idx_map.size()) idx_map.resize(other.idx_map.size());

            // or on bitmaps for union
            for (size_t i = 0; i < other.idx_map.size(); i++)
                idx_map[i] |= other.idx_map[i];

            // recount set bits.
            auto old_count = count;
            count          = 0;
            for (size_t i = 0; i < idx_map.size(); i++)
                count += idx_map[i].count();

            return old_count != count;
        }

        /// are all indices set
        bool isAllSet() const {
            // an empty state means all indices are set. This is only used for the state of Var#i
            return idx_map.size() == 0;
        }

        /// get the extraction of tuple for given index
        std::optional<const Def*> get(const Def* tuple, std::optional<nat_t> idx) const {
            if (idx && isIdxSet(*idx)) return tuple->world().extract(tuple, *idx);
            return {};
        }
    };

public:
    /// create extraction analysis for def
    EXAnalysis(const Def* def) { include(def); }

    bool include(const EXAnalysis& other) {
        bool anychange = false;

        // iterate over all entries of others state
        for (const auto& [var, map] : other.getState())
            for (const auto& [tuple, exstate] : map) {
                if (tuple->isa<Var>()) {
                    if (state_[var].contains(tuple) && state_[var][tuple].isAllSet()) continue;
                    if (exstate.isAllSet()) {
                        state_[var][tuple] = {};
                        anychange          = true;
                        continue;
                    }

                    bool change = state_[var][tuple].unify(exstate);

                    // maybe we just added the last missing extraction.
                    if (change && state_[var][tuple].count >= tuple->num_tprojs()) {
                        std::cout << "collected all extractions of var " << tuple << "\n";
                        state_[var][tuple] = {}; // mark all as set
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
            map[var] = {}; // clear all var extractions which means include all
            std::cout << "added all extractions of var " << var << "\n";
        }

        // if def is Extract then add it to the state of the Var from which it extracts
        else if (auto ext = def->isa<Extract>()) {
            // find the enclosed Var
            auto var = getVarOfExt(ext);

            // add extract to state of var
            auto& map = state_[var];

            if (isExtCovered(ext, map)) return;

            // check if index is constant
            auto idx = getConstIdx(ext);

            // set index bit(s) if we dont set all bits.
            if (idx) {
                if (!map.contains(ext->tuple()) || !map[ext->tuple()].isAllSet()) {
                    map[ext->tuple()].setIdx(*idx);
                    std::cout << "setting idx " << *idx << " for " << ext->tuple() << "\n";
                } else
                    std::cout << "idx " << *idx << " is already covored by all set\n";
            }

            if (!idx || map[ext->tuple()].count >= ext->tuple()->num_tprojs()) {
                if (ext->tuple()->isa<Var>()) {
                    assert(ext->tuple() == var);
                    map[ext->tuple()] = {}; // add var to map by clearing the state
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
            return getCovering(ext, map, {});
        }

        return {};
    }

    std::optional<const Def*>
    getCovering(const Extract* ext, const DefMap<EXState>& map, std::optional<const Def*> prev) const {
        auto idx = getConstIdx(ext);

        // if the tuple is a var we just have to check if it is already in the map
        if (auto v = ext->tuple()->isa<Var>()) {
            if (!map.contains(v)) return prev;
            if (map.at(v).isAllSet()) return ext->tuple();
            auto found = map.at(v).get(ext->tuple(), idx);
            if (!found) return prev;
            return found;
        }

        auto tuple = ext->tuple()->isa<Extract>();
        assert(tuple); // TODO: could there be anything else?
        if (!idx || !map.contains(ext->tuple()))
            return getCovering(tuple, map, prev); // use t-recursion to find covering

        // found a covering now use t recursion to return the highest covering.
        auto found = map.at(ext->tuple()).get(ext->tuple(), idx);
        if (!found) return prev;
        return getCovering(tuple, map, found);
    }

    /// create the smallest Covering of a DefSet
    DefSet getCovering(const DefSet& old) const {
        DefSet set;

        for (auto d : old) {
            auto c = getCovering(d);
            assert(c);
            set.insert(*c);
        }

        return set;
    }

    /// TODO: remove this
    void print() const {
        std::cout << "print EXAnalysis state\n";
        for (auto& [var, map] : state_) {
            std::cout << "  extractions of " << var << "\n";
            for (auto& [tuple, ex] : map)
                std::cout << "    " << tuple << "#" << (ex.isAllSet() ? "ALL" : "???") << "\n";
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
    bool isExtCovered(const Extract* ext, const DefMap<EXState>& map) { return getCovering(ext, map, {}).has_value(); }

    const Var* getVarOfExt(const Extract* ext) const {
        const Def* tmp = ext->tuple();
        while (auto t = tmp->isa<Extract>())
            tmp = t->tuple();
        auto var = tmp->isa<Var>(); // NOTE: I now expect tmp to be a Var
        assert(var);                // TODO: could there be something other then Var?
        return var;
    }

    const GIDNodeMap<const Var*, DefMap<EXState>>& getState() const { return state_; }

private: // state
    GIDNodeMap<const Var*, DefMap<EXState>> state_ = {};
};

} // namespace mim::plug::clos2
