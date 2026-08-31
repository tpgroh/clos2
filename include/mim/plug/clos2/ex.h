#pragma once

#include <optional>

#include "mim/def.h"
#include "mim/tuple.h"
#include "mim/world.h"

#include "fe/bitset.h"

namespace mim::plug::clos2 {

/// stores the extractions of a def by keeping track of all indices which are extracted
/// Analyse the extractions which are being made inside a Def
class EXAnalysis {
private:
    using Map   = DefMap<fe::Bitset>;
    using State = GIDNodeMap<const Var*, Map>;

public:
    /// create extraction analysis for def
    EXAnalysis(const Def* def) { include(def); }

    bool include(const EXAnalysis& other) {
        bool anychange = false;

        // iterate over all entries of others state
        for (const auto& [var, map] : other.getState())
            for (const auto& [tuple, exstate] : map) {
                // we differentiate between Var and Extract because we have a special way to mark all idx to be
                // exctracted for Var
                if (tuple->isa<Var>()) {
                    assert(tuple == var);
                    // skip if we already include all extractions from var
                    if (state_[var].contains(tuple) && state_[var].at(tuple).none()) continue;
                    // set all extractions if the other included all
                    if (exstate.none()) {
                        state_[var][tuple].clear();
                        anychange = true;
                        continue;
                    }

                    // otherwise unify both states
                    auto old_count = state_[var][tuple].count();
                    state_[var][tuple] |= exstate;
                    auto count = state_[var][tuple].count();

                    if (old_count != count) {
                        // maybe we just added the last missing extraction.
                        if (count >= tuple->num_tprojs()) state_[var][tuple].clear(); // mark all as set
                        anychange = true;
                    }
                } else {
                    // if tuple is already covered then tuple#exstate is also covered
                    auto ext = tuple->isa<Extract>();
                    assert(ext);
                    if (isExtCovered(ext, state_[var])) continue;

                    // tuple is not covered so tuple#exstate can be added to the state
                    auto old_count = state_[var][tuple].count();
                    state_[var][tuple] |= exstate;
                    auto count = state_[var][tuple].count();

                    if (old_count != count) {
                        // maybe we just included all or collected the last missing extractions so peal one off
                        if (count >= tuple->num_tprojs()) {
                            // remove tuple#* from state and add tuple
                            auto it = state_[var].find(tuple);
                            assert(it != state_[var].end());
                            state_[var].erase(it);
                            include(tuple);
                        }
                        anychange = true;
                    }
                }
            }

        // return if something changed
        return anychange;
    }

    /// include a Def into the Analysis
    void include(const Def* def) {
        // if def is Var then set the extractions of def to be all of def
        if (auto var = def->isa<Var>()) {
            // clear extractions
            auto& map = (state_[var] = {});

            // put var inside
            map[var] = {}; // clear all var extractions which means include all
            return;
        }

        // if def is Extract then add it to the state of the Var from which it extracts
        auto ext = def->isa<Extract>();
        auto var = ext ? getVarOfExt(ext) : nullptr;

        if (var) {
            // add extract to state of var
            auto& map = state_[var];

            if (isExtCovered(ext, map)) return;

            // check if index is constant
            auto idx = getExtIdx(ext);

            // set index bit(s) if we dont set all bits.
            if (idx)
                if (!map.contains(ext->tuple()) || !map[ext->tuple()].none()) map[ext->tuple()].set(*idx);

            // peel-of if idx was not constant or if we just collected all extractions
            if (!idx || map[ext->tuple()].count() >= ext->tuple()->num_tprojs()) {
                // clear all if tuple is Var
                if (ext->tuple()->isa<Var>()) {
                    assert(ext->tuple() == var);
                    map[ext->tuple()].clear(); // add var to map by clearing the state
                } else {
                    // remove ext->tuple() from the map if it was in the map
                    // (might not be if we skiped insertion above)
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

    /// get covered extraction from def
    template<bool fast = false>
    std::optional<const Def*> getCovering(const Def* def) const {
        if (auto var = def->isa<Var>()) {
            if (!state_.contains(var)) return {};
            if (!state_.at(var).contains(def)) return {};
            if (!state_.at(var).at(def).none()) return {};
            return def;
        }

        if (auto ext = def->isa<Extract>()) {
            auto var = getVarOfExt(ext);
            assert(var);
            if (!state_.contains(var)) return {};
            auto map = state_.at(var);
            return getCovering<fast>(ext, map, {});
        }

        return {};
    }

    /// get covering of extraction if in state
    /// using the template var `fast` you can specify whether we search for the top most or if we stop as soon as we
    /// found any couvering extraction. even a dangling one
    template<bool fast = false>
    std::optional<const Def*> getCovering(const Extract* ext, const Map& map, std::optional<const Def*> prev) const {
        auto idx = getExtIdx(ext);

        // if the tuple is a var we just have to check if it is already in the map
        if (auto v = ext->tuple()->isa<Var>()) {
            if (!map.contains(v)) return prev;
            if (map.at(v).none()) return ext->tuple();
            auto found = getExt(ext->tuple(), map.at(v), idx);
            if (!found) return prev;
            return found;
        }

        auto tuple = ext->tuple()->isa<Extract>();
        assert(tuple);
        if (!idx || !map.contains(ext->tuple()))
            return getCovering<fast>(tuple, map, prev); // use t-recursion to find covering

        // found a covering now use t recursion to return the highest covering.
        auto found = getExt(ext->tuple(), map.at(ext->tuple()), idx);
        if constexpr (!fast) {
            if (!found) return prev;
            return getCovering<fast>(tuple, map, found);
        } else
            return found;
    }

    /// check if extract is already covered by any other extract in the state of var
    bool isExtCovered(const Extract* ext, const Map& map) { return getCovering<true>(ext, map, {}).has_value(); }

    /// create the smallest Covering of a DefSet
    template<bool fast = false>
    DefSet getCovering(const DefSet& old) const {
        DefSet set;

        for (auto d : old) {
            auto c = getCovering<fast>(d);
            assert(c);
            set.insert(*c);
        }

        return set;
    }

    /// get the index if const otherwise nullopt
    static std::optional<nat_t> getExtIdx(const Extract* ext) {
        auto a = Lit::isa(ext->index());
        auto i = ext->tuple()->num_tprojs();

        if (a && i > 1) {
            assert(*a < i);
            return a;
        }
        return {};
    }

    static const Var* getVarOfExt(const Extract* ext) {
        const Def* tmp = ext->tuple();
        while (auto t = tmp->isa<Extract>())
            tmp = t->tuple();
        auto var = tmp->isa<Var>();
        return var;
    }

    /// get the extraction of tuple for given Bitset and idx
    std::optional<const Def*> getExt(const Def* tuple, const fe::Bitset& idx_map, std::optional<nat_t> idx) const {
        if (idx && idx_map[*idx]) return tuple->world().extract(tuple, *idx);
        return {};
    }

    /// get const ref to state
    const GIDNodeMap<const Var*, Map>& getState() const { return state_; }

private: // state
    State state_ = {};
};

} // namespace mim::plug::clos2
