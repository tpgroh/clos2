#pragma once

#include "mim/def.h"
#include "mim/tuple.h"
#include "mim/world.h"

#include "mim/util/util.h"

namespace mim::plug::clos2 {

/// stores the extractions of a def by keeping track of all indices which are extracted
/// Analyse the extractions which are being made inside a Def
class EXAnalysis {
private:
    friend auto& getState(const EXAnalysis& other) { return other.state_; }

    struct EXState {
        u16 count                 = 0;  ///< the count of set bits
        std::vector<bool> idx_map = {}; ///< dynamic index bit map

        /// set an index and return whether it was not set before
        bool setIdx(nat_t idx) {
            if (isIdxSet(idx)) return false;

            if (idx_map.size() <= idx) idx_map.resize(idx + 1);
            idx_map[idx] = true;
            count++;
            return true;
        }

        /// check if an index is already set
        bool isIdxSet(nat_t idx) const {
            if (idx_map.size() <= idx) return false;
            return idx_map[idx];
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
                map[ext->tuple()].setIdx(*idx);
                std::cout << "setting idx " << *idx << " for " << ext->tuple() << "\n";
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
            return getCovering(ext, map);
        }

        return {};
    }

    std::optional<const Def*> getCovering(const Extract* ext, const DefMap<EXState>& map) const {
        auto idx = getConstIdx(ext);

        // if the tuple is a var we just have to check if it is already in the map
        if (auto v = ext->tuple()->isa<Var>()) {
            if (!map.contains(v)) return {};
            if (map.at(v).isAllSet()) return ext->tuple();
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
