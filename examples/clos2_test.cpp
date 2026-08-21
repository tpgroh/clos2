#include <memory>
#include <mim/driver.h>

#include <mim/ast/parser.h>
#include <mim/phase/optimize.h>
#include <mim/util/sys.h>

#include <mim/plug/mem/mem.h>
#include "mim/def.h"

#include "mim/plug/core/autogen.h"

using namespace mim;
using namespace mim::plug;

/**
 * This is used to store the state of the fixedpoint iteration solver.
 *
 * NOTE
 * the normal libmim version stores those directly as data member is Def
 * we cannot do it that way thus we store it in this extra struct
 */
class FVAnalysis {
public:
    Vars free_vars(const Def* expr) {
        /* if expr is a mutable switch to the other free_vars */
        if (auto mut = expr->isa_mut()) return free_vars(mut);

        /* NOTE:
         * the expression is immutable. thus it doesn't introduce new vars.
         * this means that the free vars are the union of all vars reachable.
         * thus the union of the localvars of all reachable mutables.
         */
        auto& vars = expr->world().vars();
        auto fvs   = local_vars(expr);
        for (auto mut : local_muts(expr))
            fvs = vars.merge(fvs, free_vars(mut));

        return fvs;
    }

    Vars free_vars(Def* expr) {
        auto& st = get_state(expr);
        auto& w = expr->world();

        if (st.mark_ == 0) { /* use fixed-point iteration to recompute free vars */
            bool cyclic = false;
            /* first we need to do the initial run */
            w.next_run();
            free_vars<true>(cyclic, w.next_run(), expr);

            /* now we can iterate to solve for the fixed-point */
            for (bool todo = cyclic; todo;) {
                todo = false;
                free_vars<false>(todo, w.next_run(), expr);
            }
        }

        /* the free var set is stored in the state */
        return st.vars_;
    }

    template<bool init>
    Vars free_vars(bool& todo, uint32_t run, Def* expr) {
        /* NOTE: the following comment was copied from the <>Def::free_vars function */
        // If init == true : todo flag detects cycle.
        // If init == false: todo flag keeps track whether sth changed.
        //
        // Recursively recompute free vars. If
        // * mark_ == 0:        Invalid - need to recompute.
        // * mark_ == run - 1:  Previous iteration - need to recompute.
        // * mark_ == run:      We are running in cycles within the *current* iteration of our fixed-point loop.
        // * otherwise:         Valid!

        /* NOTE: this function was written based on <bool init>Def::free_vars() */
        auto& st = get_state(expr);
        if (st.mark_ != 0 && st.mark_ != run - 1) {
            if constexpr (init) todo |= st.mark_ == run;
            return st.vars_;
        }

        st.mark_ = run;

        auto fvs0  = st.vars_; // create copy to check against later, see if the set changed
        auto fvs   = fvs0;
        auto& w    = expr->world();
        auto& vars = w.vars();
        auto& muts = w.muts();

        for (auto op : expr->deps()) {
            /* we start by adding all from dependencies reachable vars */
            if constexpr (init) fvs = vars.merge(fvs, local_vars(op));

            /* then add the free vars of every from op reachable mutable */
            for (auto mut : local_muts(op)) {
                if constexpr (init) {
                    /* add expr to list of users from mut */
                    auto& st_mut = get_state(mut);
                    st_mut.muts_ = muts.insert(st_mut.muts_, expr);
                }

                /* now we add the free vars of the dependencies */
                fvs = vars.merge(fvs, free_vars<init>(todo, run, mut));
            }
        }

        if (auto var = expr->has_var()) fvs = vars.erase(fvs, var); // FV(lam x.e) = FV(e) \ {x}

        /* did smt change? */
        if constexpr (!init) todo |= fvs0 != fvs;

        /* update free var cache of expr */
        return st.vars_ = fvs;
    }

    void print_state(const Def* expr) {
        if (!state_.contains(expr)) {
            std::cout << expr << " not in state\n";
            return;
        }
        auto& st = get_state(expr);
        std::cout << "vars : " << st.vars_ << "\n"
                  << "muts : " << st.muts_
                  << std::endl;
    }

private:
    struct FVState {
        u32 mark_  = 0;
        Vars vars_ = Vars(); // Mutable: local vars; Immutable: free vars.
        Muts muts_ = Muts(); // Immutable: local_muts; Mutable: users;
    };

    DefMap<std::unique_ptr<FVState>> state_;

    FVState& get_state(const Def* expr) {
        bool exists = state_.contains(expr);

        /* TODO for debuging I'm currently using the exit label with goto. remove that paradime if no longer needed */

        if(!exists) state_.emplace(expr, std::make_unique<FVState>());
        auto& st = *state_.at(expr); /* make sure that the entry exists */

        // state already exists
        if (exists) goto exit;

        /* now we have to calculate the local vars : the set of vars reachable by following immutable deps */
        /* and we have to calculate the local muts : the set of muts reachable by following immutable deps */

        /* according to some comments this is per definition right */
        if (auto var = expr->isa<Var>()) {
            st.vars_ = Vars(var);
        } else {
            auto& world = expr->world();
            auto& vars = world.vars();
            auto& muts = world.muts();

            /* NOTE: QUESTION: I'm not using deps() because that only includes ops if they are set. (is this limitation ok?) */
            if (auto type = expr->type()) {
                st.vars_ = vars.merge(st.vars_, local_vars(type));
                st.muts_ = muts.merge(st.muts_, local_muts(type));
            }

            for (auto op : expr->ops()) {
                st.vars_ = vars.merge(st.vars_, local_vars(op));
                st.muts_ = muts.merge(st.muts_, local_muts(op));
            }
        }

exit:
        return st;
    }

    /// Var%s reachable by following *immutable* deps().
    /// @note `var->local_vars()` is by definition the set `{ var }`.
    Vars local_vars(const Def* expr) {
        return expr->is_mutable() ? Vars() : get_state(expr).vars_;
    }

    /// Mutables reachable by following *immutable* deps(); `mut->local_muts()` is by definition the set `{ mut }`.
    Muts local_muts(const Def* expr) {
        if (auto mut = expr->isa_mut()) return Muts(mut);
        return get_state(expr).muts_;
    }
};





void foo(const Def* expr, DefSet &done, FVAnalysis &ana) {
    if (!done.emplace(expr).second) return;

    std::cout << "\ncomparing free var anas for " << expr << std::endl;
    std::cout << "old free vars :" << expr->free_vars() << std::endl;
    std::cout << "new free vars : " << ana.free_vars(expr) << std::endl;

    for (auto def : expr->deps())
        foo(def, done, ana);
}

int main(int, char**) {
    auto driver = Driver("test01");
    auto& w     = driver.world();
    driver.log().set(&std::cerr).set(Log::Level::Debug);
    ast::load_plugins(w, View<std::string>{"core", "clos2"});

    auto i32  = w.type_i32();
    auto one  = w.lit_i32(1);
    auto zero = w.lit_i32(0);

    auto count    = w.mut_fun(i32, i32)->set("count");
    auto [n, ret] = count->vars<2>();
    n             = n->set("n");
    ret           = ret->set("ret");
    auto loop     = w.mut_con({i32, i32})->set("loop");
    auto [i, acc] = loop->vars<2>();
    i             = i->set("i");
    acc           = acc->set("acc");
    auto body     = w.mut_con(Defs{})->set("body");
    auto next     = w.call(core::wrap::add, core::Mode::none, Defs{i, one});
    auto sum      = w.call(core::wrap::add, core::Mode::none, Defs{acc, i});
    body->app(false, loop, Defs{next, sum});
    auto exit = w.mut_con(Defs{})->set("exit");
    exit->app(false, ret, acc);
    auto cond     = w.call(core::icmp::ul, Defs{i, n});
    auto selected = w.select(cond, body, exit);
    loop->app(false, selected, Defs{});
    count->app(false, loop, Defs{zero, zero});

    FVAnalysis ana{};
    DefSet done_{};

    foo(body, done_, ana);

    count->dot("test.dot");

    return EXIT_SUCCESS;
}
