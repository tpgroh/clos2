#include <mim/driver.h>

#include <mim/ast/parser.h>
#include <mim/phase/optimize.h>
#include <mim/util/sys.h>

#include <mim/plug/mem/mem.h>

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
        auto w = &expr->world();

        if (st.mark_ == 0) { /* use fixed-point iteration to recompute free vars */
            bool cyclic = false;
            /* first we need to do the initial run */
            w->next_run();
            free_vars<true>(cyclic, w->next_run(), expr);

            /* now we can iterate to solve for the fixed-point */
            for (bool todo = cyclic; todo;) {
                todo = false;
                free_vars<false>(todo, w->next_run(), expr);
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
            for (auto mut : op->local_muts()) {
                /* in the first run we make sure that exp is added to the local_muts of the dependency */
                if constexpr (init) {
                    auto& st = get_state(mut);
                    st.muts_ = muts.insert(st.muts_, expr);
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

    FVState& get_state(const Def* expr) {
        // state already exists
        if (state_.contains(expr)) return state_[expr];

        // create empty state
        auto& st = state_[expr];

        /* if expr is a var then local_vars is just {var}
         * NOTE: that Var means that expr is mutable. thus muts_ is just {expr}
         * which is already returned by local_muts() because it is mutable
         * */
        if (auto var = expr->isa<Var>()) {
            st.vars_ = Vars(var);
            return st;
        }

        auto& world = expr->world();
        auto& vars = world.vars();
        auto& muts = world.muts();

        if (auto type = expr->type()) {
            st.vars_ = vars.merge(st.vars_, local_vars(type));
            st.muts_ = muts.merge(st.muts_, local_muts(type));
        }

        for (auto op : expr->ops()) {
            st.vars_ = vars.merge(st.vars_, local_vars(op));
            st.muts_ = muts.merge(st.muts_, local_muts(op));
        }

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

    DefMap<FVState> state_;
};






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

    FVAnalysis fvana{};
    auto e = body;

    std::cout << "\n\ncomparing free var anas for " << e << "\n\n";

    std::cout << "libmim's free var ana" << std::endl;
    std::cout << "free vars :" << e->free_vars() << std::endl;
    std::cout << "muts : " << e->users() << std::endl;

    std::cout << "\n\nmy free var ana" << std::endl;
    std::cout << "free vars : " << fvana.free_vars(e) << std::endl;
    fvana.print_state(e);

    count->dot("test.dot");

    return EXIT_SUCCESS;
}
