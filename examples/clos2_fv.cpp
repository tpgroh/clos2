#include "mim/driver.h"

#include "mim/ast/ast.h"

#include "mim/plug/clos2/fv.h"
#include "mim/plug/core/autogen.h"
#include "mim/plug/core/core.h"

using namespace mim;
using namespace mim::plug;
using namespace mim::plug::clos2;

/*
 * FIX: QUESTIONS
 * - good way to test libmim_clos2 internal functions?
 * - use world().next_run() or my own counter?
 * - do I need invalidate() ?
 *   - if so when I use Def::local_muts I'll have to invalidate this Analysis before def->invalidate() gets called
 */

void foo(const Def* expr, DefSet& done, FVAnalysis& ana) {
    if (!done.emplace(expr).second) return;

    std::cout << "\ncomparing free var anas for " << expr << std::endl;
    std::cout << "old free vars :" << expr->free_vars() << std::endl;
    std::cout << "new free vars : {";
    for (auto v : ana.free_vars(expr))
        std::cout << v << ", ";
    std::cout << "}" << std::endl;

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
