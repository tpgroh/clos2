#include <gtest/gtest.h>

#include <mim/plug/core/core.h>

#include "mim/driver.h"

#include "mim/ast/ast.h"

#include "mim/plug/clos2/fv.h"

using namespace mim;
using namespace mim::plug;

void foo(const Def* def, DefSet& done, clos2::FVAnalysis& ana) {
    if (!done.emplace(def).second) return;

    std::cout << "foo " << def << std::endl;
    auto fv = ana.free_vars(def);

    // print free vars
    std::cout << "free vars of  " << def << "  (clos2::FVAnalysis, Def::free_vars)\n{";
    for (auto def : fv)
        std::cout << def << ", ";
    std::cout << "}\n" << def->free_vars() << "\n\n";

    for (auto dep : def->deps())
        foo(dep, done, ana);
}

TEST(internal, fv) {
    Driver driver;
    auto& w = driver.world();
    ast::load_plugin(w, "core");

    auto outer = w.mut_lam({w.type_i32(), w.arr(4, w.type_i32())}, w.type_i32())->set("outer");
    outer->var()->set("argsOuter");
    auto [a, b] = outer->vars<2>();
    a->set("a");
    b->set("b");
    auto c = b->proj(4, 3)->set("c");

    auto inner = w.mut_lam(w.type_i32(), w.type_i32())->set("inner");
    auto x     = inner->var()->set("x");

    inner->set(false, w.call(core::wrap::add, core::Mode::none, Defs{c, x}));

    outer->set(false, w.app(inner, w.lit_i32(1)));

    outer->dot("tmp.dot");

    // for debugging and showcasing I first calculate and printout the results for every def
    auto ana  = clos2::FVAnalysis{};
    auto done = DefSet{};
    foo(outer, done, ana);

    // free vars of inner should be {c}
    auto fv = ana.free_vars(inner);
    ASSERT_EQ(fv.size(), 1);
    ASSERT_TRUE(fv.contains(c));

    // free vars of outer should be {}
    fv = ana.free_vars(outer);
    ASSERT_EQ(fv.size(), 0);

    // free vars of a should be {a}
    fv = ana.free_vars(a);
    ASSERT_EQ(fv.size(), 1);
    ASSERT_TRUE(fv.contains(a));
}

/*
TEST(internal, extracts) {
    Driver driver;
    auto& w = driver.world();
    ast::load_plugin(w, "core");

    auto outer = w.mut_lam({w.type_i32(), w.type_i32()}, w.type_i32())->set("outer");
    outer->var()->set("argsOuter");
    auto [a, b] = outer->vars<2>();
    a->set("a");
    b->set("b");

    auto inner = w.mut_lam(w.type_i32(), w.type_i32())->set("inner");
    auto x     = inner->var()->set("x");

    inner->set(false, w.call(core::wrap::add, core::Mode::none, Defs{a, x}));

    outer->set(false, w.app(inner, w.lit_i32(1)));

    // TOOD I should make sure that I've contructed what I wanted

    outer->dot("internal-extracts.dot");

    // for debugging and showcasing I first calcualte and printout the results for every def
    std::cout << "performing analysis" << std::endl;
    auto ana = clos2::EXAnalysis{inner};

    ana.printState();

    ASSERT_TRUE(true); // TODO: write test asserts
}
*/
