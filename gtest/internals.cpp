#include <gtest/gtest.h>

#include <mim/plug/core/core.h>

#include "mim/driver.h"

#include "mim/ast/ast.h"

#include "mim/plug/clos2/fv.h"

using namespace mim;
using namespace mim::plug;

TEST(internal, fv) {
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

    outer->dot("tmp.dot");

    auto ana = clos2::FVAnalysis{};

    auto fv = ana.free_vars(inner);

    // print free vars
    std::cout << "free vars of inner\n";
    for (auto def : fv)
        std::cout << def << ", ";
    std::cout << "\nlibmim found free vars\n" << inner->free_vars() << std::endl;

    ASSERT_EQ(fv.size(), 1);
    ASSERT_TRUE(fv.contains(a));
}
