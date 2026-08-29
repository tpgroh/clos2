#include <gtest/gtest.h>

#include <mim/plug/core/core.h>

#include "mim/driver.h"

#include "mim/ast/ast.h"

#include "mim/plug/clos2/fv.h"

using namespace mim;
using namespace mim::plug;

void print(const Def* def, DefSet& done, clos2::FVAnalysis& ana) {
    if (!done.emplace(def).second) return;

    std::cout << "foo " << def << std::endl;
    auto fv = ana.free_vars(def);

    // print free vars
    std::cout << "free vars of  " << def << "  (clos2::FVAnalysis, Def::free_vars)\n{";
    for (auto def : fv)
        std::cout << def << ", ";
    std::cout << "}\n" << def->free_vars() << "\n\n";

    for (auto dep : def->deps())
        print(dep, done, ana);
}

void print(const Def* def) {
    DefSet done{};
    clos2::FVAnalysis ana{};

    print(def, done, ana);
}

Lam* build_poly_id(World& w) {
    // construct type
    auto pi = w.mut_pi(w.type<1>(), true)->set_dom(w.type());
    auto pT = pi->var()->set("T");
    pi->set_codom(w.pi(pT, pT));

    // construct lambda
    auto lamT = w.mut_lam(pi);
    auto lT   = lamT->var()->set("T");

    auto lamx = w.mut_lam(w.pi(lT, lT));
    auto x    = lamx->var()->set("x");

    // NOTE: I set the filter to false because I don't want this to just be partially evaluated while constructing
    lamx->set(false, x);
    lamT->set(false, lamx);

    return lamT;
}

TEST(internal_fv, simple) {
    Driver driver;
    auto& w = driver.world();
    ast::load_plugin(w, "core");

    // lam foo (a,b,c,d : I32) : I32 = bar a
    // where lam bar (x:I32) = core::wrap::add core::Mode::none x c
    auto foo          = w.mut_lam(w.arr(4, w.type_i32()), w.type_i32());
    auto [a, b, c, d] = foo->vars<4>();
    auto bar          = w.mut_lam(w.type_i32(), w.type_i32());
    auto x            = bar->var();
    bar->set(false, w.call(core::wrap::add, core::Mode::none, Defs{x, c}));
    foo->set(false, w.app(bar, a));

    clos2::FVAnalysis ana{};

    auto fv = ana.free_vars(foo->body());
    ASSERT_EQ(fv.size(), 2);
    ASSERT_TRUE(fv.contains(a));
    ASSERT_TRUE(fv.contains(c));

    fv = ana.free_vars(foo);
    ASSERT_EQ(fv.size(), 0);

    fv = ana.free_vars(bar);
    ASSERT_EQ(fv.size(), 1);
    ASSERT_TRUE(fv.contains(c));

    fv = ana.free_vars(bar->body());
    ASSERT_EQ(fv.size(), 2);
    ASSERT_TRUE(fv.contains(x));
    ASSERT_TRUE(fv.contains(c));
}

TEST(internal_fv, simple_peel_off) {
    Driver driver;
    auto& w = driver.world();
    ast::load_plugin(w, "core");

    // lam foo (a,b,c,d : I32) : I32 = bar a
    // where lam bar (x:I32) = core::wrap::add core::Mode::none x c
    auto foo    = w.mut_lam(w.arr(2, w.type_i32()), w.type_i32())->set("foo");
    auto [a, b] = foo->vars<2>();
    a->set("a");
    b->set("b");
    foo->var()->set("foovar");
    auto bar = w.mut_lam(w.type_i32(), w.type_i32())->set("bar");
    auto x   = bar->var()->set("x");
    bar->set(false, w.call(core::wrap::add, core::Mode::none, Defs{x, b}));
    foo->set(false, w.app(bar, a));
    foo->body()->set("foobody");
    bar->body()->set("barbody");

    print(foo);

    clos2::FVAnalysis ana{};

    auto fv = ana.free_vars(foo->body());
    ASSERT_EQ(fv.size(), 1);
    ASSERT_TRUE(fv.contains(foo->var()));

    fv = ana.free_vars(foo);
    ASSERT_EQ(fv.size(), 0);

    fv = ana.free_vars(bar);
    ASSERT_EQ(fv.size(), 1);
    ASSERT_TRUE(fv.contains(b));

    fv = ana.free_vars(bar->body());
    ASSERT_EQ(fv.size(), 2);
    ASSERT_TRUE(fv.contains(x));
    ASSERT_TRUE(fv.contains(b));
}
