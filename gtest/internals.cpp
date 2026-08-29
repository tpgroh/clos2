#include <gtest/gtest.h>

#include <mim/plug/core/core.h>

#include "mim/driver.h"

#include "mim/ast/ast.h"

#include "mim/plug/clos2/fv.h"
#include "mim/plug/core/autogen.h"

using namespace mim;
using namespace mim::plug;

// TODO: remove this
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

// TODO: remove this
void print(const Def* def) {
    DefSet done{};
    clos2::FVAnalysis ana{};

    print(def, done, ana);
}

// a simple to test the very basics
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

// simple test to check if the extractions of a var will be unpeeled into including the var if the union of free vars
// included all extractions of it
TEST(internal_fv, simple_peel_off) {
    Driver driver;
    auto& w = driver.world();
    ast::load_plugin(w, "core");

    auto foo    = w.mut_lam(w.arr(2, w.type_i32()), w.type_i32());
    auto [a, b] = foo->vars<2>();
    auto bar    = w.mut_lam(w.type_i32(), w.type_i32());
    auto x      = bar->var();
    bar->set(false, w.call(core::wrap::add, core::Mode::none, Defs{x, b}));
    foo->set(false, w.app(bar, a));

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

// test if dangling extractions get removed correctly
TEST(internal_fv, trans_peel_off) {
    Driver driver;
    auto& w = driver.world();
    ast::load_plugin(w, "core");

    auto foo    = w.mut_lam({w.type_bool(), w.arr(2, w.arr(2, w.type_i32()))}, w.type_i32());
    auto [a, b] = foo->var(2, 1)->projs<2>();
    auto [u, v] = a->projs<2>();
    auto [x, y] = b->projs<2>();

    auto sum2 = w.mut_lam({w.type_i32(), w.type_i32()}, w.type_i32());
    {
        auto [x, y] = sum2->vars<2>();
        sum2->set(false, w.call(core::wrap::add, core::Mode::none, Defs{x, y}));
    }

    auto sum3 = w.mut_lam(w.arr(3, w.type_i32()), w.type_i32());
    {
        auto [x, y, z] = sum3->vars<3>();
        sum3->set(false, w.app(sum2, {w.app(sum2, {x, y}), z}));
    }

    auto f1 = w.app(sum3, {x, u, y}); // FV is {b,u}
    auto f2 = w.app(sum2, {u, v});    // FV is {a}
    auto f3 = w.app(sum2, {f1, f2});  // FV is {foo->var(2,1)} I dont want u to be included!

    foo->set(false, f3);

    clos2::FVAnalysis ana{};

    auto fv = ana.free_vars(f1);
    ASSERT_EQ(fv.size(), 2);
    ASSERT_TRUE(fv.contains(b));
    ASSERT_TRUE(fv.contains(u));

    fv = ana.free_vars(f2);
    ASSERT_EQ(fv.size(), 1);
    ASSERT_TRUE(fv.contains(a));

    fv = ana.free_vars(f3);
    ASSERT_EQ(fv.size(), 1);
    ASSERT_TRUE(fv.contains(foo->var(2, 1)));
}

// tests that it doesn't unpeel if it is not extracting directly from a Var with an arity higher or equal to the
// scalarize_threshold
TEST(internal_fv, threshold1) {
    Driver driver;
    auto& w = driver.world();
    ast::load_plugin(w, "core");

    auto foo = w.mut_lam(w.arr(w.flags().scalarize_threshold, w.arr(2, w.type_bool())), w.type_bool());
    auto v1  = foo->var(0)->proj(0);
    auto v2  = foo->var(1)->proj(0);
    auto b   = w.call(core::bit2::xor_, core::Mode::none, Defs{v1, v2});
    for (size_t i = 2; i < w.flags().scalarize_threshold; i++) {
        v1 = b;
        v2 = foo->var(i)->proj(0);
        b  = w.call(core::bit2::xor_, core::Mode::none, Defs{v1, v2});
    }
    foo->set(false, b);

    clos2::FVAnalysis ana;
    auto fvs = ana.free_vars(foo->body());
    ASSERT_EQ(fvs.size(), w.flags().scalarize_threshold);
    for (size_t i = 0; i < w.flags().scalarize_threshold; i++)
        ASSERT_TRUE(fvs.contains(foo->var(i)->proj(0)));
}

// tests if it unpeels if extracting from a var which has an arity higher or equal to the scalarize_threshold
TEST(internal_fv, threshold2) {
    Driver driver;
    auto& w = driver.world();
    ast::load_plugin(w, "core");
    auto foo      = w.mut_lam(w.arr(w.flags().scalarize_threshold, w.arr(2, w.type_bool())), w.type_bool());
    auto [v1, v2] = foo->var(7)->projs<2>();
    foo->set(false, w.call(core::bit2::xor_, core::Mode::none, Defs{v1, v2}));

    clos2::FVAnalysis ana;
    auto fvs = ana.free_vars(foo->body());

    ASSERT_EQ(fvs.size(), 1);
    ASSERT_TRUE(fvs.contains(foo->var()));
}

TEST(internal_fv, extract_from_lam) {
    Driver driver;
    auto& w = driver.world();
    ast::load_plugin(w, "core");

    auto foo   = w.mut_lam(w.type_i32(), w.type_i32());
    auto v     = foo->var();
    auto inner = w.mut_lam(w.type_i32(), w.arr(2, w.type_i32()));
    inner->set(false, w.tuple({v, v}));
    auto bar = w.app(inner, w.lit_i32(1));
    foo->set(false, bar->proj(1));

    clos2::FVAnalysis ana;
    auto fvs = ana.free_vars(foo);
    ASSERT_EQ(fvs.size(), 0);

    fvs = ana.free_vars(foo->body());
    ASSERT_EQ(fvs.size(), 1);
    ASSERT_TRUE(fvs.contains(foo->var()));
}
