#include <doctest/doctest.h>

#include <mim/plug/core/core.h>

#include "mim/driver.h"

#include "mim/ast/ast.h"

#include "mim/plug/clos2/fv.h"
#include "mim/plug/core/autogen.h"

using namespace mim;
using namespace mim::plug;

// a simple to test the very basics
TEST_CASE("clos2.fvanalysis-simple") {
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
    CHECK(fv.size() == 2);
    CHECK(fv.contains(a));
    CHECK(fv.contains(c));

    fv = ana.free_vars(foo);
    CHECK(fv.size() == 0);

    fv = ana.free_vars(bar);
    CHECK(fv.size() == 1);
    CHECK(fv.contains(c));

    fv = ana.free_vars(bar->body());
    CHECK(fv.size() == 2);
    CHECK(fv.contains(x));
    CHECK(fv.contains(c));
}

// simple test to check if the extractions of a var will be unpeeled into including the var if the union of free vars
// included all extractions of it
TEST_CASE("clos2.internals_simple_peel_off") {
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
    CHECK(fv.size() == 1);
    CHECK(fv.contains(foo->var()));

    fv = ana.free_vars(foo);
    CHECK(fv.size() == 0);

    fv = ana.free_vars(bar);
    CHECK(fv.size() == 1);
    CHECK(fv.contains(b));

    fv = ana.free_vars(bar->body());
    CHECK(fv.size() == 2);
    CHECK(fv.contains(x));
    CHECK(fv.contains(b));
}

// test if dangling extractions get removed correctly
TEST_CASE("clos2.internals_trans_peel_off") {
    Driver driver;
    auto& w = driver.world();
    ast::load_plugin(w, "core");

    auto foo    = w.mut_lam({w.type_bool(), w.arr(2, w.sigma({w.type_i32(), w.type_i32(), w.type_nat()}))}, w.type_i32());
    auto [a, b] = foo->var(2, 1)->projs<2>();
    auto [u, v, q] = a->projs<3>();
    auto [x, y, z] = b->projs<3>();

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

    auto f1 = w.app(sum3, {x, y, w.app(sum2, {u, w.call<core::bitcast>(w.type_i32(), z)})}); // FV is {b,u}
    auto f2 = w.app(sum3, {u, v, w.call<core::bitcast>(w.type_i32(), q)});    // FV is {a}
    auto f3 = w.app(sum2, {f1, f2});  // FV is {foo->var(2,1)} I dont want `u` to be included!

    foo->set(false, f3);

    clos2::FVAnalysis ana{};

    auto fv = ana.free_vars(f1);
    CHECK(fv.size() == 2);
    CHECK(fv.contains(b));
    CHECK(fv.contains(u));

    fv = ana.free_vars(f2);
    CHECK(fv.size() == 1);
    CHECK(fv.contains(a));

    fv = ana.free_vars(f3);
    CHECK(fv.size() == 1);
    CHECK(fv.contains(foo->var(2, 1)));
}

// tests that it doesn't unpeel if it is not extracting directly from a Var with an arity higher or equal to the
// scalarize_threshold
TEST_CASE("clos2.internals_threshold1") {
    Driver driver;
    auto& w = driver.world();
    ast::load_plugin(w, "core");

    auto foo = w.mut_lam(w.arr(w.flags().scalarize_threshold, w.sigma({w.type_bool(), w.type_nat()})), w.type_bool());
    auto v1  = foo->var(w.flags().scalarize_threshold, 0)->proj(2, 0);
    auto v2  = foo->var(w.flags().scalarize_threshold, 1)->proj(2, 0);
    auto b   = w.call(core::bit2::xor_, core::Mode::none, Defs{v1, v2});
    for (size_t i = 2; i < w.flags().scalarize_threshold; i++) {
        v1 = b;
        v2 = foo->var(w.flags().scalarize_threshold, i)->proj(2, 0);
        b  = w.call(core::bit2::xor_, core::Mode::none, Defs{v1, v2});
    }
    foo->set(false, b);

    clos2::FVAnalysis ana;
    auto fvs = ana.free_vars(foo->body());
    CHECK(fvs.size() == w.flags().scalarize_threshold);
    for (size_t i = 0; i < w.flags().scalarize_threshold; i++)
        CHECK(fvs.contains(foo->var(w.flags().scalarize_threshold, i)->proj(2, 0)));
}

// tests if it unpeels if extracting from a var which has an arity higher or equal to the scalarize_threshold
TEST_CASE("clos2.internals_threshold2") {
    Driver driver;
    auto& w = driver.world();
    ast::load_plugin(w, "core");
    auto foo      = w.mut_lam(w.arr(w.flags().scalarize_threshold, w.arr(2, w.type_bool())), w.type_bool());
    auto [v1, v2] = foo->var(w.flags().scalarize_threshold, 7)->projs<2>();
    foo->set(false, w.call(core::bit2::xor_, core::Mode::none, Defs{v1, v2}));

    clos2::FVAnalysis ana;
    auto fvs = ana.free_vars(foo->body());

    CHECK(fvs.size() == 1);
    CHECK(fvs.contains(foo->var()));
}

TEST_CASE("clos2.internals_extract_from_lam") {
    Driver driver;
    auto& w = driver.world();
    ast::load_plugin(w, "core");

    auto foo   = w.mut_lam(w.type_i32(), w.type_i32());
    auto v     = foo->var();
    auto inner = w.mut_lam(w.type_i32(), w.arr(2, w.type_i32()));
    inner->set(false, w.tuple({v, v}));
    auto bar = w.app(inner, w.lit_i32(1));
    foo->set(false, bar->proj(bar->num_projs(), 1));

    clos2::FVAnalysis ana;
    auto fvs = ana.free_vars(foo);
    CHECK(fvs.size() == 0);

    fvs = ana.free_vars(foo->body());
    CHECK(fvs.size() == 1);
    CHECK(fvs.contains(foo->var()));
}

// regression test: cyclic mutables must not cache half computed free var sets
// lam outer (a, b : I32) : I32 = up a
// where lam up (x : I32) : I32 = h (in x)
//       lam in (y : I32) : I32 = up y   <- cycle up -> in -> up
//       lam h  (z : I32) : I32 = z + b  <- b only reachable via a nested mutable of up
static void check_cyclic_fvs(bool up_first) {
    Driver driver;
    auto& w = driver.world();
    ast::load_plugin(w, "core");

    auto outer  = w.mut_lam(w.arr(2, w.type_i32()), w.type_i32());
    auto [a, b] = outer->vars<2>();
    auto in     = w.mut_lam(w.type_i32(), w.type_i32()); // created first so it is visited before h
    auto h      = w.mut_lam(w.type_i32(), w.type_i32());
    auto up     = w.mut_lam(w.type_i32(), w.type_i32());
    h->set(false, w.call(core::wrap::add, core::Mode::none, Defs{h->var(), b}));
    up->set(false, w.app(h, w.app(in, up->var())));
    in->set(false, w.app(up, in->var()));
    outer->set(false, w.app(up, a));

    clos2::FVAnalysis ana;
    if (up_first) {
        auto fvs = ana.free_vars(up);
        CHECK(fvs.size() == 1);
        CHECK(fvs.contains(b));
    }

    auto fvs = ana.free_vars(in);
    CHECK(fvs.size() == 1);
    CHECK(fvs.contains(b));
    CHECK(!fvs.contains(up->var()));

    fvs = ana.free_vars(up);
    CHECK(fvs.size() == 1);
    CHECK(fvs.contains(b));

    fvs = ana.free_vars(outer);
    CHECK(fvs.size() == 0);
}

TEST_CASE("clos2.internals_cyclic_fresh") { check_cyclic_fvs(false); }
TEST_CASE("clos2.internals_cyclic_cached") { check_cyclic_fvs(true); }

// regression test: a common ancestor that reaches *both* members of a cycle directly.
// The existing cyclic test enters the cycle through a single member, which always worked:
// the entry point of a traversal is exact. Here `outer` asks for `e` and for `o`, and the
// one that was not the entry point must not be served from a half computed result.
// lam outer (a, b : I32) : I32 = e a + o a
// where lam e (x : I32) : I32 = o x + b
//       lam o (y : I32) : I32 = e y + b   <- cycle e -> o -> e, both reachable from outer
static void check_mutual_siblings(bool members_first) {
    Driver driver;
    auto& w = driver.world();
    ast::load_plugin(w, "core");

    auto outer  = w.mut_lam(w.arr(2, w.type_i32()), w.type_i32());
    auto [a, b] = outer->vars<2>();
    auto e      = w.mut_lam(w.type_i32(), w.type_i32());
    auto o      = w.mut_lam(w.type_i32(), w.type_i32());
    e->set(false, w.call(core::wrap::add, core::Mode::none, Defs{w.app(o, e->var()), b}));
    o->set(false, w.call(core::wrap::add, core::Mode::none, Defs{w.app(e, o->var()), b}));
    outer->set(false, w.call(core::wrap::add, core::Mode::none, Defs{w.app(e, a), w.app(o, a)}));

    clos2::FVAnalysis ana;

    // querying a member first makes it a traversal root, so it is cached as an exact result
    if (members_first) {
        auto fvs = ana.free_vars(e);
        CHECK(fvs.size() == 1);
        CHECK(fvs.contains(b));
    }

    auto fvs = ana.free_vars(outer);
    CHECK(fvs.size() == 0);
    CHECK(!fvs.contains(e->var())); // the bug: e's own var leaked out through o's cached entry
    CHECK(!fvs.contains(o->var()));

    fvs = ana.free_vars(e);
    CHECK(fvs.size() == 1);
    CHECK(fvs.contains(b));

    fvs = ana.free_vars(o);
    CHECK(fvs.size() == 1);
    CHECK(fvs.contains(b));
}

TEST_CASE("clos2.internals_mutual_siblings_fresh") { check_mutual_siblings(false); }
TEST_CASE("clos2.internals_mutual_siblings_cached") { check_mutual_siblings(true); }

// a three member cycle where only the last member mentions the free var, so every other member
// can only learn about it by going around the cycle. `outer` asks for all three, so two of them
// are recomputed as traversal roots after having been discarded.
// lam outer (a, b : I32) : I32 = f a + (g a + h a)
// where lam f (x : I32) : I32 = g x
//       lam g (x : I32) : I32 = h x
//       lam h (x : I32) : I32 = f x + b   <- only h mentions b
TEST_CASE("clos2.internals_cycle3_shared_ancestor") {
    Driver driver;
    auto& w = driver.world();
    ast::load_plugin(w, "core");

    auto outer  = w.mut_lam(w.arr(2, w.type_i32()), w.type_i32());
    auto [a, b] = outer->vars<2>();
    auto f      = w.mut_lam(w.type_i32(), w.type_i32());
    auto g      = w.mut_lam(w.type_i32(), w.type_i32());
    auto h      = w.mut_lam(w.type_i32(), w.type_i32());
    f->set(false, w.app(g, f->var()));
    g->set(false, w.app(h, g->var()));
    h->set(false, w.call(core::wrap::add, core::Mode::none, Defs{w.app(f, h->var()), b}));
    outer->set(false,
               w.call(core::wrap::add, core::Mode::none,
                      Defs{w.app(f, a), w.call(core::wrap::add, core::Mode::none, Defs{w.app(g, a), w.app(h, a)})}));

    clos2::FVAnalysis ana;

    auto fvs = ana.free_vars(outer);
    CHECK(fvs.size() == 0);

    for (auto mut : {f, g, h}) {
        fvs = ana.free_vars(mut);
        CHECK(fvs.size() == 1);
        CHECK(fvs.contains(b)); // reachable only around the cycle for f and g
        CHECK(!fvs.contains(f->var()));
        CHECK(!fvs.contains(g->var()));
        CHECK(!fvs.contains(h->var()));
    }
}
