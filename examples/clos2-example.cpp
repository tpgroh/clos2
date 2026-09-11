#include <cstdlib>

#include <sstream>

#include "mim/driver.h"
#include "mim/phase.h"
#include "mim/plugin.h"

#include "mim/ast/ast.h"
#include "mim/ast/parser.h"
#include "mim/phase/optimize.h"

using namespace mim;

auto constexpr prog = R"(
plugin core;
plugin clos2;
plugin compile;

// define a custom pipeline for optimization
lam extern _compile(): %compile.Phase =
	let optimize =
        // fixed-point iteration off by default; enable with `-X compile:aggr`
        %compile.phases (%compile.aggr ff) (
            %compile.scalarize,
            %compile.phases tt (
                %compile.beta_red,
                %compile.eta_conv,
            ),
            %compile.named "%mem.seo",
            %compile.static_arg_opt,
        );

    %compile.phases ff (
		optimize,
		%compile.branch_normalize,
        %compile.named "%clos2.clos_conv",
    );

fun extern make_adder (n : I32) : I32->I32 =
    lam add (x:I32) : I32 = %core.wrap.add 0 (x,n);
    return add;

fun extern foo () : I32 =
    ret add2 = make_adder $ 2I32;
    ret add3 = make_adder $ 3I32;
    let a = add2 0I32;
    let b = add3 0I32;
    let sum = %core.wrap.add 0 (a,b);
    return sum;

/*
fun extern count (n : I32) : I32 =
    loop (0I32, 0I32)
    where
        con loop (i acc : I32) =
            let cond = %core.icmp.ul (i, n);
            %core.select (cond, body, exit) ()
            where
                con body () =
                    let next = %core.wrap.add 0 (i, 1I32);
                    let sum = %core.wrap.add 0 (acc, i);
                    loop (next, sum);
                con exit () =
                    return acc;
            end;
    end;
*/
)";

/* what I think the result should be

lam extern procedure (n:I32) (x:I32) : I32 = %core.warp.add 0 (n,x);

lam extern make_adder (n:I32) (return : [T:*, T, T->[Sigma T_2:*, T, T->I32->I32]]): =
    return#2_3 return#1_3 [I32, n, procedure]

fun extern foo () : I32 =
    ret add2 = make_adder $ 2I32;
    ret add3 = make_adder $ 3I32;
    let a = add2#2_3 add2#1_3 0I32;
    let b = add3#2_3 add3#1_3 0I32;
    let sum = %core.wrap.add 0 (a,b);
    return sum;

 */

int main(int, char**) {
    auto driver = Driver();
    driver.log().set(&std::cerr).set(fe::Log::Level::Debug);
    auto& world = driver.world();
    auto ast    = mim::ast::AST(world);
    auto parser = mim::ast::Parser(ast);
    auto is     = std::istringstream(prog);

    auto mod = parser.import(is, "prog.mim");
    assert(mod);
    mod->compile(ast);

    world.dot("before.dot", {.follow_types = true});
    world.dump();

    optimize(world);

    world.dot("after.dot", {.follow_types = true});
    world.dump();

    return EXIT_SUCCESS;
}
