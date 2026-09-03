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
    %compile.phases ff (
        %compile.named "%clos2.clos_conv",
    );

// define a function for testing closure conversion on
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
)";

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

    world.dot("before.dot");
    world.dump();

    optimize(world);

    world.dot("after.dot");
    world.dump();

    return EXIT_SUCCESS;
}
