#include "mim/plug/clos2/phase/absclos_to_sjlj.h"

#include "mim/plug/core/core.h"
#include "mim/plug/mem/mem.h"
#include "mim/tuple.h"

using namespace mim;
using namespace mim::plug;
using namespace mim::plug::clos2;

const Def* AbsClosSjLj::rewrite_body2setjmp(Lam* old_lam) {
    log().d("body2setjmp {}", old_lam);

    auto& w = new_world();

    log().d("test1");
    auto new_lam = w.mut_lam(rewrite(old_lam->type())->as<Pi>());
    map(old_lam, new_lam);
    log().d("test1");

    push();
    bind_old(old_lam->has_var());
    bind_new(new_lam->var()->isa<Var>());

    log().d("test1");

    // first job; find out which type we have to return
    auto m0 = mem::mem_var(new_lam);
    assert(m0);
    log().d("test1");
    assert(new_lam->ret_var() && "new_lam must have a return continuation");
    auto ret_dom = core::strip_mem_ty(new_lam->ret_dom());
    
    log().d("test1");

    bool skip_ret_pointer = ret_dom == old_world().sigma();

    // only allocate the return buffer if needed.
    const Def* tmp_m = nullptr;
    const Def* ret_ptr = nullptr;
    if (!skip_ret_pointer) {
        auto tmp = mem::op_alloc(ret_dom, m0);
        tmp_m = tmp->proj(2,0);
        ret_ptr = tmp->proj(2,1);
    }

    log().d("test1");

    auto [tmp2_m, jmp_buf] = w.call<alloc_jmpbuf>(skip_ret_pointer ? m0 : tmp_m)->projs<2>();
    auto [new_m, tag] = w.call<setjmp>(Defs{tmp2_m, jmp_buf})->projs<2>();
    
    log().d("test2");

    // create the return body
    auto return_body = w.mut_con(w.sigma());
    if (skip_ret_pointer)
        return_body->set(true, w.call(new_lam->ret_var(), new_m));
    else {
        auto [ret_new_m, ret_value] = w.call<mem::load>(Defs{new_m, ret_ptr})->projs<2>();
        auto ret_actual_value = Prod::cat(true, 1, ret_value->num_projs(), ret_new_m, ret_value);
        return_body->set(true, w.app(new_lam->ret_var(), ret_actual_value));
    }
    
    log().d("test3");

    // create the actual body
    map(mem::mem_var(old_lam), new_m);
    map(old_lam->ret_var(), w.tuple(skip_ret_pointer ? Defs{jmp_buf} : Defs{jmp_buf, ret_ptr}));

    auto body = w.mut_con(w.sigma());
    body->set(rewrite(old_lam->filter()), rewrite(old_lam->body()));
    
    log().d("test4");

    // switch on tag
    auto cond = w.call(core::icmp::e, Defs{tag, w.lit_i32(0)});
    auto swtch = w.select(cond, body, return_body);

    // now set stub
    new_lam->set(rewrite(old_lam->filter()), w.app(swtch, w.tuple()));

    pop();
    return new_lam;
}
