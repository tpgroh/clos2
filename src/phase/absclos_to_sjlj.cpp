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

    auto new_lam = w.mut_lam(rewrite(old_lam->type())->as<Pi>());
    map(old_lam, new_lam);

    push();
    bind_old(old_lam->has_var());
    bind_new(new_lam->var()->isa<Var>());

    // first job; find out which type we have to return
    auto m0 = mem::mem_var(new_lam);
    assert(m0);
    assert(new_lam->ret_var() && "new_lam must have a return continuation");
    auto ret_dom = core::strip_mem_ty(new_lam->ret_dom());
    
    bool skip_ret_pointer = ret_dom == old_world().sigma();

    // only allocate the return buffer if needed.
    const Def* tmp_m = nullptr;
    const Def* ret_ptr = nullptr;
    if (!skip_ret_pointer) {
        auto tmp = mem::op_alloc(ret_dom, m0);
        tmp_m = tmp->proj(2,0);
        ret_ptr = tmp->proj(2,1);
        tmp_m->set(m0->dbg_key());
        ret_ptr->set("payload");
    }

    auto [tmp2_m, jmp_buf] = w.call<alloc_jmpbuf>(skip_ret_pointer ? m0 : tmp_m)->projs<2>();
    auto [new_m, tag] = w.call<setjmp>(Defs{tmp2_m, jmp_buf})->projs<2>();

    tmp2_m->set(m0->dbg_key());
    jmp_buf->set("jmpbuf");
    new_m->set(m0->dbg_key());
    tag->set("setjmptag");


    // create the return body
    auto return_body = w.mut_con(w.sigma());
    if (skip_ret_pointer)
        return_body->set(true, w.call(new_lam->ret_var(), new_m));
    else {
        auto [ret_new_m, ret_value] = w.call<mem::load>(Defs{new_m, ret_ptr})->projs<2>();
        auto ret_actual_value = Prod::cat(true, 1, ret_value->num_projs(), ret_new_m, ret_value);
        return_body->set(true, w.app(new_lam->ret_var(), ret_actual_value));
    }
    
    // create the actual body
    map(mem::mem_var(old_lam), new_m);
    map(old_lam->ret_var(), w.tuple(skip_ret_pointer ? Defs{jmp_buf} : Defs{jmp_buf, ret_ptr}));

    auto body = w.mut_con(w.sigma());
    body->set(rewrite(old_lam->filter()), rewrite(old_lam->body()));

    // switch on tag
    auto cond = w.call(core::icmp::e, Defs{tag, w.lit_i32(0)});
    auto swtch = w.select(cond, body, return_body);

    // now set stub
    new_lam->set(rewrite(old_lam->filter()), w.app(swtch, w.tuple()));

    pop();
    return new_lam;
}


const Def* AbsClosSjLj::rewrite_hoist_capretcon(size_t i, const Def* old_op, size_t &idx_i, fe::Vector<nat_t>& idx) {
    auto& w = new_world();

    if (idx[idx_i] != i) return rewrite(old_op);
    idx_i++;

    auto cn = Pi::isa_cn(old_op);
    assert(cn && "return continuations in hoistup env param should have type Cn");

    auto old_rettype = cn->dom();
    auto new_rettype = core::strip_mem_ty(rewrite(old_rettype));

    if (new_rettype == w.sigma()) return w.annex<JmpBufPtr>();

    return w.sigma({w.call<mem::Ptr0>(new_rettype), w.annex<JmpBufPtr>()});
}

const Def* AbsClosSjLj::rewrite_hoist(Lam* old_proc, fe::Vector<nat_t>& idx) {
    auto& w = new_world();
    auto dom = old_proc->dom();
    auto n = old_proc->num_doms();

    log().d("rewrite hoist {} with idx {}", old_proc, idx);

    // TODO handle case n == 1

    // rebuild the environment sigma
    if (auto tel = dom->isa_mut<Sigma>()) {
        auto new_sig = w.mut_sigma(rewrite(tel->type()), n);
        push();
        bind_old(tel->has_var());
        bind_new(new_sig->var()->isa<Var>());
        if (auto v = tel->has_var()) map(v, new_sig->var());
        size_t idx_i = 0;
        for (size_t i = 0; i < n; i++)
            new_sig->set(i, rewrite_hoist_capretcon(i, tel->op(i), idx_i, idx));
        pop();
        log().d("rewrote {}", tel);
        log().d("to      {}", new_sig);
    } else {
        auto old_sig = dom->isa<Sigma>();
        assert(old_sig && "the domain of a procedure should be a sigma");
        size_t idx_i = 0;
        auto new_sig = w.sigma(DefVec{n, [&](auto i){ return rewrite_hoist_capretcon(i, old_sig->op(i), idx_i, idx); }});
        log().d("rewrote {}", old_sig);
        log().d("to      {}", new_sig);
    }

    assert(0 && "ok");
    return nullptr;
}

const Def* AbsClosSjLj::rewrite_environment(const Def* old_env, fe::Vector<nat_t>& idx) {
    log().d("rewrite environment {}", old_env);

    auto n = old_env->num_projs();

    if (n <= 1) {
        if (Axm::isa(anno::captured_ret, old_env)) idx.push_back(0);
    } else
        for (size_t i = 0; i < n; i++)
            if (Axm::isa(anno::captured_ret, old_env->proj(n, i))) idx.push_back(i);

    return rewrite(old_env);
    
    // TODO: rewrite the environement
    // for this I have to rewrite

/*
    auto& w = new_world();
    auto n = old_env->num_projs();

    // if the environment is a single thing it is not a tuple
    if (n <= 1) return rewrite(old_env);

    auto ops = rewrite(old_env->ops());
    log().d("ops {}", ops);
    return w.tuple(ops);
*/
}

