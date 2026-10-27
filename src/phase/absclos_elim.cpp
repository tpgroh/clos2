#include "mim/plug/clos2/phase/absclos_elim.h"

#include "mim/def.h"
#include "mim/phase.h"

using namespace mim;
using namespace mim::plug;
using namespace mim::plug::clos2;

Lam* AbsClosElim::rewrite_procedure(Lam* old_proc) {
    log().d("rewrite procedure {}", old_proc);

    auto& w = new_world();
    auto old_lam = old_proc->body()->as<Lam>();

    log().d("proc {}:{}", old_proc, old_proc->type());
    log().d("lam {}:{}", old_lam, old_lam->type());

    if (auto it = procedures_.find(old_proc); it != procedures_.end()) {
        log().d("reuse procedure {}", old_proc, it->second);
        return it->second;
    }

    push();
    bind_old(old_proc->has_var());
    bind_old(old_lam->has_var());

    auto dom_type = rewrite(old_proc->type()->type()); // FIXME: there must be a nicer way for this
    log().d("dom_type {}", dom_type);
    auto dom = w.mut_sigma(dom_type, 2);
    bind_new(dom->var()->isa<Var>());
    // TODO: I actually dont want to name this sigma but it is currently required to dump something that is recursive
    dom->set("procedure_dom");
    auto env_type = rewrite(old_proc->dom());
    log().d("env type {}", env_type);
    dom->set(0, w.sigma({w.cn(dom), env_type}));
    dom->var(2, 0)->set("clos");
    // this map is the reason for the pop();push(); below
    if (auto v = old_proc->has_var()) map(v, dom->var(2, 0)->proj(2, 1));
    dom->set(1, rewrite(old_lam->dom()));
    dom->var(2, 1)->set("arg");
    pop();

    // we have to reset the scope because of the map above
    push();
    bind_old(old_proc->has_var());
    bind_old(old_lam->has_var());

    auto proc = w.mut_con(dom);
    proc->set(old_proc->dbg_key());
    bind_new(proc->var()->isa<Var>());

    // TODO: I should be able to use map for this. procedure is closed. thus it should fall through to the root scope
    // the lookup above could then be replaced by a lookup() call. this only changes where this is stored.
    procedures_[old_proc] = proc;

    log().d("new proc {}:{}", proc, proc->type());

    { // set syms for debugging
        auto [c, a] = proc->vars<2>();
        auto [p, e] = c->projs<2>();
        a->set("arg");
        p->set(old_proc->sym());
        e->set(old_proc->var()->sym());
        if (old_proc->num_vars() > 1) {
            auto num_vars = old_proc->num_vars();
            assert(e->num_projs() == num_vars && "the size of the environment should be preserved in rewriting the procedure");
            for (size_t i = 0; i < old_proc->num_vars(); i++)
                e->proj(num_vars, i)->set(old_proc->var(num_vars, i)->sym());
        }
    }

    if (auto v = old_proc->has_var()) map(v, proc->var(2, 0)->proj(2, 1));
    if (auto v = old_lam->has_var()) map(v, proc->var(2,1));
    proc->set(rewrite(old_lam->filter()), rewrite(old_lam->body()));
    pop();

    if (auto fvs = proc->type()->free_vars(); fvs.size() != 0)
        proc->blame("the type of this procedure is not closed, has free vars {}", fvs).bail();
    if (auto fvs = proc->free_vars(); fvs.size() != 0) {
        for (auto v : fvs) log().w("fv {} has binder {}", v, v->binder());
        proc->blame("the procedure is not closed, has free vars {}", fvs).bail();
    }

    return proc;
}