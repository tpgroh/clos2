#include "mim/plug/clos2/phase/absclos_elim.h"

#include "mim/def.h"
#include "mim/phase.h"

using namespace mim;
using namespace mim::plug;
using namespace mim::plug::clos2;

Lam* AbsClosElim::rewrite_procedure(Lam* old_proc) {
    log().i("rewrite procedure {}", old_proc);

    auto& w = new_world();
    auto old_lam = old_proc->body()->as<Lam>();

    log().i("proc {}:{}", old_proc, old_proc->type());
    log().i("lam {}:{}", old_lam, old_lam->type());

    if (auto it = procedures_.find(old_proc); it != procedures_.end()) {
        log().i("reuse procedure {}", old_proc, it->second);
        return it->second;
    }

    push(); // this prevents a bug where we leak stuff from the type rewrite into the body
    auto dom_type = rewrite(old_proc->type()->type());
    log().i("dom_type {}", dom_type);
    auto dom = w.mut_sigma(dom_type, 2);
    // TODO: I actually dont want to name this sigma but there it currently is required to dump something that is recursive
    dom->set("procedure_dom");
    auto env_type = rewrite(old_proc->dom());
    log().i("env type {}", env_type);
    dom->set(0, w.sigma({w.cn(dom), env_type}));
    dom->var(2, 0)->set("clos");
    map(old_proc->var(), dom->var(2, 0)->proj(2, 1));
    dom->set(1, rewrite(old_lam->dom()));
    dom->var(2, 1)->set("arg");
    pop();
    auto proc = w.mut_con(dom);
    proc->set(old_proc->dbg_key());

    procedures_[old_proc] = proc;

    log().i("new proc {}:{}", proc, proc->type());

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

    push();
    map(old_proc->var(), proc->var(2, 0)->proj(2, 1));
    if (auto mlam = old_lam->isa_mut<Lam>())
        map(mlam->var(), proc->var(2,1));
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