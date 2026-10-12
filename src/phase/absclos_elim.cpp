#include "mim/plug/clos2/phase/absclos_elim.h"

#include "mim/def.h"
#include "mim/phase.h"

using namespace mim;
using namespace mim::plug;
using namespace mim::plug::clos2;

const Def* AbsClosElim::rewrite_mut_Pi(Pi* pi) {
    if (Pi::isa_cn(pi)) return Closure::closure_type(rewrite(pi->dom()));
    return RWPhase::rewrite_mut_Pi(pi);
}

const Def* AbsClosElim::rewrite_imm_Pi(const Pi* pi) {
    if (Pi::isa_cn(pi)) return Closure::closure_type(rewrite(pi->dom()));
    return RWPhase::rewrite_imm_Pi(pi);
}

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

    auto dom = w.mut_sigma(rewrite(old_proc->type()->type()), 2);
    dom->set(0, rewrite(old_proc->dom()));
    dom->set(1, rewrite(old_lam->dom()));
    auto proc = w.mut_con(dom);
    proc->set(old_proc->dbg_key());

    procedures_[old_proc] = proc;

    log().i("new proc {}:{}", proc, proc->type());

    push();
    map(old_proc->var(), proc->var(2,0));
    if (auto mlam = old_lam->isa_mut<Lam>())
        map(mlam->var(), proc->var(2,1));
    proc->set(rewrite(old_lam->filter()), rewrite(old_lam->body()));
    pop();

    return proc;
}