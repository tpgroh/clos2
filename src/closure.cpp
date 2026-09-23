#include "mim/world.h"

#include "mim/plug/clos2/clos2.h"

using namespace mim;
using namespace mim::plug::clos2;

const Def* Closure::closure_type(const Def* dom) {
    auto& w = dom->world();

    auto sig = w.mut_sigma(3);
    sig->set(0, w.type());
    auto N = sig->var(3, 0)->set("N");
    sig->set(1, N);
    sig->set(2, w.cn({N, dom}));

    return sig;
}

const Def* Closure::pack() const {
    auto& w       = procedure->world();
    auto clostype = closure_type(procedure->type()->dom());

    return w.tuple(clostype, {environment->type(), environment, procedure});
}

const Def* Closure::closure_apply(const Def* clos, const Def* arg) {
    auto& w             = clos->world();
    auto [_, env, proc] = clos->projs<3>();

    w.log().i("UP {}", clos);
    w.log().i("prc {}:{}", proc, proc->type());
    w.log().i("env {}:{}", env, env->type());
    w.log().i("arg {}:{}", arg, arg->type());
    w.tuple({clos, arg})->dot("crash.dot", {.follow_types = false});

    return w.app(proc, {env, arg});
}
