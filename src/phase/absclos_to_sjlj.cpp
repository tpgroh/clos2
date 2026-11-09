#include "mim/plug/clos2/phase/absclos_to_sjlj.h"

using namespace mim;
using namespace mim::plug;
using namespace mim::plug::clos2;

const Def* AbsClosSjLj::rewrite_body2setjmp(Lam* old_lam) {
    return RWPhase::rewrite_mut_Lam(old_lam);
}
