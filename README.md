# Clos2 - Closure Conversion in MimIR
The Target of this project is to add closure conversion to the research compiler [MimIR](https://github.com/mimir/mimir).

## Closure Conversion
TODO describe what Closure Conversion is.

## Installation
Because this is a plugin for `MimIR` you will have to clone [it's repository](https://github.com/mimir/mimir) and get it to work.

Then you can add this plugin by cloning this repository into `extra/`

MimIR will take care of the rest and will include this plugin in the next build.

# Notes
## different ideas that I was playing around with
### Idea 1 : a transformation based on the paper from 2018
This paper uses abstract closure conversion as the result of this paper was that a closure representation is impossible (when we dont want to add logical paradoxes)

The presented transformation can still be used to get a phase that hoists up every lambda (using curried application)
Essentially after this transformation we have lambdas at the top level which take the environment as an argument and then return the original lambda with free vars substituted by extractions of the environment.
Thus this transformation is robust and should be type safe.

#### Pro
- all lambdas are hoisted up to the top level
- after it there are no more nesting/scoping problems because everything is hoisted up

#### Con
- it **must** use curried application (see above why)
- it requires "reallocating" the environment which is not really a problem if this is just intermediate

### Idea 2 : my experiment where I wanted to see how far I could get using existentials for the closure representation

### Idea 3 : use lambda lifting to get rid of free vars in the type of lambdas
Here I had problems with scoping.

```mim
extern con pick (m: mem.M 0, n: Nat, i: Idx n, j: Idx n, c: Bool, return_1: Cn [mem.M 0, Idx n]) as _1 =
    con choose (_2: mem.M 0, _3: Cn [mem.M 0, Idx n]) as _4 =
        fun snd (m_1: mem.M 0): [mem.M 0, Idx n] =
            return (m_1, j);

        fun fst (m_2: mem.M 0): [mem.M 0, Idx n] =
            return (m_2, i);

        (snd, fst)#c _4;

    choose (m, return_1);
```

In this example the line `(snd, fst)#c _4` contains this problem. We have to
pass the free var `n` to `fst`,`snd` thus we pass `(n', _4)` in the rewritten
line. Those two functions now expect a return continuation which receives
`[mem.M 0, Idx n']` where `n'` is the argument of the rewritten `choose` which
replaces the free var `n` in its type. But `j` is of the actual type `Idx n`
not `Idx n'`. You might notice that this looks like a familiar problem.

In Idea 2 we had the exact same problem (which could be solved using a special
kind of singletons which we dont want in mim)

At this point I'm thinking in two directions.
1. maybe I could combine Idea 2 with Idea 3 by performing both at the same
   time. Lambda lift free vars from the type and put other free vars inside the
   environment. In this case the environment has to follow after the lambda
   lifted arguments. Because their type might depend on those lifted arguments.
   (In the above example `j` from the environment has a type that would depend
   on the lifted argument for fv `n`)
2. another phase before this one which removes those scoping problems. There
   **must not** be anything free inside the lambda's body which is not also
   free inside the lambda's type and depends on anything which is free inside
   the lambda's type.

Ideas that did not make it.
3. select the right n in the application rewrite.
   - this is not possible. In the above example I would just have to add
     another argument that gets passed which is from another scope than j but
     also depends on n. then I would have to pass n from both scopes (not
     possible) or tell the type system that they are equal (again the old
     problem)

### future plan
1. use Idea 1
    - this removes all nesting problems
    - it can be improved by using closure annotation with a normalization that performs delayed partial application this way I keep closures as a wrapped tuple.
2. lambda lifting.
    - lambda lift only the free vars of the types of the lambdas.
    - this might be complicated because we undo some of the work done in the first step.
    - this allows closure representation using existentials
        - I still have to justify why lambda lifting is allowed here. (It might not be in general). This has to do with lambda lifting only being allowed for known call sites.
    - the environment has to be the last argument of the procedure as its type might depend on the previous arguments.
3. use existential representation to hide the environment
    - this should now be possible

#### 3.2 - does not work as I wanted - write up by claude
**Idea.** Lift a free var of `f`'s *type* to an extra parameter passed at every call site, so
the type closes and the existing `[Env: *, Cn [Env, …], Env]` representation still works.

**Why it fails.** Lifting turns a dependency into a coincidence. Source:

```mim
extern fun make_adder (m: Nat, n: Idx m): Fn Idx m → Idx m =
    let f = fn (x: Idx m) = return (x + n);
    return f;
```

After lifting `m` out of `f`'s type:

```mim
con f (m: Nat, n: Idx m) as _1@(ff) (m_1: Nat, x: Idx m_1, return_1: Cn [Nat, Idx m_1]) as _2 =
    let _3 = core.wrap.add 0 @ m_1 (n, x);   // n : Idx m, but x : Idx m_1
    return_1 (m_1, _3);

extern fun make_adder (_4: [m: Nat, Idx m])
    : [m_2: Nat, Cn [m_3: Nat, Idx m_3, Cn [m_4: Nat, Idx m_3]]] = …
```

The `add` is well-typed only under `m ≡ m_1`, which nothing in the type records — the lifted
parameter is unconstrained. The same break reappears at the use site: the result advertises
*every* `m_3`, while the code works only for `m_3 = _4#0`, and `m_2` is never tied to `m_3`.

Singletons do not repair it: `m_1: «m»` is transparent (`#m_1` normalizes back to `m`, the
binder never occurs in the body), so the free var is re-spelled, not removed; over a concrete
`m` it also pins the closure type. The variant that would work, `«env#0»`, is unwritable in
the closure type, where only `Env : *` is in scope — never an environment *value*.

**Conclusion.** The free variable belongs to the enclosing context, not to the signature:
closure conversion rewrites the *body*, never the type. So `f`'s converted type keeps `m`
free, and the closure representation is allowed to carry free vars in its type.

### Idea 4
use Idea 1 (the 2018 papers transformation) - here I'll use my implementation of Idea 3.
this hoists up every (in the future only selected) lambda(s) while annotating important parts for later phases.
I should add another annotation phase or update the above one to also annotate use sites/etc instead of only construction sites.
Then a phase that works on that but simply ignoring free vars in the type.
