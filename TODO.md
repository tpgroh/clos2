# TODO
[x] first implement a finer freevar (fixpoint solving by iteration) then `Def::freevars`
    orient on the algo from the already implemented freevars
    that one has the problem that lambda's are unary (meaning that they take one argument possible containing multiple vars) this means that
    lam foo (a b : Nat) ->
    lam bar (x y : Nat) -> x * y + a
    the free vars of `bar` are now a,b but we expect just a!
    This is even worse if foo takes an argument `mem` to store side efects as those are linear
    but mim doesn't have linear types => the type system cannot find errors where because of this false analysis
    `mem` might get copied in closure conversion.
    - for this I should use the thresholded vars()/... methods.
    var() gets the unary vars and vars() unpacks the tuple
    this is problemetic if there are many arguments packed inside the tuple.
    in this case just take the unary as the free var (speed over correctnes)

# Other Stuff for later
using llvm Landingpads we can sometimes get arround closure conversion
for escaping stuff we require a garbage collector (for example tinygc)
in some cases we could use setjmp/longjump (this is more important then the other stuff)
