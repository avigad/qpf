Contents
========

This is work in progress.

- `for_mathlib.lean` : auxiliary stuff that should eventually be moved elsewhere.

- `pfunctor.lean` : unary polynomial functors, and the `W`-type as a polynomial functor.

- `M.lean` : the M-type contruction

- `qpf.lean` : quotients of unary polynomial functors, initial algebras, final coalgebras, and closure under quotients and composition. This is subsumed by the multivariate versions later on, which do not depend on the unary version. But we will keep the unary ones around for reference.

- `mvfunctor.lean` : tuples of types, tuples of functions, and functorial maps on these. Includes operations for appending a single type / function to a tuple, destructing n+1-ary tuples of types and functions into n-ary tuples and a last element, and related theorems.

- `mvpfunctor/` : multivariate polynomial functors, including W and M

- `mvqpf/` : multivariate quotients of polynomial functors, including initial algebras (fix) and final coalgebras (cofix).