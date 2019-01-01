# Datatypes as Quotients of Polynomial Functors

This repository contains joint work in progress by Jeremy Avigad, Mario Carneiro, and Simon Hudon.

In analogy to Isabelle's *bounded natural functors*, we represent datatypes as *quotients of polynomial functors*. The file `qpf.lean` shows that every qpf has an initial algebra and a final coalgebra, and that compositions and quotients of qpfs are again qpfs.

(The constructions depend on M-type constructions which we have also carried out in Lean, but, at the moment, they are assumed axiomatically in `qpf.lean`.)

We are working on a multiple-arity version of qpfs, and showing that the qpf structure is preserved under the initial algebra and final coalgebra constructions.

For more information, see this talk: [http://www.andrew.cmu.edu/user/avigad/Talks/qpf](http://www.andrew.cmu.edu/user/avigad/Talks/qpf).