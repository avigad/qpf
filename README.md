[![Build Status](https://travis-ci.org/avigad/qpf.svg?branch=master)](https://travis-ci.org/avigad/qpf)

# Datatypes as Quotients of Polynomial Functors

This repository contains work in progress by Jeremy Avigad, Mario Carneiro, and Simon Hudon.

In analogy to Isabelle's *bounded natural functors*, we represent datatypes as *quotients of polynomial functors*. The file `qpf.lean` shows that every qpf has an initial algebra and a final coalgebra, and that compositions and quotients of qpfs are again qpfs. It should compile with any recent version of Lean's `mathlib`.

We are working on the multiple-arity version of qpfs, and showing that the qpf structure is preserved under the initial algebra and final coalgebra constructions.

For more information, see this talk: [http://www.andrew.cmu.edu/user/avigad/Talks/qpf.pdf](http://www.andrew.cmu.edu/user/avigad/Talks/qpf.pdf).
