[![Build Status](https://travis-ci.org/avigad/qpf.svg?branch=master)](https://travis-ci.org/avigad/qpf)

# Data Types as Quotients of Polynomial Functors

This repository contains a formalization of data type constructions in Lean, by Jeremy Avigad, Mario Carneiro, and Simon Hudon. A preliminary version of the work is described in this talk: [http://www.andrew.cmu.edu/user/avigad/Talks/qpf.pdf](http://www.andrew.cmu.edu/user/avigad/Talks/qpf.pdf).

See the `README` file in the `src` folder for a description of the contents.

The easiest way to test the code is as follows:

- Install a precompiled binary of [Lean](https://github.com/leanprover/lean/releases/tag/v3.4.2).

- In the root folder of this repository, type
  ```
        path-to-lean/bin/leanpkg build
  ```
  where `path-to-lean` is the path to the folder you just installed.

This will install a local copy of the [mathlib](https://github.com/leanprover-community/mathlib) and compile and check the dependencies as well. Lean will report any errors or `sorry`s. (There shouldn't be any.)

If you want to browse the files with interactive feedback from Lean, we recommend using [Visual Studio Code](https://code.visualstudio.com/) and installing the Lean extension via the extension manager.

There are variations. For instructions that install `elan`, a system which will manage versions of Lean for you automatically, see [here](https://github.com/leanprover-community/mathlib/blob/master/docs/elan.md). You can also install `mathlib` via binaries, following the directions in the README file [here](https://github.com/leanprover-community/mathlib).