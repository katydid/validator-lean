# validator-lean

Proofs written in [Lean4](https://leanprover.github.io/) for the core [katydid](https://katydid.github.io/) validation algorithm

![Check Proofs](https://github.com/katydid/validator-lean/workflows/Check%20Proofs/badge.svg)

## Goal

The goal is to formalize the core [katydid](https://katydid.github.io/) validation algorithm.
This algorithm allows us to validate millions of serialized data structures per second on a single core.
The algorithm is based on derivatives for regular expressions and extends this to Visibly Pushdown Automata (VPA), by splitting the derivative function into two functions.
It also includes several basic optimizations, such as memoization, simplification, laziness, zipping of multiple states, short circuiting, evaluation at compilation, symbolic derivatives and a pull based parser for serialized data structures that allows us to skip over some of the parsing. 
You can play around with the validation language on its [playground](http://katydid.github.io/play/).

## Plan

This is just a quick overview of the steps towards our goal.

- [ ] Create Language definition for the symbolic tree expressions.
- [ ] Code Pull-based Parser class in Lean and implement JSON as an example.
- [x] Code Katydid validator algorithm in Lean.
- [ ] Prove correctness of derivative tree algorithm.
- [ ] Prove decidablity of derivative tree algorithm.
- [ ] Prove that the simple tree function and the VPA functions are equivalent and equivalent to the inductive predicate.
- [ ] Prove correctness of new simplification rules
- [ ] Prove all optimizations of the katydid algorithm

## Contributing

The contributing guidelines are short and shouldn't be surprising.
Read the [contributing guidelines](./CONTRIBUTING.md).

## Learning

* An explanation of the core [validator algorithm](./Validator/Learning/Readme.md)
* [learnings about Lean](./learnings/) we had while creating this code.

## Setup

  - Lean4 has exceptional [instructions for installing Lean4 in VS Code](https://lean-lang.org/install/).
  - Remember to also add `lake` (the build system for lean) to your `PATH`.  You can do this on mac by adding `export PATH=~/.elan/bin/:${PATH}` to your  `~/.zshrc` file
  - Use mathlib's cache to speed up building time by running: `$ lake exe cache get`
