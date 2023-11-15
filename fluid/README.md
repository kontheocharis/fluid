# Fluid

The goal of this project is to develop refactoring transformations for a toy dependently-typed language called Fluid.

See command-line help with the `-h` flag (`stack run --` with Stack).

This repository contains a simple compiler for the Fluid language, which is a
subset of Idris with some basic data types such as `Vect`, `Nat`, `Fin`, and
`Maybe`, in `src/Lang`.

The type checking implementation for this can be found in `src/Checking`.
It is a bi-directional type checking implementation with inference, holes, and pattern unification.

The repository also contains some basic refactoring transformations, such as ornamenting declarations and
expanding patterns in clauses. These can be found in `src/Refactoring.`

## General TODO

- [x] Write a small parser & REPL
- [ ] Handle inference of lists vs vectors

## Type-checking TODO

- [ ] Handle reducing declarations during normalisation
- [ ] Add support for implicit (type?) arguments
- [ ] Add unit and void types (or use Fin Z)
- [ ] Handle impossible patterns in TC
- [ ] Implement a pattern exhaustiveness/totality check
- [ ] Find a convenient way to query the type of some language node (including holes), to be used for type-aware transformations.

## Refactoring TODO

- [ ] Switch an argument to be implicit/explicit (type-directed).
