# refactor-v1

The goal of this project is to develop refactoring transformations for a dependently-typed language.

This repository contains a small dependently-typed language with some basic data types
such as `Vect`, `Nat`, `Fin`, and `Maybe`, in `src/Lang`.

The type checking implementation for this can be found in `src/Checking`.
It is a bi-directional type checking implementation with inference, holes, and pattern unification.

It also contains some basic refactoring transformations, such as ornamenting declarations and
expanding patterns in clauses. These can be found in `src/Refactoring.`

## General TODO

- Write a small parser & REPL

## Type-checking TODO

- Handle reducing declarations during normalisation
- Add support for implicit (type?) arguments
- Add unit and void types (or use Fin Z)
- Handle impossible patterns in TC
- Implement a pattern exhaustiveness/totality check
- Find a convenient way to query the type of some language node (including holes), to be used for type-aware transformations.

## Refactoring TODO

- Switch an argument to be implicit/explicit (type-directed).
