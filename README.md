# Fluid

The goal of this project is to develop refactoring transformations for a toy
dependently-typed language called Fluid.

It accompanies the paper "Structural Refactorings for Exploring
Dependently-Typed Programming" submitted to [TFP 2024](https://trendsfp.github.io/index.html).

See command-line help with the `-h` flag (`stack run --` with Stack).

This repository contains a simple compiler for the Fluid language, which is a
subset of Idris with some basic data types such as `Vect`, `Nat`, `Fin`, and
`Maybe`, in `src/Lang`.

The type checking implementation for this can be found in `src/Checking`. It is
a bi-directional type checking implementation with inference, holes, and pattern
unification.

The repository also contains some basic refactoring transformations, such as
ornamenting declarations and expanding patterns in clauses. These can be found
in `src/Refactoring.`
