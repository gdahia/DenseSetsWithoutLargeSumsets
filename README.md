# DenseSetsWithoutLargeSumsets

This repository contains the Lean 4 formalization of
[**Dense sets without large sumsets**](https://arxiv.org/abs/2607.15269), by Gabriel Dahia,
João Pedro Marciano, and Victor Souza.

The main result constructs dense subsets of $[n]$ which contain no sumset $A + B$ when both
summands are sufficiently large. The formalization includes the probabilistic construction and
the estimates for small, moderate, and very large sumsets which are combined in the final
theorem `DenseSetsWithoutLargeSumsets.dense_subset_without_large_sumsets`.

## Axioms

The development is built on Mathlib, except for two external additive-combinatorics inputs which
are currently stated axiomatically in `DenseSetsWithoutLargeSumsets/ExtraAxioms.lean`:

- Theorem 2 of Bollobás, Leader, and Tiba's
  [*Large sumsets from medium-sized subsets*](https://arxiv.org/abs/2206.09366), in a finite
  uniform-expectation form. Its unspecified constant is represented by
  `originalBltConstant`, and the theorem by `exists_blt_sample`.
- The proper-generalized-arithmetic-progression consequence of Mei-Chu Chang's
  [*A polynomial bound in Freiman's theorem*](https://doi.org/10.1215/S0012-7094-02-11331-3).
  Its absolute positive constant is represented by `changConstant`, with assumptions
  `changConstant_pos` and `exists_properGAP_of_small_sumset`.

All other ingredients used by the main theorem are proved in Lean from these assumptions and
Mathlib.

## Other formalized results

The repository also develops a substantial amount of reusable additive combinatorics, including:

- Sections 3 and 4 of Ben Green's
  [*Counting sets with small sumset, and the clique number of random Cayley graphs*](https://arxiv.org/abs/math/0304183):
  Freiman-relation systems and isomorphism classes, restricted sumsets, core decompositions,
  determining coordinates, bounded-dimension realization counts, and the count of
  small-self-sumset isomorphism classes.
- Imre Z. Ruzsa's sharp lower bound from
  [*Sum of sets in several dimensions*](https://doi.org/10.1007/BF01302969), together with the
  transport of this geometric bound through rational Freiman models and its consequences for
  Freiman dimension.
- Supporting results about generalized arithmetic progressions, finite probability spaces,
  binomial random finite sets, and concentration estimates needed for the main argument.

## Build

Build the project:

```bash
lake exe cache get
lake build
```
