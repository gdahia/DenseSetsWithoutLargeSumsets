# DenseSetsWithoutLargeSumsets

This repository contains the Lean 4 formalization of
[**Dense sets without large sumsets**](https://arxiv.org/abs/2607.15269), by Gabriel Dahia,
João Pedro Marciano, and Victor Souza.

The main result constructs dense subsets of $[n]$ which contain no sumset $A + B$ when both
summands are sufficiently large. The formalization includes the probabilistic construction and
the estimates for small, moderate, and very large sumsets which are combined in the final
theorem `DenseSetsWithoutLargeSumsets.dense_subset_without_large_sumsets`.

The only dependencies are Mathlib and the [`APAP` project](https://yaeldillies.github.io/apap/),
where the latter is used for additive combinatorics / discrete Fourier analysis machinery
in Chang's theorem.

One file, `DenseSetsWithoutLargeSumsets/Combinatorics/SimpleGraph/KovariSosTuran.lean`, is not
original to this project: it is a verbatim copy of the Kővári–Sós–Turán theorem written by
**Mitchell Horner** for the open Mathlib pull request
[#25841](https://github.com/leanprover-community/mathlib4/pull/25841), reproduced here under
Mathlib's Apache 2.0 license because that pull request has not been merged into the Mathlib
revision this project pins. The only edits are the removal of the `module` / `public import`
declarations. Once the pull request lands, the file should be deleted in favour of importing
`Mathlib.Combinatorics.SimpleGraph.Extremal.KovariSosTuran`.

## Other formalized results

The repository also develops a substantial amount of reusable additive combinatorics, including:

- A weak version of proper-generalized-arithmetic-progression consequence of Mei-Chu Chang's
  [*A polynomial bound in Freiman's theorem*](https://doi.org/10.1215/S0012-7094-02-11331-3).
- Sections 3 and 4 of Ben Green's
  [*Counting sets with small sumset, and the clique number of random Cayley graphs*](https://arxiv.org/abs/math/0304183):
  Freiman-relation systems and isomorphism classes, restricted sumsets, core decompositions,
  determining coordinates, bounded-dimension realization counts, and the count of
  small-self-sumset isomorphism classes.
- Imre Z. Ruzsa's sharp lower bound from
  [*Sum of sets in several dimensions*](https://doi.org/10.1007/BF01302969), together with the
  transport of this geometric bound through rational Freiman models and its consequences for
  Freiman dimension.
- Theorem 2 of Bollobás, Leader, and Tiba's
  [*Large sumsets from medium-sized subsets*](https://arxiv.org/abs/2206.09366).
- Supporting results about generalized arithmetic progressions, finite probability spaces,
  binomial random finite sets, and concentration estimates needed for the main argument.
- The complementary *lower* bound (`DenseSetsWithoutLargeSumsets.pairEvent_of_lt_density`).
  For any $m\le n$, representing every $s\in S\setminus\{1\}$ in the $m$ ways
  $s=(i+s)-i$ gives a bipartite relation with at least $m(|S|-1)$ edges. The
  Kővári–Sós–Turán estimate yields the sharp sufficient density
  $$(k-1)^{1/k}(1+m/n)m^{-1/k}+k/n<\delta.$$
  Taking $m=\lfloor n/k\rfloor$ gives
  $k=(1-o(1))\log n/\log(1/\delta)$, matching the construction's leading constant up to a
  factor of $3$.

## Build

Build the project:

```bash
lake exe cache get
lake build
```
