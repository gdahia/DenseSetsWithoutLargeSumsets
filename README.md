# Dense sets without large sumsets

Lean 4 formalization of Gabriel Dahia, João Pedro Marciano and Victor Souza,
[*Dense sets without large sumsets*](https://arxiv.org/abs/2607.15269), laid out for the
[Palomar registry](https://palomar-registry.org/).

## Results

Write `[n] = {1, …, n}` and `A + B = {a + b | a ∈ A, b ∈ B}`. For `0 ≤ δ ≤ 1`, let `φ(δ, N)` be
the largest integer `k` such that every `S ⊆ [N]` with `|S| ≥ δ N` contains a sumset `A + B` with
`A, B ⊆ [N]` and `min {|A|, |B|} ≥ k`. This function is defined by Kra, Moreira, Richter and
Robertson in
[*Problems on infinite sumset configurations in the integers and beyond*](https://arxiv.org/abs/2311.06197),
Bull. Amer. Math. Soc. 62 (2025), 537–574, Section 4.3. In Lean it is
`DenseSetsWithoutLargeSumsets.phi δ N`, with `δ : unitInterval`.

[Solution.lean](Solution.lean) proves the following statements, in the namespace
`DenseSetsWithoutLargeSumsets`. [Challenge.lean](Challenge.lean) contains the same statements in
terms of Mathlib and of the definitions `interval`, `pairEvent`, `sumsetThresholdSet` and `phi`,
with `sorry` placeholders.

**Theorem 1.1** (`exists_dense_subset_forall_add_not_subset`). For every `0 < γ ≤ 1` and
`0 < c < 1` there is `α > 0` such that, for all large `n` and every `n ^ (-α) < δ ≤ 1 - c`, some
`S ⊆ [n]` with `|S| ≥ δ n` contains no sumset `A + B` with `A, B ⊆ [n]` and

`min {|A|, |B|} ≥ (3 + γ) * log n / log (1 / δ)`.

**Corollary 1.2** (`exists_forall_phi_div_log_mem_Icc`). For every `0 < γ ≤ 1` and `0 < c < 1`
there is `α > 0` such that, for all large `n` and every `n ^ (-α) ≤ δ ≤ 1 - c`,

`(1 - γ) / log (1 / δ) ≤ φ(δ, n) / log n ≤ (3 + γ) / log (1 / δ)`.

**The bound of Hernández and Hetzel** (`one_div_log_one_div_le_liminf_phi_div_log`). For fixed
`0 < δ < 1`,

`1 / log (1 / δ) ≤ liminf φ(δ, N) / log N`.

This is Corollary C of Felipe Hernández and Luke Hetzel,
[*On growth rates of infinite and finite sumsets*](https://arxiv.org/abs/2606.07310). The paper
quotes it for the lower bound of Corollary 1.2. The proof here is different from theirs: see
below.

**The upper bound for fixed density** (`limsup_phi_div_log_le_three_div_log_one_div`). For fixed
`0 < δ < 1`, `limsup φ(δ, N) / log N ≤ 3 / log (1 / δ)`.

**Conjecture 4.10 of Kra, Moreira, Richter and Robertson**
(`limsup_phi_div_log_lt_top_and_liminf_phi_div_log_pos`). For fixed `0 < δ < 1`,

`limsup φ(δ, N) / log N < ∞` and `liminf φ(δ, N) / log N > 0`.

The two limits are taken in the extended reals, so the statement is the one of the conjecture.
The conjecture is stated for every `δ > 0`. The range here is `0 < δ < 1` because
`φ(1, N) = ⌊N / 2⌋`.

**Question 4.12 of Kra, Moreira, Richter and Robertson**
(`tendsto_phi_div_log_nhds_zero_of_tendsto_nhds_zero`). The question asks whether
`liminf φ(δ_N, N) / log N > 0` for some sequence `δ_N → 0`, for instance `δ_N = 1 / log N`. It is
not: `φ(δ_N, N) / log N → 0` for every sequence `δ_N → 0`.

The library and the solution contain no `sorry`, and the theorems depend on no axioms other than
`propext`, `Classical.choice` and `Quot.sound`. No proof changes the heartbeat limit.

The library has further statements. The main ones are the following.

| Declaration | Statement |
| --- | --- |
| `eventually_forall_exists_dense_subset_without_large_sumsets`, `dense_subset_without_large_sumsets` | Theorem 1.1 with the explicit exponent `denseSubsetDensityExponent γ c`, for every `δ` and for a sequence `δ n` |
| `eventually_pairEvent_probability_le` | Theorem 1.3: a `δ`-random subset of `[n]` contains such a sumset with probability at most `4 k ^ 2 / n ^ (γ / (8 (γ + 3)))`, where `k = ⌈(3 + γ) * log n / log (1 / δ)⌉` |
| `eventually_forall_phi_lt_log_div_log`, `eventually_forall_log_div_log_le_phi` | The two bounds of Corollary 1.2, the lower one for `δ ≥ n ^ (-γ / 4)` |
| `exists_mul_log_le_phi_le_mul_log` | For fixed `0 < δ < 1` there are `c > 0` and `C` with `c * log N ≤ φ(δ, N) ≤ C * log N` for all large `N` |
| `eventually_phi_logDensity_lt_log_div_log_log` | `φ(1 / log N, N) < 4 * log N / log log N` for all large `N` |
| `pairEvent_of_lt_density` | If `S ⊆ [n]`, `\|S\| ≥ δ n`, `1 ≤ k`, `1 ≤ m ≤ n` and `(k - 1) ^ (1 / k) * (1 + m / n) * m ^ (-1 / k) + k / n < δ`, then `S` contains `A + B` with `A, B ⊆ [n]` and `\|A\|, \|B\| ≥ k` |
| `largeSubsets_exists_zmodGAPPreimageContainer` | Large subsets `A₀ ⊆ A` and `B₀ ⊆ B` of sets with `\|A + B\| ≤ C k` lie in the preimage of a proper progression of `ZMod q` of bounded size and of dimension at most the Freiman dimension of `A₀ ∪ B₀` |
| `pairSumsetsFamily_ncard_le`, `pairSumsetsFamily_ncard_le_of_small_sumset` | The number of sumsets `A + B` of moderate size of two `k`-subsets of `[n]` |

## Proof and files

Theorem 1.1 follows the paper. Let `S` be a `δ`-random subset of `[n]` and
`k = ⌈(3 + γ) * log n / log (1 / δ)⌉`. The probability that `S` contains `A + B` with
`|A| = |B| = k` is bounded in three ranges of `|A + B|`.

- Small sumsets. Theorem 2 of Bollobás, Leader and Tiba gives subsets `A' ⊆ A` and `B' ⊆ B` of
  size about `√k` whose sumset is almost as large as that of large subsets of `A` and `B`. By
  Chang's theorem these lie in a proper generalized arithmetic progression of bounded size and of
  dimension at most the Freiman dimension, and Ruzsa's lower bound for sumsets in several
  dimensions bounds `|A' + B'|` from below in terms of that dimension. A union bound over
  progressions and over pairs `(A', B')` finishes this range.
- Moderate sumsets. The pairs `(A, B)` are counted through the Freiman isomorphism classes of
  `A ∪ B`, as in Green's count of sets with small sumset.
- Very large sumsets. A union bound over all pairs.

The lower bound of Corollary 1.2 is not proved as in Hernández and Hetzel, who use a finitary
intersectivity lemma. Here every `s ∈ S` is written as `(i + s) - i` for `0 ≤ i < m`. This gives a
relation between `[n + m]` and `[m]` with about `m |S|` pairs, and a `k × k` rectangle in it gives
`A + B ⊆ S` with `|A| = |B| = k`. The Kővári–Sós–Turán theorem bounds the number of pairs of a
relation without such a rectangle, and the choice `m = ⌈n / k⌉` gives the constant `1`.

| Files in `DenseSetsWithoutLargeSumsets/` | Contents |
| --- | --- |
| `Common.lean` | `interval`, `pairEvent`, the threshold `⌈c * log n / log (1 / δ)⌉` |
| `Probability.lean` | The binomial random subset of a finite set, tail bounds for the binomial distribution |
| `Combinatorics/Additive/ProperGAP.lean` | The number of proper progressions (`ChangFreimanRuzsa.GAP` with `GAP.Proper`) of given dimension and size in `ZMod q` |
| `RandomSetContainsNoSmallSumset/` | Small sumsets (Section 2 of the paper) |
| `CountingSumsetsOfModerateSize/` | Moderate sumsets (Section 3) |
| `SimpleBoundForVeryLargeSumsets.lean` | Very large sumsets (Section 4) |
| `DenseSubsetsWithoutLargeSumsets.lean` | Theorems 1.1 and 1.3 |
| `Combinatorics/SimpleGraph/BipartiteRel.lean` | A relation with more than `zarankiewicz` pairs contains a rectangle |
| `Combinatorics/Additive/SumsetFromZarankiewicz.lean`, `SumsetLowerBound.lean` | Sumsets in dense subsets of `[n]` from the Zarankiewicz function and from the Kővári–Sós–Turán theorem |
| `SumsetThreshold/` | `φ(δ, N)`, its upper and lower bounds, Corollary 1.2, Conjecture 4.10, Question 4.12 |
| `Mathlib/` | The Kővári–Sós–Turán theorem, copied from a Mathlib pull request |

Four results that the paper cites are proved in repositories of their own, which are Lake
dependencies pinned to a commit in `lakefile.toml`:

- [SumOfSetsInSeveralDimensions](https://github.com/gdahia/SumOfSetsInSeveralDimensions): the
  lower bound of Ruzsa, [*Sum of sets in several dimensions*](https://doi.org/10.1007/BF01302969).
  It also has the definition `SumOfSetsInSeveralDimensions.freimanDim` of the Freiman dimension,
  Ruzsa's bound for sets of given Freiman dimension,
  `card_add_sum_min_le_of_freimanDim_union`, and the bound `freimanDim X ≤ 2 κ - 1` for sets
  with `|X + X| ≤ κ |X|`, `freimanDim_le_two_mul_sub_one_of_card_add_le`.
- [ChangFreimanRuzsa](https://github.com/gdahia/ChangFreimanRuzsa): Chang's theorem in `ZMod q`
  with a `2`-proper progression of dimension at most the Freiman dimension of the set,
  `ChangFreimanRuzsa.exists_twoProperGAP_zmod_dim_le_freimanDim`. It uses Chang's lemma on large
  spectra from [APAP](https://github.com/YaelDillies/apap) and Minkowski's second theorem from
  [Tau Ceti](https://github.com/TauCetiProject/TauCeti).
- [LargeSumsetsFromSubsets](https://github.com/gdahia/LargeSumsetsFromSubsets): Theorem 2 of
  Bollobás, Leader and Tiba,
  [*Large sumsets from medium-sized subsets*](https://arxiv.org/abs/2206.09366).
- [CountingSetsWithSmallSumset](https://github.com/gdahia/CountingSetsWithSmallSumset): Sections 3
  and 4 of Ben Green, *Counting sets with small sumset, and the clique number of random Cayley
  graphs*, Combinatorica 25 (2005), 307–326: the number of sets of given Freiman dimension,
  `card_boundedFreimanDimSets`, and the number of Freiman isomorphism classes of sets with small
  sumset, `exists_smallRestrictedSumsetFreimanClassCover`.

These four repositories were split from this one, the first three at commit `5f4b915`, and are
private for now. CountingSetsWithSmallSumset is not on GitHub yet.

`Mathlib/Combinatorics/SimpleGraph/Extremal/KovariSosTuran.lean` is a copy of the proof of the
Kővári–Sós–Turán theorem by Mitchell Horner, from the Mathlib pull request
[#25841](https://github.com/leanprover-community/mathlib4/pull/25841) at commit `1ed83fc`, and
`Mathlib/Combinatorics/SimpleGraph/Bipartite.lean` has the four lemmas that the pull request adds
to the file of the same name. They are to be deleted when Mathlib has the theorem.

All files use the module system. [formalization.yaml](formalization.yaml) records the differences
from the paper, the scope, and the use of AI coding agents.

## Build

The Lean and Mathlib versions are pinned in `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`, to `v4.35.0-rc4`.

```sh
lake exe cache get
lake build
```

The default build includes the library, challenge, and solution. The `sorry` warnings from
`Challenge.lean` are expected. While the four repositories above are private, Lake cannot fetch
them over HTTPS without credentials; a checkout of each at the pinned commit under
`.lake/packages/` works.

CI also runs `scripts/check-lean-sources.py`, `scripts/validate-formalization.rb` and
`scripts/verify-comparator.sh`. The last one needs Linux with `bwrap`.
