# Dense sets without large sumsets

Lean 4 formalization of Gabriel Dahia, João Pedro Marciano and Victor Souza,
[*Dense sets without large sumsets*](https://arxiv.org/abs/2607.15269): for $0 < \delta < 1$ and
all large $n$ there is $S \subseteq \{1, \dots, n\}$ with $|S| \ge \delta n$ that contains no sumset
$A + B$ with $\min\{|A|, |B|\} \ge (3 + o(1)) \log n / \log(1 / \delta)$. The formalization also
covers the function $\varphi(\delta, N)$ of Kra, Moreira, Richter and Robertson,
[*Problems on infinite sumset configurations in the integers and beyond*](https://arxiv.org/abs/2311.06197),
Bull. Amer. Math. Soc. 62 (2025), 537–574: Corollary 1.2 of the paper, the lower bound of Felipe
Hernández and Luke Hetzel, Conjecture 4.10 and the negative answer to Question 4.12.

## Results

Write $[n] = \{1, \dots, n\}$ and $A + B = \{a + b : a \in A, b \in B\}$. For
$0 \le \delta \le 1$, $\varphi(\delta, N)$ is the largest integer $k$ such that every
$S \subseteq [N]$ with $|S| \ge \delta N$ contains a sumset $A + B$ with $A, B \subseteq [N]$ and
$\min\{|A|, |B|\} \ge k$. In Lean it is `DenseSetsWithoutLargeSumsets.phi δ N`, with
`δ : unitInterval`. All names below are in the namespace `DenseSetsWithoutLargeSumsets`.

**Theorem 1** (Theorem 1.1 of the paper, `exists_dense_subset_forall_add_not_subset`). For every
$0 < \gamma \le 1$ and $0 < c < 1$ there is $\alpha > 0$ such that, for all large $n$ and every
$n^{-\alpha} < \delta \le 1 - c$, some $S \subseteq [n]$ with $|S| \ge \delta n$ contains no sumset
$A + B$ with $A, B \subseteq [n]$ and

$$\min\{|A|, |B|\} \ge \frac{(3 + \gamma) \log n}{\log(1 / \delta)}.$$

**Theorem 2** (Corollary 1.2 of the paper, `exists_forall_phi_div_log_mem_Icc`). For every
$0 < \gamma \le 1$ and $0 < c < 1$ there is $\alpha > 0$ such that, for all large $n$ and every
$n^{-\alpha} \le \delta \le 1 - c$,

$$\frac{1 - \gamma}{\log(1 / \delta)} \le \frac{\varphi(\delta, n)}{\log n} \le \frac{3 + \gamma}{\log(1 / \delta)}.$$

**Theorem 3** (Corollary C of Hernández and Hetzel, `one_div_log_one_div_le_liminf_phi_div_log`).
For fixed $0 < \delta < 1$,

$$\frac{1}{\log(1 / \delta)} \le \liminf_{N \to \infty} \frac{\varphi(\delta, N)}{\log N}.$$

This is Corollary C of [*On growth rates of infinite and finite sumsets*](https://arxiv.org/abs/2606.07310).
The paper quotes it for the lower bound of Corollary 1.2. The proof here is not theirs: see below.

**Theorem 4** (`limsup_phi_div_log_le_three_div_log_one_div`). For fixed $0 < \delta < 1$,

$$\limsup_{N \to \infty} \frac{\varphi(\delta, N)}{\log N} \le \frac{3}{\log(1 / \delta)}.$$

**Theorem 5** (Conjecture 4.10 of Kra, Moreira, Richter and Robertson,
`limsup_phi_div_log_lt_top_and_liminf_phi_div_log_pos`). For fixed $0 < \delta < 1$,

$$\limsup_{N \to \infty} \frac{\varphi(\delta, N)}{\log N} < \infty \quad \text{and} \quad \liminf_{N \to \infty} \frac{\varphi(\delta, N)}{\log N} > 0,$$

with both limits taken in the extended reals. The conjecture is stated for every $\delta > 0$. The
range here is $0 < \delta < 1$ because $\varphi(1, N) = \lfloor N / 2 \rfloor$.

**Theorem 6** (Question 4.12 of Kra, Moreira, Richter and Robertson,
`tendsto_phi_div_log_nhds_zero_of_tendsto_nhds_zero`). The question asks whether
$\liminf_N \varphi(\delta_N, N) / \log N > 0$ for some sequence $\delta_N \to 0$, for instance
$\delta_N = 1 / \log N$. It is not: for every sequence $\delta_N \to 0$,

$$\frac{\varphi(\delta_N, N)}{\log N} \to 0.$$

[Challenge.lean](DenseSetsWithoutLargeSumsetsPalomar/Challenge.lean) states these six theorems
under the library names with a prime, with `sorry` placeholders, in terms of Mathlib and of the
definitions `interval`, `pairEvent`, `sumsetThresholdSet` and `phi`.
[Solution.lean](DenseSetsWithoutLargeSumsetsPalomar/Solution.lean) proves each statement by the
library theorem. The library and the solution contain no `sorry`, and the theorems depend on no
axioms other than `propext`, `Classical.choice` and `Quot.sound`.

The library has further statements. The main ones are the following.

| Declaration | Statement |
| --- | --- |
| `eventually_forall_exists_dense_subset_without_large_sumsets`, `dense_subset_without_large_sumsets` | Theorem 1.1 with the explicit exponent `denseSubsetDensityExponent γ c`, for every $\delta$ and for a sequence $\delta_n$ |
| `eventually_pairEvent_probability_le` | Theorem 1.3: a $\delta$-random subset of $[n]$ contains such a sumset with probability at most $4 k^2 / n^{\gamma / (8 (\gamma + 3))}$, where $k = \lceil (3 + \gamma) \log n / \log(1 / \delta) \rceil$ |
| `eventually_forall_phi_lt_log_div_log`, `eventually_forall_log_div_log_le_phi` | The two bounds of Corollary 1.2, the lower one for $\delta \ge n^{-\gamma / 4}$ |
| `exists_mul_log_le_phi_le_mul_log` | For fixed $0 < \delta < 1$ there are $c > 0$ and $C$ with $c \log N \le \varphi(\delta, N) \le C \log N$ for all large $N$ |
| `eventually_phi_logDensity_lt_log_div_log_log` | $\varphi(1 / \log N, N) < 4 \log N / \log \log N$ for all large $N$ |
| `pairEvent_of_lt_density` | If $S \subseteq [n]$, $\|S\| \ge \delta n$, $1 \le k$, $1 \le m \le n$ and $(k - 1)^{1 / k} (1 + m / n) m^{-1 / k} + k / n < \delta$, then $S$ contains $A + B$ with $A, B \subseteq [n]$ and $\|A\|, \|B\| \ge k$ |
| `largeSubsets_exists_zmodGAPPreimageContainer` | Large subsets $A_0 \subseteq A$ and $B_0 \subseteq B$ of sets with $\|A + B\| \le C k$ lie in the preimage of a proper progression of `ZMod q` of bounded size and of dimension at most the Freiman dimension of $A_0 \cup B_0$ |
| `pairSumsetsFamily_ncard_le`, `pairSumsetsFamily_ncard_le_of_small_sumset` | The number of sumsets $A + B$ of moderate size of two $k$-subsets of $[n]$ |

Theorem 1.1 follows the paper. Let $S$ be a $\delta$-random subset of $[n]$ and
$k = \lceil (3 + \gamma) \log n / \log(1 / \delta) \rceil$. The probability that $S$ contains
$A + B$ with $|A| = |B| = k$ is bounded in three ranges of $|A + B|$.

- Small sumsets. Theorem 2 of Bollobás, Leader and Tiba gives subsets $A' \subseteq A$ and
  $B' \subseteq B$ of size about $\sqrt{k}$ whose sumset is almost as large as that of large
  subsets of $A$ and $B$. By Chang's theorem these lie in a proper generalized arithmetic
  progression of bounded size and of dimension at most the Freiman dimension, and Ruzsa's lower
  bound for sumsets in several dimensions bounds $|A' + B'|$ from below in terms of that
  dimension. A union bound over progressions and over pairs $(A', B')$ finishes this range.
- Moderate sumsets. The pairs $(A, B)$ are counted through the Freiman isomorphism classes of
  $A \cup B$, as in Green's count of sets with small sumset.
- Very large sumsets. A union bound over all pairs.

The lower bound of Theorem 3 is not proved as in Hernández and Hetzel, who use a finitary
intersectivity lemma. Here every $s \in S$ is written as $(i + s) - i$ for $0 \le i < m$. This
gives a relation between $[n + m]$ and $[m]$ with about $m |S|$ pairs, and a $k \times k$ rectangle
in it gives $A + B \subseteq S$ with $|A| = |B| = k$. The Kővári–Sós–Turán theorem bounds the number
of pairs of a relation without such a rectangle, and the choice $m = \lceil n / k \rceil$ gives the
constant $1$.

Four results that the paper cites are proved in Lake dependencies pinned to a commit in
`lakefile.toml`:

- [SumOfSetsInSeveralDimensions](https://github.com/gdahia/SumOfSetsInSeveralDimensions): the
  lower bound of Ruzsa, [*Sum of sets in several dimensions*](https://doi.org/10.1007/BF01302969),
  the Freiman dimension `SumOfSetsInSeveralDimensions.freimanDim`, Ruzsa's bound for sets of given
  Freiman dimension, `card_add_sum_min_le_of_freimanDim_union`, and the bound
  $\dim_F X \le 2\kappa - 1$ for sets with $|X + X| \le \kappa |X|$,
  `freimanDim_le_two_mul_sub_one_of_card_add_le`.
- [ChangFreimanRuzsa](https://github.com/gdahia/ChangFreimanRuzsa): Chang's theorem in `ZMod q`
  with a $2$-proper progression of dimension at most the Freiman dimension of the set,
  `ChangFreimanRuzsa.exists_twoProperGAP_zmod_dim_le_freimanDim`. It uses Chang's lemma on large
  spectra from [APAP](https://github.com/YaelDillies/apap) and Minkowski's second theorem from
  [Tau Ceti](https://github.com/TauCetiProject/TauCeti).
- [LargeSumsetsFromSubsets](https://github.com/gdahia/LargeSumsetsFromSubsets): Theorem 2 of
  Bollobás, Leader and Tiba,
  [*Large sumsets from medium-sized subsets*](https://arxiv.org/abs/2206.09366).
- [CountingSetsWithSmallSumset](https://github.com/gdahia/CountingSetsWithSmallSumset): Sections 3
  and 4 of Ben Green, *Counting sets with small sumset, and the clique number of random Cayley
  graphs*, Combinatorica 25 (2005), 307–326: Lemma 11, Proposition 18 and the bound for the members
  of a Freiman isomorphism class in an interval from the proof of Proposition 23. From them,
  `CountingSumsetsOfModerateSize/BoundedFreimanDimSets.lean` counts the sets of natural numbers of
  given Freiman dimension, `card_boundedFreimanDimSets` and `smallSumsetFreimanDimSets_ncard_le`.

## Files

| Files in `DenseSetsWithoutLargeSumsets/` | Contents |
| --- | --- |
| `Common.lean` | `interval`, `pairEvent`, the threshold $\lceil c \log n / \log(1 / \delta) \rceil$ |
| `Probability.lean` | The binomial random subset of a finite set, tail bounds for the binomial distribution |
| `Combinatorics/Additive/ProperGAP.lean` | The number of proper progressions (`ChangFreimanRuzsa.GAP` with `GAP.Proper`) of given dimension and size in `ZMod q` |
| `RandomSetContainsNoSmallSumset/` | Small sumsets (Section 2 of the paper) |
| `CountingSumsetsOfModerateSize/` | Moderate sumsets (Section 3) |
| `SimpleBoundForVeryLargeSumsets.lean` | Very large sumsets (Section 4) |
| `DenseSubsetsWithoutLargeSumsets.lean` | Theorems 1.1 and 1.3 |
| `Combinatorics/SimpleGraph/BipartiteRel.lean` | A relation with more than `zarankiewicz` pairs contains a rectangle |
| `Combinatorics/Additive/SumsetFromZarankiewicz.lean`, `SumsetLowerBound.lean` | Sumsets in dense subsets of $[n]$ from the Zarankiewicz function and from the Kővári–Sós–Turán theorem |
| `SumsetThreshold/` | $\varphi(\delta, N)$, its upper and lower bounds, Corollary 1.2, Conjecture 4.10, Question 4.12 |
| `Mathlib/` | The Kővári–Sós–Turán theorem |

`Mathlib/Combinatorics/SimpleGraph/Extremal/KovariSosTuran.lean` is the proof of the
Kővári–Sós–Turán theorem by Mitchell Horner in the Mathlib pull request
[#25841](https://github.com/leanprover-community/mathlib4/pull/25841), at commit `1ed83fc`, and
`Mathlib/Combinatorics/SimpleGraph/Bipartite.lean` has the four lemmas that the pull request adds
to the file of the same name. They are to be deleted when Mathlib has the theorem.

[formalization.yaml](formalization.yaml) records the sources, the differences from them, the
scope, and the use of AI coding agents.

## Verification

`Challenge.lean` imports only Mathlib. It repeats the library definitions of `interval`,
`pairEvent`, `sumsetThresholdSet` and `phi` and states
`exists_dense_subset_forall_add_not_subset'`, `exists_forall_phi_div_log_mem_Icc'`,
`one_div_log_one_div_le_liminf_phi_div_log'`, `limsup_phi_div_log_le_three_div_log_one_div'`,
`limsup_phi_div_log_lt_top_and_liminf_phi_div_log_pos'` and
`tendsto_phi_div_log_nhds_zero_of_tendsto_nhds_zero'` with `sorry`. `comparator.json` names these
six theorems, `DenseSetsWithoutLargeSumsetsPalomar.Challenge` and
`DenseSetsWithoutLargeSumsetsPalomar.Solution` as the modules to compare, and `propext`,
`Classical.choice` and `Quot.sound` as the permitted axioms. The two modules sit in
`DenseSetsWithoutLargeSumsetsPalomar/` rather than at the root, so that they do not clash with the
`Challenge` and `Solution` modules of the projects this one requires.

## Build

The Lean, Mathlib, ChangFreimanRuzsa, SumOfSetsInSeveralDimensions, LargeSumsetsFromSubsets and
CountingSetsWithSmallSumset versions are pinned in `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The default build includes the library, challenge, and solution. The `sorry` warnings from
`Challenge.lean` are expected. LargeSumsetsFromSubsets is private for now, so Lake cannot fetch it
over HTTPS without credentials; a checkout at the pinned commit under `.lake/packages/` works.

CI also runs `scripts/check-lean-sources.py`, `scripts/validate-formalization.rb` and
`scripts/verify-comparator.sh`. The last one needs Linux with `bwrap`.
