# Dense sets without large sumsets

Lean 4 formalization of Gabriel Dahia, João Pedro Marciano and Victor Souza,
[*Dense sets without large sumsets*](https://arxiv.org/abs/2607.15269): for $0 < \delta < 1$ and
all large $n$ there is $S \subseteq \{1, \dots, n\}$ with $|S| \ge \delta n$ that contains no sumset
$A + B$ with $\min\{|A|, |B|\} \ge (3 + o(1)) \log n / \log(1 / \delta)$. The formalization also
covers the function $\varphi(\delta, N)$ of Kra, Moreira, Richter and Robertson,
[*Problems on infinite sumset configurations in the integers and beyond*](https://arxiv.org/abs/2311.06197),
Bull. Amer. Math. Soc. 62 (2025), 537–574: Corollary 1.2 of the paper, the lower bound of Felipe
Hernández and Luke Hetzel with its finitary forms, Conjecture 4.10 and the negative answer to
Question 4.12.

Write $[n] = \{1, \dots, n\}$ and $A + B = \{a + b : a \in A, b \in B\}$. For $0 \le \delta \le 1$,
the $\delta$-random subset $S_\delta$ of $[n]$ contains each element of $[n]$ independently with
probability $\delta$. In Lean its distribution is `ProbabilityTheory.setBernoulli (Set.Icc 1 n) δ`.
For $\tau > 0$, write $k_\tau = \lceil \tau \log n / \log(1 / \delta) \rceil$, which is
`pairCardThreshold τ n δ` in Lean. The function $\varphi(\delta, N)$ is the largest integer $k$ such
that every $S \subseteq [N]$ with $|S| \ge \delta N$ contains a sumset $A + B$ with
$A, B \subseteq [N]$ and $\min\{|A|, |B|\} \ge k$. In Lean it is `phi δ N`, with
`δ : unitInterval`. All Lean names below are in the namespace `DenseSetsWithoutLargeSumsets`.

## Results

Theorems 1 to 9 are results of the paper: Theorem 1 is its Theorem 1.1, Theorem 2 its
Corollary 1.2, Theorem 3 its Theorem 1.3, Theorem 4 its Lemma 2.1, Theorems 5 and 6 its
Theorem 3.1, Theorem 7 its Corollary 3.3, Theorem 8 its Lemma 4.1 and Theorem 9 its Corollary 4.3.
Theorem 10 is Corollary C of Hernández and Hetzel,
[*On growth rates of infinite and finite sumsets*](https://arxiv.org/abs/2606.07310), which the
paper quotes for the lower bound of Corollary 1.2, and Theorems 11 and 12 are finitary forms of it.
Theorems 13 to 16 concern Conjecture 4.10 of Kra, Moreira, Richter and Robertson, and Theorems 17
to 19 their Question 4.12.

**Theorem 1** (`exists_dense_subset_forall_add_not_subset'`). Let $0 < \gamma \le 1$ and
$0 < c < 1$. Then there is $\alpha > 0$ such that, for all large $n$ and every
$n^{-\alpha} < \delta \le 1 - c$, some $S \subseteq [n]$ with $|S| \ge \delta n$ contains no sumset
$A + B$ with $A, B \subseteq [n]$ and

$$\min\{|A|, |B|\} \ge \frac{(3 + \gamma) \log n}{\log(1 / \delta)}.$$

**Theorem 2** (`exists_forall_phi_div_log_mem_Icc'`). Let $0 < \gamma \le 1$ and $0 < c < 1$. Then
there is $\alpha > 0$ such that, for all large $n$ and every $n^{-\alpha} \le \delta \le 1 - c$,

$$\frac{1 - \gamma}{\log(1 / \delta)} \le \frac{\varphi(\delta, n)}{\log n} \le \frac{3 + \gamma}{\log(1 / \delta)}.$$

**Theorem 3** (`exists_forall_setBernoulli_real_pairEvent_le'`). Let $0 < \gamma \le 1$ and
$0 < c < 1$. Then there is $\alpha > 0$ such that, for all large $n$ and every
$n^{-\alpha} < \delta \le 1 - c$,

$$\mathbb{P}\big(A + B \subseteq S_\delta \text{ for some } A, B \subseteq [n] \text{ with } |A|, |B| \ge k\big) \le \frac{4 k^2}{n^{\gamma / (8 (\gamma + 3))}},$$

where $k = k_{3 + \gamma}$.

**Theorem 4** (`exists_forall_setBernoulli_real_pairSumsetIsSubset_le'`). Let $0 < \gamma \le 1$,
$C > 1$ and $c > 0$. Then there is $\alpha > 0$ such that, for all large $n$ and every
$n^{-\alpha} < \delta \le 1 - c$,

$$\mathbb{P}\big(A + B \subseteq S_\delta \text{ for some } A, B \subseteq [n] \text{ with } |A| = |B| = k \text{ and } |A + B| \le C k\big) \le \frac{2 k}{n^{\gamma / (8 (\gamma + 2))}},$$

where $k = k_{3 + \gamma}$.

**Theorem 5** (`pairSumsetsFamily_ncard_le'`). Let $n, k, m$ be natural numbers. If
$m < k (k + 1) / 2$, then the number of sets $A + B$ with $A, B \subseteq [n]$, $|A| = |B| = k$ and
$|A + B| \le m$ is at most

$$n^{2 m / k + 1} k^{24 k}.$$

**Theorem 6** (`pairSumsetsFamily_ncard_le_of_small_sumset'`). Let $n, k, m$ be natural numbers and
$\xi \le 2^{-8}$ a real number, called `c` in Lean. If $m < k (k + 1) / 2$, $k \ge 2^{9000}$ and
$m \le k^{1 + \xi}$, then the number of sets of Theorem 5 is at most

$$n^{2 m / k + 1} \left(\frac{6 e m}{k}\right)^{6 k} \exp\big(k^{1 - 2 \xi}\big).$$

**Theorem 7** (`exists_forall_setBernoulli_real_moderateSumsetEvent_le'`). Let $0 < \gamma \le 2$
and $0 < c < 1$. Then there are $C > 1$ and $\alpha > 0$ such that, for every $n \ge 2$ and every
$n^{-\alpha} < \delta \le 1 - c$,

$$\mathbb{P}\big(A + B \subseteq S_\delta \text{ for some } A, B \subseteq [n] \text{ with } |A| = |B| = k \text{ and } C k < |A + B| < k (k + 1) / 2\big) \le \frac{2 k^2}{n^{\gamma C / 2}},$$

where $k = k_{2 + \gamma}$.

**Theorem 8** (`eventually_forall_setBernoulli_real_veryLargeSumsetEvent_le'`). Let
$0 < \gamma \le 1$ and $c > 0$. Then, for all large $n$ and every $n^{-1/2} < \delta \le 1 - c$,

$$\mathbb{P}\big(A + B \subseteq S_\delta \text{ for some } A, B \subseteq [n] \text{ with } |A| = |B| = k \text{ and } |A + B| \ge k (k + 1) / 2\big) \le \frac{k^2}{n^{\gamma k / 3}},$$

where $k = k_{3 + \gamma}$.

**Theorem 9** (`pair_small_sumset_family_card_le'`). Let $n, k, m$ be natural numbers. Then the
number of pairs $(A, B)$ with $A, B \subseteq [n]$, $|A| = |B| = k$ and $|A + B| \le m$ is at most

$$n^{k + \lfloor m / k \rfloor} \binom{k^3}{k}.$$

**Theorem 10** (`one_div_log_one_div_le_liminf_phi_div_log'`). Let $0 < \delta < 1$. Then

$$\frac{1}{\log(1 / \delta)} \le \liminf_{N \to \infty} \frac{\varphi(\delta, N)}{\log N}.$$

**Theorem 11** (`eventually_div_log_le_phi_div_log'`). Let $0 < \delta < 1$ and $\gamma > 0$. Then,
for all large $N$,

$$\frac{1 - \gamma}{\log(1 / \delta)} \le \frac{\varphi(\delta, N)}{\log N}.$$

**Theorem 12** (`eventually_forall_log_div_log_le_phi'`). Let $\gamma > 0$ and $0 < c < 1$. Then,
for all large $n$ and every $n^{-\gamma / 4} \le \delta \le 1 - c$,

$$\frac{(1 - \gamma) \log n}{\log(1 / \delta)} \le \varphi(\delta, n).$$

**Theorem 13** (`limsup_phi_div_log_le_three_div_log_one_div'`). Let $0 < \delta < 1$. Then

$$\limsup_{N \to \infty} \frac{\varphi(\delta, N)}{\log N} \le \frac{3}{\log(1 / \delta)}.$$

**Theorem 14** (`limsup_phi_div_log_lt_top_and_liminf_phi_div_log_pos'`). Let $0 < \delta < 1$.
Then

$$\limsup_{N \to \infty} \frac{\varphi(\delta, N)}{\log N} < \infty \quad \text{and} \quad \liminf_{N \to \infty} \frac{\varphi(\delta, N)}{\log N} > 0,$$

with both limits taken in the extended reals. This is Conjecture 4.10. The conjecture is stated for
every $\delta > 0$. The range here is $0 < \delta < 1$ because $\varphi(1, N) = \lfloor N / 2 \rfloor$.

**Theorem 15** (`liminf_phi_div_log_pos'`). Let $0 < \delta < 1$. Then, with the limit taken in the
reals,

$$\liminf_{N \to \infty} \frac{\varphi(\delta, N)}{\log N} > 0.$$

**Theorem 16** (`exists_mul_log_le_phi_le_mul_log'`). Let $0 < \delta < 1$. Then there are $c > 0$
and $C$ such that, for all large $N$,

$$c \log N \le \varphi(\delta, N) \le C \log N.$$

**Theorem 17** (`tendsto_phi_div_log_nhds_zero_of_tendsto_nhds_zero'`). Question 4.12 asks whether
$\liminf_N \varphi(\delta_N, N) / \log N > 0$ for some sequence $\delta_N \to 0$, for instance
$\delta_N = 1 / \log N$. It is not. Let $(\delta_N)$ be a sequence in $[0, 1]$. If $\delta_N \to 0$,
then

$$\frac{\varphi(\delta_N, N)}{\log N} \to 0.$$

**Theorem 18** (`liminf_phi_div_log_eq_zero'`). Let $(\delta_N)$ be a sequence in $[0, 1]$. If
$\delta_N \to 0$, then

$$\liminf_{N \to \infty} \frac{\varphi(\delta_N, N)}{\log N} = 0.$$

**Theorem 19** (`eventually_phi_lt_log_div_log_log'`). Let $(\delta_N)$ be a sequence in $[0, 1]$.
If $\delta_N = 1 / \log N$ for all large $N$, then, for all large $N$,

$$\varphi(\delta_N, N) < \frac{4 \log N}{\log \log N}.$$

[Challenge.lean](DenseSetsWithoutLargeSumsetsPalomar/Challenge.lean) states these nineteen theorems
under the library names with a prime, with `sorry` placeholders, in terms of Mathlib and of the
definitions `interval`, `pairSumsetIsSubset`, `pairEvent`, `pairCardThreshold`,
`pairSumsetsFamily`, `moderateSumsetEvent`, `veryLargeSumsetEvent`, `sumsetThresholdSet` and `phi`.
[Solution.lean](DenseSetsWithoutLargeSumsetsPalomar/Solution.lean) proves each statement by the
library theorem without the prime. The library and the solution contain no `sorry`, and the
theorems depend on no axioms other than `propext`, `Classical.choice` and `Quot.sound`.

In the library, the constants of Theorems 1, 3, 4 and 7 are explicit. Theorems 1 and 3 hold with
$\alpha$ `denseSubsetDensityExponent γ c`, Theorem 4 with $\alpha$ `lowerDensityExponent C γ`, and
Theorem 7 with $C$ `moderateSumsetGapConstant γ c` and $\alpha$ `moderateSumsetDensityExponent γ c`.
The exponents depend on constants of the Lake dependencies, so `Challenge.lean` quantifies them,
and with them the constant $C$ of Theorem 7. The library has further statements. The main ones are the following.

| Declaration | Statement |
| --- | --- |
| `eventually_forall_exists_dense_subset_without_large_sumsets`, `dense_subset_without_large_sumsets` | Theorem 1.1 with the explicit exponent `denseSubsetDensityExponent γ c`, for every $\delta$ and for a sequence $\delta_n$ |
| `eventually_pairEvent_probability_le` | Theorem 1.3 with the explicit exponent, for the random subset as a measure on finite sets |
| `small_sumset_pair_probability_le`, `moderate_sumset_probability_le`, `very_large_sumset_probability_le` | Lemma 2.1, Corollary 3.3 and Lemma 4.1 with explicit constants and thresholds on $n$ |
| `eventually_forall_phi_lt_log_div_log` | The upper bound of Corollary 1.2 with the explicit exponent |
| `pairEvent_of_lt_density` | If $S \subseteq [n]$, $\|S\| \ge \delta n$, $1 \le k$, $1 \le m \le n$ and $(k - 1)^{1 / k} (1 + m / n) m^{-1 / k} + k / n < \delta$, then $S$ contains $A + B$ with $A, B \subseteq [n]$ and $\|A\|, \|B\| \ge k$ |
| `largeSubsets_exists_zmodGAPPreimageContainer` | Large subsets $A_0 \subseteq A$ and $B_0 \subseteq B$ of sets with $\|A + B\| \le C k$ lie in the preimage of a proper progression of `ZMod q` of bounded size and of dimension at most the Freiman dimension of $A_0 \cup B_0$ |
| `card_boundedFreimanDimSets`, `smallSumsetFreimanDimSets_ncard_le` | Lemma 3.2: the number of sets $X \subseteq [n]$ with $\|X\| = t$ and Freiman dimension at most $r$, and of those with $\|X + X\| \le s$ |

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

The lower bound of Theorem 10 is not proved as in Hernández and Hetzel, who use a finitary
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
  `CountingSumsetsOfModerateSize/BoundedFreimanDimSets.lean` proves Lemma 3.2 of the paper,
  `card_boundedFreimanDimSets` and `smallSumsetFreimanDimSets_ncard_le`.

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

## Build

The Lean, Mathlib, ChangFreimanRuzsa, SumOfSetsInSeveralDimensions, LargeSumsetsFromSubsets and
CountingSetsWithSmallSumset versions are pinned in `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The default build includes the library and the solution. `lake build Challenge` builds the
challenge, and its nineteen `sorry` warnings are expected. LargeSumsetsFromSubsets is private for
now, so Lake cannot fetch it over HTTPS without credentials; a checkout at the pinned commit under
`.lake/packages/` works.

## Verification

`Challenge.lean` imports only the Mathlib module `Mathlib.Probability.Distributions.SetBernoulli`.
It repeats the library definitions of `interval`, `pairSumsetIsSubset`, `pairEvent`,
`pairCardThreshold`, `pairSumsetsFamily`, `moderateSumsetEvent`, `veryLargeSumsetEvent`,
`sumsetThresholdSet` and `phi` and states the nineteen theorems above with `sorry`.
[comparator.json](comparator.json) names these nineteen theorems,
`DenseSetsWithoutLargeSumsetsPalomar.Challenge` and `DenseSetsWithoutLargeSumsetsPalomar.Solution`
as the modules to compare, and `propext`, `Classical.choice` and `Quot.sound` as the permitted
axioms. The two modules sit in `DenseSetsWithoutLargeSumsetsPalomar/` rather than at the root, so
that they do not clash with the `Challenge` and `Solution` modules of the projects this one
requires.

CI also runs `scripts/check-lean-sources.py`, `scripts/validate-formalization.rb` and
`scripts/verify-comparator.sh`. The last one needs Linux with `bwrap`.
