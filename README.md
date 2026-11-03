# Dense sets without large sumsets

Lean 4 formalization of Gabriel Dahia, João Pedro Marciano and Victor Souza,
[*Dense sets without large sumsets*](https://arxiv.org/abs/2607.15269): for $0 < \delta < 1$ and
all large $n$ there is $S \subseteq \{1, \dots, n\}$ with $|S| \ge \delta n$ that contains no sumset
$A + B$ with $\min\{|A|, |B|\} \ge (3 + o(1)) \log n / \log(1 / \delta)$. The formalization also
covers the function $\varphi(\delta, N)$ of Kra, Moreira, Richter and Robertson,
[*Problems on infinite sumset configurations in the integers and beyond*](https://arxiv.org/abs/2311.06197),
Bull. Amer. Math. Soc. 62 (2025), 537–574: the lower bound of Felipe Hernández and Luke Hetzel,
Conjecture 4.10 and the negative answer to Question 4.12.

Write $[n] = \{1, \dots, n\}$ and $A + B = \{a + b : a \in A, b \in B\}$. For $0 \le \delta \le 1$,
the $\delta$-random subset $S_\delta$ of $[n]$ contains each element of $[n]$ independently with
probability $\delta$. In Lean its distribution is `ProbabilityTheory.setBernoulli (Set.Icc 1 n) δ`.
The function $\varphi(\delta, N)$ is the largest integer $k$ such that every $S \subseteq [N]$ with
$|S| \ge \delta N$ contains a sumset $A + B$ with $A, B \subseteq [N]$ and
$\min\{|A|, |B|\} \ge k$. This is the function of Kra, Moreira, Richter and Robertson. In Lean it is
`φ δ N`, with `δ : unitInterval`, and lemma names spell it `phi`. All Lean names below are in the
namespace `DenseSetsWithoutLargeSumsets`.

## Results

Theorems 1 and 2 are Theorem 1.1 and Corollary 1.2 of the paper. Theorem 3 is Corollary C of
Hernández and Hetzel,
[*On growth rates of infinite and finite sumsets*](https://arxiv.org/abs/2606.07310), which the
paper quotes for the lower bound of Corollary 1.2. Theorems 4 and 5 are Conjecture 4.10 and
Question 4.12 of Kra, Moreira, Richter and Robertson.

**Theorem 1** (`exists_dense_subset_forall_add_not_subset'`). Let $0 < \gamma \le 1$ and
$0 < c < 1$. If $n \ge n_0$ and $n^{-\alpha} < \delta \le 1 - c$, then some $S \subseteq [n]$ with
$|S| \ge \delta n$ contains no sumset $A + B$ with $A, B \subseteq [n]$ and

$$\min\{|A|, |B|\} \ge \frac{(3 + \gamma) \log n}{\log(1 / \delta)},$$

where

$$\alpha = \frac{\gamma}{\exp(\exp(10^4 / c))}, \qquad n_0 = \exp\left(\frac{\exp(10^5 / c)}{(\gamma T)^{16}}\right),$$

and $T$ is the constant `SimpleGraph.triangleRemovalBound` of the triangle removal lemma in Mathlib
at $\gamma^2 / \exp(3 \cdot 10^4 / c)$.

**Theorem 2** (`phi_div_log_mem_Icc'`). Let $\gamma$, $c$, $\alpha$ and $n_0$ be as in Theorem 1.
If $n \ge n_0$ and $n^{-\alpha} \le \delta \le 1 - c$, then

$$\frac{1 - \gamma}{\log(1 / \delta)} \le \frac{\varphi(\delta, n)}{\log n} \le \frac{3 + \gamma}{\log(1 / \delta)}.$$

**Theorem 3** (`one_div_log_one_div_le_liminf_phi_div_log'`). Let $0 < \delta < 1$. Then

$$\frac{1}{\log(1 / \delta)} \le \liminf_{N \to \infty} \frac{\varphi(\delta, N)}{\log N}.$$

**Theorem 4** (`limsup_phi_div_log_lt_top_and_liminf_phi_div_log_pos'`). Let $0 < \delta < 1$.
Then

$$\limsup_{N \to \infty} \frac{\varphi(\delta, N)}{\log N} < \infty \quad \text{and} \quad \liminf_{N \to \infty} \frac{\varphi(\delta, N)}{\log N} > 0,$$

with both limits taken in the extended reals. This is Conjecture 4.10. The conjecture is stated for
every $\delta > 0$. The range here is $0 < \delta < 1$ because $\varphi(1, N) = \lfloor N / 2 \rfloor$.

**Theorem 5** (`liminf_phi_div_log_eq_zero'`). Question 4.12 asks whether
$\liminf_N \varphi(\delta_N, N) / \log N > 0$ for some sequence $\delta_N \to 0$. It is not. Let
$(\delta_N)$ be a sequence in $[0, 1]$. If $\delta_N \to 0$, then

$$\liminf_{N \to \infty} \frac{\varphi(\delta_N, N)}{\log N} = 0.$$

[Challenge.lean](DenseSetsWithoutLargeSumsetsPalomar/Challenge.lean) states these five theorems
under the library names with a prime, with `sorry` placeholders, in terms of Mathlib and of the
definitions `φ`, `α` and `n₀`, the last two being $\alpha$ and $n_0$ above. The bounds on
$\gamma$, $c$ and $\delta$ are stated as membership in intervals such as `Set.Ioc 0 1`.
[Solution.lean](DenseSetsWithoutLargeSumsetsPalomar/Solution.lean) repeats `α` and `n₀` and
proves each statement from the library theorem without the prime, which takes the bounds as
separate hypotheses and writes $\alpha$ and $n_0$ as `explicitDensityExponent γ c` and
`exp (explicitLogThreshold γ c)`. The library and the solution contain no `sorry`, and the theorems
depend on no axioms other than `propext`, `Classical.choice` and `Quot.sound`.

The paper takes $\alpha$ small and $n$ large without giving values. The proof gives an exponent
`denseSubsetDensityExponent γ c` and a threshold on $n$ that are built from the constants of
Chang's theorem, of the theorem of Bollobás, Leader and Tiba and of Green's count. The library
states Theorem 1 with them as `eventually_forall_exists_dense_subset_without_large_sumsets` and
`dense_subset_without_large_sumsets`. It also proves Theorem 1.3 of the paper, the bound
$4 k^2 / n^{\gamma / (8 (\gamma + 3))}$ on the probability that $S_\delta$ contains $A + B$ with
$|A|, |B| \ge k = \lceil (3 + \gamma) \log n / \log(1 / \delta) \rceil$, as
`setBernoulli_real_pairEvent_le` and `eventually_pairEvent_probability_le`.
`ExplicitConstants.lean` bounds these constants by the expressions in $\gamma$ and $c$ above. The
constant of Bollobás, Leader and Tiba comes from the arithmetic removal lemma, so $n_0$ involves
the triangle removal constant $T$, which is of tower type.

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
  with a $t$-proper progression of dimension at most the Freiman dimension of the set,
  `ChangFreimanRuzsa.exists_tProperGAP_zmod_dim_le_freimanDim`, used here for $t = 2$. It uses
  Chang's lemma on large spectra from [APAP](https://github.com/YaelDillies/apap) and Minkowski's
  second theorem from [Tau Ceti](https://github.com/TauCetiProject/TauCeti).
- [LargeSumsetsFromSubsets](https://github.com/gdahia/LargeSumsetsFromSubsets): Theorem 2 of
  Bollobás, Leader and Tiba,
  [*Large sumsets from medium-sized subsets*](https://arxiv.org/abs/2206.09366), in the symmetric
  square-root form `LargeSumsetsFromSubsets.exists_subset_card_le_mul_sqrt_min_le_card_add`.
- [CountingSetsWithSmallSumset](https://github.com/gdahia/CountingSetsWithSmallSumset): Sections 3
  and 4 of Ben Green, *Counting sets with small sumset, and the clique number of random Cayley
  graphs*, Combinatorica 25 (2005), 307–326: Lemma 11, Proposition 18 and the bound for the members
  of a Freiman isomorphism class in an interval from the proof of Proposition 23.

## Files

| Files in `DenseSetsWithoutLargeSumsets/` | Contents |
| --- | --- |
| `Common.lean` | `interval`, `pairEvent`, the threshold $\lceil c \log n / \log(1 / \delta) \rceil$ |
| `Probability.lean` | The binomial random subset of a finite set, tail bounds for the binomial distribution |
| `Combinatorics/Additive/ProperGAP.lean` | The number of proper progressions (`ChangFreimanRuzsa.GAP` with `GAP.Proper`) of given dimension and size in `ZMod q` |
| `RandomSetContainsNoSmallSumset/` | Small sumsets (Section 2 of the paper) |
| `CountingSumsetsOfModerateSize/` | Moderate sumsets (Section 3) |
| `SimpleBoundForVeryLargeSumsets.lean` | Very large sumsets (Section 4) |
| `Combinatorics/SimpleGraph/TriangleRemovalBound.lean` | Monotonicity of the triangle removal constant of Mathlib, up to a factor $3/4$ |
| `ExplicitConstants.lean` | Bounds on the exponent and the threshold on $n$ of Theorems 1.1 and 1.3 by explicit expressions in $\gamma$ and $c$ |
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
`lake-manifest.json`. Mathlib is pinned to the commit that Tau Ceti `v4.35.0` pins, on Lean
`v4.35.0`.

```sh
lake exe cache get
lake build
```

The default build includes the library and the solution. `lake build Challenge` builds the
challenge, and its five `sorry` warnings are expected.

## Verification

`Challenge.lean` imports only the Mathlib module `Mathlib.Combinatorics.SimpleGraph.Triangle.Removal`.
It defines `φ`, `α` and `n₀` with Mathlib notions, and states the five theorems above with `sorry`.
[comparator.json](comparator.json) names these five theorems,
`DenseSetsWithoutLargeSumsetsPalomar.Challenge` and `DenseSetsWithoutLargeSumsetsPalomar.Solution`
as the modules to compare, and `propext`, `Classical.choice` and `Quot.sound` as the permitted
axioms. The two modules sit in `DenseSetsWithoutLargeSumsetsPalomar/` rather than at the root, so
that they do not clash with the `Challenge` and `Solution` modules of the projects this one
requires.

CI also runs `scripts/check-lean-sources.py`, `scripts/validate-formalization.rb` and
`scripts/verify-comparator.sh`. The last one needs Linux with `bwrap`.
