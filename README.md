# Dense sets without large sumsets

Lean 4 formalization of Gabriel Dahia, João Pedro Marciano and Victor Souza,
[*Dense sets without large sumsets*](https://arxiv.org/abs/2607.15269): for $0 < \delta < 1$ and
all large $n$ there is $S \subseteq \{1, \dots, n\}$ with $|S| \ge \delta n$ that contains no sumset
$A + B$ with $\min\{|A|, |B|\} \ge (3 + o(1)) \log n / \log(1 / \delta)$. The formalization also
covers the the lower bound of Felipe Hernández and Luke Hetzel function and the resolution of
Conjecture 4.10 and the negative answer to Question 4.12 of Kra, Moreira, Richter and Robertson,
[*Problems on infinite sumset configurations in the integers and beyond*](https://arxiv.org/abs/2311.06197),
Bull. Amer. Math. Soc. 62 (2025), 537–574.

## Results

Theorems 1 and 2 are Theorem 1.1 and Corollary 1.2 of the paper. Theorem 3 is Corollary C of
Hernández and Hetzel,
[*On growth rates of infinite and finite sumsets*](https://arxiv.org/abs/2606.07310), which the
paper quotes for the lower bound of Corollary 1.2. Theorems 4 and 5 are Conjecture 4.10 and
Question 4.12 of Kra, Moreira, Richter and Robertson.

**Theorem 1** (`exists_dense_subset_forall_add_not_subset'`). For every $0 < \gamma \le 1$ and
$0 < c < 1$, there exist $\alpha > 0$ and $n_0 \in \mathbb{N}$ such that the following holds.
If $n \ge n_0$ and $n^{-\alpha} < \delta \le 1 - c$, then some $S \subseteq [n]$ with
$|S| \ge \delta n$ contains no sumset $A + B$ with $A, B \subseteq [n]$ and

$$\min\{|A|, |B|\} \ge \frac{(3 + \gamma) \log n}{\log(1 / \delta)}.$$

**Theorem 2** (`phi_div_log_mem_Icc'`). Let $\gamma$, $c$, $\alpha$ and $n_0$ be as in Theorem 1.
If $n \ge n_0$ and $n^{-\alpha} \le \delta \le 1 - c$, then

$$\frac{1 - \gamma}{\log(1 / \delta)} \le \frac{\varphi(\delta, n)}{\log n} \le \frac{3 + \gamma}{\log(1 / \delta)}.$$

**Theorem 3** (`one_div_log_one_div_le_liminf_phi_div_log'`). For all $0 < \delta < 1$, we have

$$\frac{1}{\log(1 / \delta)} \le \liminf_{N \to \infty} \frac{\varphi(\delta, N)}{\log N}.$$

**Theorem 4** (`limsup_phi_div_log_lt_top_and_liminf_phi_div_log_pos'`). For all $0 < \delta < 1$,
we have

$$\limsup_{N \to \infty} \frac{\varphi(\delta, N)}{\log N} < \infty \quad \text{and} \quad \liminf_{N \to \infty} \frac{\varphi(\delta, N)}{\log N} > 0.$$

**Theorem 5** (`liminf_phi_div_log_eq_zero'`). Question 4.12 asks whether
$\liminf_N \varphi(\delta_N, N) / \log N > 0$ for some sequence $\delta_N \to 0$. It is not. Let
$(\delta_N)$ be a sequence in $[0, 1]$. If $\delta_N \to 0$, then

$$\liminf_{N \to \infty} \frac{\varphi(\delta_N, N)}{\log N} = 0.$$

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
axioms.

CI also runs `scripts/check-lean-sources.py`, `scripts/validate-formalization.rb` and
`scripts/verify-comparator.sh`. The last one needs Linux with `bwrap`.
