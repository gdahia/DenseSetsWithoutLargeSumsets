# DenseSetsWithoutLargeSumsets

This repository contains the Lean 4 formalization of
[**Dense sets without large sumsets**](https://arxiv.org/abs/2607.15269), by Gabriel Dahia,
João Pedro Marciano, and Victor Souza.

The main result constructs dense subsets of $[n]$ which contain no sumset $A + B$ when both
summands are sufficiently large. The formalization includes the probabilistic construction and
the estimates for small, moderate, and very large sumsets which are combined in the final
theorem `DenseSetsWithoutLargeSumsets.dense_subset_without_large_sumsets`.

Following the introduction of the paper, `DenseSetsWithoutLargeSumsets.phi` is the threshold
function $\varphi(\delta, N)$: the largest integer $k$ such that *every* $A \subseteq [N]$ with
$|A| \ge \delta N$ contains a sumset $B + C$ with $B, C \subseteq [N]$ and
$\min\{|B|, |C|\} \ge k$. Both directions formalized here are bounds on $\varphi$, and the main
theorem takes the asymptotic form
`DenseSetsWithoutLargeSumsets.limsup_phi_mul_log_div_log_le_three`:

$$\limsup_{N \to \infty} \frac{\varphi(\delta, N) \log (1 / \delta)}{\log N} \le 3
\qquad \text{for every fixed } \delta \in (0, 1).$$

It bounds the $\limsup$ rather than only the $\liminf$ because the construction produces a dense
sumset-free subset of $[N]$ for *every* sufficiently large $N$.

## Corollary 1.2: Conjecture 4.10 and Question 4.12

Corollary 1.2 of *Dense sets without large sumsets* combines Theorem 1.1 with a lower bound of
Hernández and Hetzel to sandwich $\varphi$,

$$\frac{1 - \gamma}{\log(1/\delta)} \le \frac{\varphi(\delta, n)}{\log n}
\le \frac{3 + \gamma}{\log(1/\delta)} ,$$

which settles Conjecture 4.10 and answers Question 4.12 of [*Problems on infinite sumset
configurations in the integers and beyond*](https://arxiv.org/abs/2311.06197), by Bryna Kra, Joel
Moreira, Florian K. Richter and Donald Robertson (Bull. Amer. Math. Soc. **62** (2025), 537–574),
in the negative.

This repository formalizes the **upper** half of that sandwich — the half supplied by Theorem 1.1 —
and the two readings of it that the corollary highlights. The lower half is quoted in the paper from
Hernández and Hetzel and is not formalized here; the Zarankiewicz reduction listed below is the
project's own lower bound instead.

**Conjecture 4.10, upper half.** At a fixed $\delta \in (0,1)$,
`DenseSetsWithoutLargeSumsets.limsup_phi_div_log_le` gives
$\limsup_N \varphi(\delta, N)/\log N \le 4/\log(1/\delta) < \infty$.

**Question 4.12.** It asks whether $\liminf_N \varphi(\delta_N, N)/\log N > 0$ for some sequence
$\delta_N \to 0$, and specifically whether one can take $\delta_N = 1/\log N$. Both parts are
negative, because the bound costs a factor $\log(1/\delta)$ which blows up as $\delta \to 0$.
Since $\varphi$ is monotone in the density (`DenseSetsWithoutLargeSumsets.phi_mono`), a vanishing
sequence can be compared against a small *constant* density, so the conclusion holds for **every**
$\delta_N \to 0$ and not only those in the range $\delta \ge n^{-\alpha}$ of Corollary 1.2:

- `DenseSetsWithoutLargeSumsets.tendsto_phi_div_log_atTop_nhds_zero` — for every $\delta_N \to 0$
  the whole limit $\lim_N \varphi(\delta_N, N)/\log N$ is $0$;
  `DenseSetsWithoutLargeSumsets.liminf_phi_div_log_eq_zero` states the question verbatim, so the
  $\liminf$ is $0$ and never positive.
- `DenseSetsWithoutLargeSumsets.liminf_phi_logDensity_div_log_eq_zero` — one cannot take
  $\delta_N = 1/\log N$. Here `DenseSetsWithoutLargeSumsets.logDensity` is $1/\log N$ clamped
  into $[0, 1]$, which for $N \ge 3$ is $1/\log N$ on the nose.
- `DenseSetsWithoutLargeSumsets.eventually_phi_logDensity_lt_log_div_log_log` — the rate for that
  sequence: $\varphi(1/\log N, N) < 4 \log N / \log\log N$ for all large $N$.

Question 4.11 of the same paper, on whether $\lim_N \varphi(\delta, N)/\log N$ exists, is left
open there and is not addressed here.

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
- A reduction of the complementary *lower* bound — every sufficiently dense $S \subseteq [n]$
  does contain a sumset $A + B$ with $\min\{|A|, |B|\} \ge k$ — to Mathlib's Zarankiewicz
  function, obtained by encoding $[n]$ in base $\lfloor\sqrt{n}\rfloor + 1$ as a bipartite
  relation (`DenseSetsWithoutLargeSumsets.exists_pairEvent_of_zarankiewicz_lt`).  Read through
  $\varphi$, this is the lower bound `DenseSetsWithoutLargeSumsets.le_phi_of_zarankiewicz_lt`.

## Build

Build the project:

```bash
lake exe cache get
lake build
```
