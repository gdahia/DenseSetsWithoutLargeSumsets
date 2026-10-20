/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib

/-!
# Dense sets without large sumsets

Theorem 1.1 and Corollary 1.2 of Gabriel Dahia, João Pedro Marciano and Victor Souza, *Dense sets
without large sumsets*, arXiv:2607.15269, Corollary C of Hernández and Hetzel, and the answers to
Conjecture 4.10 and Question 4.12 of Kra, Moreira, Richter and Robertson.

Write $[n] = \{1, \dots, n\}$. Kra, Moreira, Richter and Robertson define $\varphi(\delta, N)$ as
the largest integer $k$ such that every $S \subseteq [N]$ with $|S| \ge \delta N$ contains a
sumset $A + B$ with $A, B \subseteq [N]$ and $\min\{|A|, |B|\} \ge k$ (*Problems on infinite
sumset configurations in the integers and beyond*, Bull. Amer. Math. Soc. 62 (2025), 537–574,
Section 4.3).

The proofs are in `Solution.lean`.
-/

@[expose] public section

open Filter Real
open scoped Finset Pointwise

namespace DenseSetsWithoutLargeSumsets

noncomputable section

/-- The interval `[n] = {1, …, n}`. -/
def interval (n : ℕ) : Finset ℕ := Finset.Icc 1 n

/-- The set `S` contains a sumset `A + B` with `A, B ⊆ [n]` and `|A|, |B| ≥ k`. -/
def pairEvent (n k : ℕ) (S : Finset ℕ) : Prop :=
  ∃ A B : Finset ℕ,
    A ⊆ interval n ∧ B ⊆ interval n ∧ k ≤ A.card ∧ k ≤ B.card ∧ A + B ⊆ S

/-- The set of `k` such that every `S ⊆ [N]` with `|S| ≥ δ N` contains a sumset `B + C` with
`B, C ⊆ [N]` and `min {|B|, |C|} ≥ k`. -/
def sumsetThresholdSet (δ : unitInterval) (N : ℕ) : Set ℕ :=
  {k | ∀ S : Finset ℕ, S ⊆ interval N → (δ : ℝ) * (N : ℝ) ≤ (S.card : ℝ) → pairEvent N k S}

/-- `φ(δ, N)`, the largest integer `k` such that every `A ⊆ [N]` with `|A| ≥ δ N` contains a sumset
`B + C` with `B, C ⊆ [N]` and `min {|B|, |C|} ≥ k`. The set of such `k` contains `0` and is bounded
by `N`, so the supremum is attained. -/
def phi (δ : unitInterval) (N : ℕ) : ℕ := sSup (sumsetThresholdSet δ N)

end

/-- **Dense sets without large sumsets** (Theorem 1.1). For every $0 < \gamma \le 1$ and
$0 < c < 1$ there is $\alpha > 0$ such that, for all large $n$ and every
$n^{-\alpha} < \delta \le 1 - c$, some $S \subseteq [n]$ with $|S| \ge \delta n$ contains no sumset
$A + B$ with $A, B \subseteq [n]$ and $|A|, |B| \ge (3 + \gamma) \log n / \log(1 / \delta)$. -/
theorem exists_dense_subset_forall_add_not_subset' {γ c : ℝ} (hγ : 0 < γ) (hγ' : γ ≤ 1)
    (hc : 0 < c) (hc' : c < 1) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop, ∀ δ : ℝ, (n : ℝ) ^ (-α) < δ → δ ≤ 1 - c →
      ∃ S ⊆ Finset.Icc 1 n, δ * n ≤ #S ∧ ∀ A ⊆ Finset.Icc 1 n, ∀ B ⊆ Finset.Icc 1 n,
        ⌈(3 + γ) * log n / log (1 / δ)⌉₊ ≤ #A → ⌈(3 + γ) * log n / log (1 / δ)⌉₊ ≤ #B →
          ¬ A + B ⊆ S :=
  sorry

/-- **Corollary 1.2.** For every $0 < \gamma \le 1$ and $0 < c < 1$ there is $\alpha > 0$ such
that, for all large $n$ and every $n^{-\alpha} \le \delta \le 1 - c$,
$(1 - \gamma) / \log(1 / \delta) \le \varphi(\delta, n) / \log n$ and
$\varphi(\delta, n) / \log n \le (3 + \gamma) / \log(1 / \delta)$. -/
theorem exists_forall_phi_div_log_mem_Icc' {γ c : ℝ} (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c)
    (hc' : c < 1) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop, ∀ δ : unitInterval,
      (n : ℝ) ^ (-α) ≤ δ → (δ : ℝ) ≤ 1 - c →
        (phi δ n : ℝ) / log n ∈
          Set.Icc ((1 - γ) / log (1 / δ)) ((3 + γ) / log (1 / δ)) :=
  sorry

/-- **Corollary C of Hernández and Hetzel.** For fixed $0 < \delta < 1$,
$1 / \log(1 / \delta) \le \liminf_N \varphi(\delta, N) / \log N$. -/
theorem one_div_log_one_div_le_liminf_phi_div_log' {δ : unitInterval} (hδ : 0 < (δ : ℝ))
    (hδ' : (δ : ℝ) < 1) :
    1 / log (1 / δ) ≤ liminf (fun N : ℕ ↦ (phi δ N : ℝ) / log N) atTop :=
  sorry

/-- For fixed $0 < \delta < 1$, $\limsup_N \varphi(\delta, N) / \log N \le 3 / \log(1 / \delta)$.
-/
theorem limsup_phi_div_log_le_three_div_log_one_div' {δ : unitInterval} (hδ : 0 < (δ : ℝ))
    (hδ' : (δ : ℝ) < 1) :
    limsup (fun N : ℕ ↦ (phi δ N : ℝ) / log N) atTop ≤ 3 / log (1 / δ) :=
  sorry

/-- **Conjecture 4.10 of Kra, Moreira, Richter and Robertson.** For fixed $0 < \delta < 1$,
$\limsup_N \varphi(\delta, N) / \log N < \infty$ and $\liminf_N \varphi(\delta, N) / \log N > 0$.
Both limits are taken in the extended reals, as in the conjecture. The conjecture is stated for
every $\delta > 0$. The function $\varphi(\delta, N)$ is defined for $\delta \le 1$, and
$\varphi(1, N) = \lfloor N / 2 \rfloor$, so the range is $0 < \delta < 1$. -/
theorem limsup_phi_div_log_lt_top_and_liminf_phi_div_log_pos' {δ : unitInterval}
    (hδ : 0 < (δ : ℝ)) (hδ' : (δ : ℝ) < 1) :
    limsup (fun N : ℕ ↦ ((phi δ N / log N : ℝ) : EReal)) atTop < ⊤ ∧
      0 < liminf (fun N : ℕ ↦ ((phi δ N / log N : ℝ) : EReal)) atTop :=
  sorry

/-- **Question 4.12 of Kra, Moreira, Richter and Robertson** asks whether
$\liminf_N \varphi(\delta_N, N) / \log N > 0$ for some sequence $\delta_N \to 0$, for instance
$\delta_N = 1 / \log N$. It is not: $\varphi(\delta_N, N) / \log N \to 0$ for every sequence
$\delta_N \to 0$. -/
theorem tendsto_phi_div_log_nhds_zero_of_tendsto_nhds_zero' (δ : ℕ → unitInterval)
    (hδ : Tendsto (fun N : ℕ ↦ (δ N : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ ↦ (phi (δ N) N : ℝ) / log N) atTop (nhds 0) :=
  sorry

end DenseSetsWithoutLargeSumsets
