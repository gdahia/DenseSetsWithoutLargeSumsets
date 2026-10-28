/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Probability.Distributions.SetBernoulli

/-!
# Dense sets without large sumsets

Theorems 1.1, 1.3 and 3.1, Corollaries 1.2, 3.3 and 4.3 and Lemmas 2.1 and 4.1 of Dahia, Marciano
and Souza, *Dense sets without large sumsets*, arXiv:2607.15269. Corollary C of Hernández and
Hetzel, *On growth rates of infinite and finite sumsets*, arXiv:2606.07310, with its finitary
forms. Conjecture 4.10 and Question 4.12 of Kra, Moreira, Richter and Robertson, *Problems on
infinite sumset configurations in the integers and beyond*, Bull. Amer. Math. Soc. 62 (2025),
537–574, whose function `φ(δ, N)` is `phi δ N`. The `δ`-random subset of `[n]` has distribution
`setBernoulli (Set.Icc 1 n) δ`. The proofs are in `Solution.lean`.
-/

@[expose] public section

open Filter ProbabilityTheory Real
open scoped Finset Pointwise

namespace DenseSetsWithoutLargeSumsets

noncomputable section

/-- The interval `[n] = {1, …, n}`. -/
def interval (n : ℕ) : Finset ℕ := Finset.Icc 1 n

/-- The set `S` contains a sumset `A + B` with `A, B ⊆ [n]`, `|A| = |B| = k` and
`lb ≤ |A + B| ≤ ub`. -/
def pairSumsetIsSubset (n k : ℕ) (lb ub : ℝ) (S : Finset ℕ) : Prop :=
  ∃ A B : Finset ℕ, A ⊆ interval n ∧ B ⊆ interval n ∧ A.card = k ∧ B.card = k ∧
      lb ≤ (A + B).card ∧ (A + B).card ≤ ub ∧ A + B ⊆ S

/-- The set `S` contains a sumset `A + B` with `A, B ⊆ [n]` and `|A|, |B| ≥ k`. -/
def pairEvent (n k : ℕ) (S : Finset ℕ) : Prop :=
  ∃ A B : Finset ℕ,
    A ⊆ interval n ∧ B ⊆ interval n ∧ k ≤ A.card ∧ k ≤ B.card ∧ A + B ⊆ S

/-- The threshold `⌈c * log n / log (1 / δ)⌉`. -/
def pairCardThreshold (c : ℝ) (n : ℕ) (δ : unitInterval) : ℕ :=
  Nat.ceil (c * Real.log (n : ℝ) / Real.log (1 / δ))

/-- The sets `A + B` with `A, B ⊆ [n]`, `|A| = |B| = k` and `|A + B| ≤ m`. -/
def pairSumsetsFamily (n k m : ℕ) : Set (Finset ℕ) :=
  {Y : Finset ℕ |
    Y ⊆ interval (2 * n) ∧
      ∃ A B : Finset ℕ,
        A ⊆ interval n ∧ B ⊆ interval n ∧
          #A = k ∧ #B = k ∧ A + B = Y ∧ #Y ≤ m}

/-- The set `S` contains a sumset `A + B` with `A, B ⊆ [n]`, `|A| = |B| = k` and
`C * k < |A + B| < k * (k + 1) / 2`. -/
def moderateSumsetEvent (n k : ℕ) (C : ℝ) (S : Finset ℕ) : Prop :=
  ∃ A B : Finset ℕ,
    A ⊆ interval n ∧ B ⊆ interval n ∧ #A = k ∧ #B = k ∧
      C * (k : ℝ) < (#(A + B) : ℝ) ∧
        #(A + B) < k * (k + 1) / 2 ∧ A + B ⊆ S

/-- The set `S` contains a sumset `A + B` with `A, B ⊆ [n]`, `|A| = |B| = k` and
`|A + B| ≥ (k + 1) * k / 2`. -/
def veryLargeSumsetEvent (n k : ℕ) (S : Finset ℕ) : Prop :=
  ∃ A B : Finset ℕ,
    A ⊆ interval n ∧ B ⊆ interval n ∧ #A = k ∧ #B = k ∧
      (k + 1) * k / 2 ≤ #(A + B) ∧ A + B ⊆ S

/-- The set of `k` such that every `S ⊆ [N]` with `|S| ≥ δ N` contains a sumset `B + C` with
`B, C ⊆ [N]` and `min {|B|, |C|} ≥ k`. -/
def sumsetThresholdSet (δ : unitInterval) (N : ℕ) : Set ℕ :=
  {k | ∀ S : Finset ℕ, S ⊆ interval N → (δ : ℝ) * (N : ℝ) ≤ (S.card : ℝ) → pairEvent N k S}

/-- `φ(δ, N)`, the largest integer `k` such that every `A ⊆ [N]` with `|A| ≥ δ N` contains a sumset
`B + C` with `B, C ⊆ [N]` and `min {|B|, |C|} ≥ k`. -/
def phi (δ : unitInterval) (N : ℕ) : ℕ := sSup (sumsetThresholdSet δ N)

end

/-! ### Dense sets without large sumsets -/

/-- **Theorem 1.1.** For `0 < γ ≤ 1` and `0 < c < 1` there is `α > 0` such that, for all large `n`
and every `n ^ (-α) < δ ≤ 1 - c`, some `S ⊆ [n]` with `|S| ≥ δ n` contains no sumset `A + B` with
`A, B ⊆ [n]` and `|A|, |B| ≥ (3 + γ) * log n / log (1 / δ)`. -/
theorem exists_dense_subset_forall_add_not_subset' {γ c : ℝ} (hγ : 0 < γ) (hγ' : γ ≤ 1)
    (hc : 0 < c) (hc' : c < 1) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop, ∀ δ : ℝ, (n : ℝ) ^ (-α) < δ → δ ≤ 1 - c →
      ∃ S ⊆ Finset.Icc 1 n, δ * n ≤ #S ∧ ∀ A ⊆ Finset.Icc 1 n, ∀ B ⊆ Finset.Icc 1 n,
        ⌈(3 + γ) * log n / log (1 / δ)⌉₊ ≤ #A → ⌈(3 + γ) * log n / log (1 / δ)⌉₊ ≤ #B →
          ¬ A + B ⊆ S :=
  sorry

/-- **Corollary 1.2.** For `0 < γ ≤ 1` and `0 < c < 1` there is `α > 0` such that, for all large
`n` and every `n ^ (-α) ≤ δ ≤ 1 - c`,
`(1 - γ) / log (1 / δ) ≤ φ(δ, n) / log n ≤ (3 + γ) / log (1 / δ)`. -/
theorem exists_forall_phi_div_log_mem_Icc' {γ c : ℝ} (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c)
    (hc' : c < 1) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop, ∀ δ : unitInterval,
      (n : ℝ) ^ (-α) ≤ δ → (δ : ℝ) ≤ 1 - c →
        (phi δ n : ℝ) / log n ∈
          Set.Icc ((1 - γ) / log (1 / δ)) ((3 + γ) / log (1 / δ)) :=
  sorry

/-- **Theorem 1.3.** For `0 < γ ≤ 1` and `0 < c < 1` there is `α > 0` such that, for all large
`n`, every `n ^ (-α) < δ ≤ 1 - c` and `k = ⌈(3 + γ) * log n / log (1 / δ)⌉`, the `δ`-random subset
of `[n]` contains a sumset `A + B` with `A, B ⊆ [n]` and `|A|, |B| ≥ k` with probability at most
`4 * k ^ 2 / n ^ (γ / (8 * (γ + 3)))`. -/
theorem exists_forall_setBernoulli_real_pairEvent_le' {γ c : ℝ} (hγ : 0 < γ) (hγ' : γ ≤ 1)
    (hc : 0 < c) (hc' : c < 1) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop, ∀ δ : unitInterval, (n : ℝ) ^ (-α) < δ →
      (δ : ℝ) ≤ 1 - c →
        (setBernoulli (Set.Icc 1 n) δ).real
            ((↑) '' {S : Finset ℕ | pairEvent n (pairCardThreshold (3 + γ) n δ) S}) ≤
          4 * pairCardThreshold (3 + γ) n δ ^ 2 / n ^ (γ / (8 * (γ + 3))) :=
  sorry

/-- **Lemma 2.1.** Let `0 < γ ≤ 1`, `C > 1` and `c > 0`. There is `α > 0` such that, for all large
`n`, every `n ^ (-α) < δ ≤ 1 - c` and `k = ⌈(3 + γ) * log n / log (1 / δ)⌉`, the `δ`-random subset
of `[n]` contains a sumset `A + B` with `A, B ⊆ [n]`, `|A| = |B| = k` and `|A + B| ≤ C * k` with
probability at most `2 * k / n ^ (γ / (8 * (γ + 2)))`. -/
theorem exists_forall_setBernoulli_real_pairSumsetIsSubset_le' {γ C c : ℝ} (hγ : 0 < γ)
    (hγ' : γ ≤ 1) (hC : 1 < C) (hc : 0 < c) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop, ∀ δ : unitInterval, (n : ℝ) ^ (-α) < δ →
      (δ : ℝ) ≤ 1 - c →
        (setBernoulli (Set.Icc 1 n) δ).real
            ((↑) '' {S : Finset ℕ | pairSumsetIsSubset n (pairCardThreshold (3 + γ) n δ) 0
              (C * pairCardThreshold (3 + γ) n δ) S}) ≤
          2 * pairCardThreshold (3 + γ) n δ / n ^ (γ / (8 * (γ + 2))) :=
  sorry

/-- **Theorem 3.1.** If `m < k * (k + 1) / 2`, then the number of sets `A + B` with `A, B ⊆ [n]`,
`|A| = |B| = k` and `|A + B| ≤ m` is at most `n ^ (2 * m / k + 1) * k ^ (24 * k)`. -/
theorem pairSumsetsFamily_ncard_le' (n k m : ℕ) (hm : m < k * (k + 1) / 2) :
    ((pairSumsetsFamily n k m).ncard : ℝ) ≤
        (n : ℝ) ^ (2 * (m : ℝ) / (k : ℝ) + 1) * (k : ℝ) ^ (24 * k) :=
  sorry

/-- **Theorem 3.1**, second part. If moreover `k ≥ 2 ^ 9000` and `m ≤ k ^ (1 + c)` with
`c ≤ 2⁻⁸`, then the number of these sets is at most
`n ^ (2 * m / k + 1) * (6 * e * m / k) ^ (6 * k) * exp (k ^ (1 - 2 * c))`. -/
theorem pairSumsetsFamily_ncard_le_of_small_sumset' (n k m : ℕ) (c : ℝ)
    (hm : m < k * (k + 1) / 2)
    (hc_le : c ≤ 1 / (2 : ℝ) ^ (8 : ℕ))
    (hk_threshold : 2 ^ 9000 ≤ k)
    (hm_small : (m : ℝ) ≤ (k : ℝ) ^ (1 + c)) :
    ((pairSumsetsFamily n k m).ncard : ℝ) ≤
      (n : ℝ) ^ (2 * (m : ℝ) / (k : ℝ) + 1) *
        ((6 * Real.exp 1 * (m : ℝ)) / (k : ℝ)) ^ (6 * k) *
          Real.exp ((k : ℝ) ^ (1 - 2 * c)) :=
  sorry

/-- **Corollary 3.3.** For `0 < γ ≤ 2` and `0 < c < 1` there are `C > 1` and `α > 0` such that,
for `n ≥ 2`, every `n ^ (-α) < δ ≤ 1 - c` and `k = ⌈(2 + γ) * log n / log (1 / δ)⌉`, the
`δ`-random subset of `[n]` contains a sumset `A + B` with `A, B ⊆ [n]`, `|A| = |B| = k` and
`C * k < |A + B| < k * (k + 1) / 2` with probability at most `2 * k ^ 2 / n ^ (γ * C / 2)`. -/
theorem exists_forall_setBernoulli_real_moderateSumsetEvent_le' {γ c : ℝ} (hγ : 0 < γ)
    (hγ' : γ ≤ 2) (hc : 0 < c) (hc' : c < 1) :
    ∃ C α : ℝ, 1 < C ∧ 0 < α ∧ ∀ n : ℕ, 2 ≤ n → ∀ δ : unitInterval, (n : ℝ) ^ (-α) < δ →
      (δ : ℝ) ≤ 1 - c →
        (setBernoulli (Set.Icc 1 n) δ).real
            ((↑) '' {S : Finset ℕ | moderateSumsetEvent n (pairCardThreshold (2 + γ) n δ) C S}) ≤
          2 * pairCardThreshold (2 + γ) n δ ^ 2 / n ^ (γ * C / 2) :=
  sorry

/-- **Lemma 4.1.** Let `0 < γ ≤ 1`, `c > 0` and `k = ⌈(3 + γ) * log n / log (1 / δ)⌉`. For all large
`n` and every `n ^ (-1 / 2) < δ ≤ 1 - c`, the `δ`-random subset of `[n]` contains a sumset `A + B`
with `A, B ⊆ [n]`, `|A| = |B| = k` and `|A + B| ≥ (k + 1) * k / 2` with probability at most
`k ^ 2 / n ^ (γ * k / 3)`. -/
theorem eventually_forall_setBernoulli_real_veryLargeSumsetEvent_le' {γ c : ℝ} (hγ : 0 < γ)
    (hγ' : γ ≤ 1) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ δ : unitInterval, (n : ℝ) ^ (-(1 / 2 : ℝ)) < δ →
      (δ : ℝ) ≤ 1 - c →
        (setBernoulli (Set.Icc 1 n) δ).real
            ((↑) '' {S : Finset ℕ | veryLargeSumsetEvent n (pairCardThreshold (3 + γ) n δ) S}) ≤
          pairCardThreshold (3 + γ) n δ ^ 2 / n ^ (γ * pairCardThreshold (3 + γ) n δ / 3) :=
  sorry

/-- **Corollary 4.3.** There are at most `n ^ (k + m / k) * (k ^ 3).choose k` pairs `(A, B)` of
`k`-subsets of `[n]` with `|A + B| ≤ m`. -/
theorem pair_small_sumset_family_card_le' (n k m : ℕ) :
    {p : Finset ℕ × Finset ℕ |
      p.1 ⊆ interval n ∧ p.2 ⊆ interval n ∧
        #p.1 = k ∧ #p.2 = k ∧ #(p.1 + p.2) ≤ m}.ncard ≤
      n ^ (k + m / k) * (k ^ 3).choose k :=
  sorry

/-! ### The lower bound of Hernández and Hetzel -/

/-- **Corollary C of Hernández and Hetzel.** For fixed `0 < δ < 1`,
`1 / log (1 / δ) ≤ liminf φ(δ, N) / log N`. -/
theorem one_div_log_one_div_le_liminf_phi_div_log' {δ : unitInterval} (hδ : 0 < (δ : ℝ))
    (hδ' : (δ : ℝ) < 1) :
    1 / log (1 / δ) ≤ liminf (fun N : ℕ ↦ (phi δ N : ℝ) / log N) atTop :=
  sorry

/-- Corollary C of Hernández and Hetzel for all large `N`: for fixed `0 < δ < 1` and `γ > 0`,
`(1 - γ) / log (1 / δ) ≤ φ(δ, N) / log N` for all large `N`. -/
theorem eventually_div_log_le_phi_div_log' {γ : ℝ} {δ : unitInterval} (hδ_pos : 0 < (δ : ℝ))
    (hδ_lt : (δ : ℝ) < 1) (hγ : 0 < γ) :
    ∀ᶠ N : ℕ in atTop, (1 - γ) / log (1 / δ) ≤ (phi δ N : ℝ) / log N :=
  sorry

/-- Corollary C of Hernández and Hetzel, uniformly in the density: for `γ > 0` and `0 < c < 1`,
for all large `n` and every `n ^ (-(γ / 4)) ≤ δ ≤ 1 - c`,
`(1 - γ) * log n / log (1 / δ) ≤ φ(δ, n)`. -/
theorem eventually_forall_log_div_log_le_phi' {γ c : ℝ} (hγ : 0 < γ) (hc₀ : 0 < c) (hc : c < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ δ : unitInterval, (n : ℝ) ^ (-(γ / 4)) ≤ δ → (δ : ℝ) ≤ 1 - c →
      (1 - γ) * log n / log (1 / δ) ≤ phi δ n :=
  sorry

/-! ### Conjecture 4.10 and Question 4.12 of Kra, Moreira, Richter and Robertson -/

/-- For fixed `0 < δ < 1`, `limsup φ(δ, N) / log N ≤ 3 / log (1 / δ)`. -/
theorem limsup_phi_div_log_le_three_div_log_one_div' {δ : unitInterval} (hδ : 0 < (δ : ℝ))
    (hδ' : (δ : ℝ) < 1) :
    limsup (fun N : ℕ ↦ (phi δ N : ℝ) / log N) atTop ≤ 3 / log (1 / δ) :=
  sorry

/-- **Conjecture 4.10 of Kra, Moreira, Richter and Robertson.** For fixed `0 < δ < 1`,
`limsup φ(δ, N) / log N < ∞` and `liminf φ(δ, N) / log N > 0`, with both limits taken in the
extended reals. The conjecture is stated for every `δ > 0`; it fails for `δ = 1`, where
`φ(1, N) = N / 2`. -/
theorem limsup_phi_div_log_lt_top_and_liminf_phi_div_log_pos' {δ : unitInterval}
    (hδ : 0 < (δ : ℝ)) (hδ' : (δ : ℝ) < 1) :
    limsup (fun N : ℕ ↦ ((phi δ N / log N : ℝ) : EReal)) atTop < ⊤ ∧
      0 < liminf (fun N : ℕ ↦ ((phi δ N / log N : ℝ) : EReal)) atTop :=
  sorry

/-- The lower half of Conjecture 4.10 with the limit in the reals: for fixed `0 < δ < 1`,
`liminf φ(δ, N) / log N > 0`. -/
theorem liminf_phi_div_log_pos' {δ : unitInterval} (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) :
    0 < liminf (fun N : ℕ ↦ (phi δ N : ℝ) / log N) atTop :=
  sorry

/-- Conjecture 4.10 for all large `N`: for fixed `0 < δ < 1` there are `c > 0` and `C` with
`c * log N ≤ φ(δ, N) ≤ C * log N` for all large `N`. -/
theorem exists_mul_log_le_phi_le_mul_log' {δ : unitInterval} (hδ_pos : 0 < (δ : ℝ))
    (hδ_lt : (δ : ℝ) < 1) :
    ∃ c C : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * log N ≤ phi δ N ∧ (phi δ N : ℝ) ≤ C * log N :=
  sorry

/-- **Question 4.12 of Kra, Moreira, Richter and Robertson** asks whether
`liminf φ(δ_N, N) / log N > 0` for some sequence `δ_N → 0`, for instance `δ_N = 1 / log N`. It is
not: `φ(δ_N, N) / log N → 0` for every sequence `δ_N → 0`. -/
theorem tendsto_phi_div_log_nhds_zero_of_tendsto_nhds_zero' (δ : ℕ → unitInterval)
    (hδ : Tendsto (fun N : ℕ ↦ (δ N : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ ↦ (phi (δ N) N : ℝ) / log N) atTop (nhds 0) :=
  sorry

/-- Question 4.12 as asked: for every sequence `δ_N → 0`, `liminf φ(δ_N, N) / log N = 0`. -/
theorem liminf_phi_div_log_eq_zero' (δ : ℕ → unitInterval)
    (hδ : Tendsto (fun N : ℕ ↦ (δ N : ℝ)) atTop (nhds 0)) :
    liminf (fun N : ℕ ↦ (phi (δ N) N : ℝ) / log N) atTop = 0 :=
  sorry

/-- The rate for `δ_N = 1 / log N` in Question 4.12: if `δ_N = 1 / log N` for all large `N`, then
`φ(δ_N, N) < 4 * log N / log (log N)` for all large `N`. -/
theorem eventually_phi_lt_log_div_log_log' (δ : ℕ → unitInterval)
    (hδ : ∀ᶠ N : ℕ in atTop, (δ N : ℝ) = 1 / log N) :
    ∀ᶠ N : ℕ in atTop, (phi (δ N) N : ℝ) < 4 * log N / log (log N) :=
  sorry

end DenseSetsWithoutLargeSumsets
