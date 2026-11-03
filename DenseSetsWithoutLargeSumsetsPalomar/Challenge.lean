/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Probability.Distributions.SetBernoulli

/-!
# Dense sets without large sumsets

Theorems 1.1 and 1.3 and Corollary 1.2 of Dahia, Marciano and Souza, *Dense sets without large
sumsets*, arXiv:2607.15269. Corollary C of Hernández and Hetzel, *On growth rates of infinite and
finite sumsets*, arXiv:2606.07310. Conjecture 4.10 and Question 4.12 of Kra, Moreira, Richter and
Robertson, *Problems on infinite sumset configurations in the integers and beyond*, Bull. Amer.
Math. Soc. 62 (2025), 537–574, whose function `φ(δ, N)` is `phi δ N`. The `δ`-random subset of
`[n]` has distribution `setBernoulli (Set.Icc 1 n) δ`. The proofs are in `Solution.lean`.
-/

@[expose] public section

open Filter ProbabilityTheory Real
open scoped Finset Pointwise

namespace DenseSetsWithoutLargeSumsets

/-- `φ(δ, N)`, the largest integer `k` such that every `S ⊆ [N]` with `|S| ≥ δ N` contains a sumset
`A + B` with `A, B ⊆ [N]` and `min {|A|, |B|} ≥ k`. -/
noncomputable def phi (δ : unitInterval) (N : ℕ) : ℕ :=
  sSup {k | ∀ S ⊆ Finset.Icc 1 N, (δ : ℝ) * N ≤ #S → ∃ A B : Finset ℕ,
    A ⊆ Finset.Icc 1 N ∧ B ⊆ Finset.Icc 1 N ∧ k ≤ #A ∧ k ≤ #B ∧ A + B ⊆ S}

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
        (setBernoulli (Set.Icc 1 n) δ).real ((↑) '' {S : Finset ℕ | ∃ A B : Finset ℕ,
            A ⊆ Finset.Icc 1 n ∧ B ⊆ Finset.Icc 1 n ∧ ⌈(3 + γ) * log n / log (1 / δ)⌉₊ ≤ #A ∧
              ⌈(3 + γ) * log n / log (1 / δ)⌉₊ ≤ #B ∧ A + B ⊆ S}) ≤
          4 * ⌈(3 + γ) * log n / log (1 / δ)⌉₊ ^ 2 / n ^ (γ / (8 * (γ + 3))) :=
  sorry

/-! ### The lower bound of Hernández and Hetzel -/

/-- **Corollary C of Hernández and Hetzel.** For fixed `0 < δ < 1`,
`1 / log (1 / δ) ≤ liminf φ(δ, N) / log N`. -/
theorem one_div_log_one_div_le_liminf_phi_div_log' {δ : unitInterval} (hδ : 0 < (δ : ℝ))
    (hδ' : (δ : ℝ) < 1) :
    1 / log (1 / δ) ≤ liminf (fun N : ℕ ↦ (phi δ N : ℝ) / log N) atTop :=
  sorry

/-! ### Conjecture 4.10 and Question 4.12 of Kra, Moreira, Richter and Robertson -/

/-- **Conjecture 4.10 of Kra, Moreira, Richter and Robertson.** For fixed `0 < δ < 1`,
`limsup φ(δ, N) / log N < ∞` and `liminf φ(δ, N) / log N > 0`, with both limits taken in the
extended reals. The conjecture is stated for every `δ > 0`; it fails for `δ = 1`, where
`φ(1, N) = N / 2`. -/
theorem limsup_phi_div_log_lt_top_and_liminf_phi_div_log_pos' {δ : unitInterval}
    (hδ : 0 < (δ : ℝ)) (hδ' : (δ : ℝ) < 1) :
    limsup (fun N : ℕ ↦ ((phi δ N / log N : ℝ) : EReal)) atTop < ⊤ ∧
      0 < liminf (fun N : ℕ ↦ ((phi δ N / log N : ℝ) : EReal)) atTop :=
  sorry

/-- **Question 4.12 of Kra, Moreira, Richter and Robertson** asks whether
`liminf φ(δ_N, N) / log N > 0` for some sequence `δ_N → 0`. It is not: the limit inferior is `0`
for every sequence `δ_N → 0`. -/
theorem liminf_phi_div_log_eq_zero' (δ : ℕ → unitInterval)
    (hδ : Tendsto (fun N : ℕ ↦ (δ N : ℝ)) atTop (nhds 0)) :
    liminf (fun N : ℕ ↦ (phi (δ N) N : ℝ) / log N) atTop = 0 :=
  sorry

end DenseSetsWithoutLargeSumsets
