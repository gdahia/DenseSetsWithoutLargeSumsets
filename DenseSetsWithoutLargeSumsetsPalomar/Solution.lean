/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module -- shake: keep-all

public import Mathlib.Probability.Distributions.SetBernoulli
public import DenseSetsWithoutLargeSumsets.SumsetThreshold.Basic
import DenseSetsWithoutLargeSumsets.DenseSubsetsWithoutLargeSumsets
import DenseSetsWithoutLargeSumsets.SumsetThreshold.Growth
import DenseSetsWithoutLargeSumsets.SumsetThreshold.VanishingDensity

/-!
# Dense sets without large sumsets

The statements of `Challenge.lean`, proved by the results of the library with the same names
without the prime. The library states Theorem 1.3 with `pairEvent` and `pairCardThreshold`, which
unfold to the statement here.
-/

public section

open Filter ProbabilityTheory Real
open scoped Finset Pointwise

namespace DenseSetsWithoutLargeSumsets

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
  exists_dense_subset_forall_add_not_subset hγ hγ' hc hc'

/-- **Corollary 1.2.** For `0 < γ ≤ 1` and `0 < c < 1` there is `α > 0` such that, for all large
`n` and every `n ^ (-α) ≤ δ ≤ 1 - c`,
`(1 - γ) / log (1 / δ) ≤ φ(δ, n) / log n ≤ (3 + γ) / log (1 / δ)`. -/
theorem exists_forall_phi_div_log_mem_Icc' {γ c : ℝ} (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c)
    (hc' : c < 1) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop, ∀ δ : unitInterval,
      (n : ℝ) ^ (-α) ≤ δ → (δ : ℝ) ≤ 1 - c →
        (phi δ n : ℝ) / log n ∈
          Set.Icc ((1 - γ) / log (1 / δ)) ((3 + γ) / log (1 / δ)) :=
  exists_forall_phi_div_log_mem_Icc hγ hγ' hc hc'

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
  exists_forall_setBernoulli_real_pairEvent_le hγ hγ' hc hc'

/-! ### The lower bound of Hernández and Hetzel -/

/-- **Corollary C of Hernández and Hetzel.** For fixed `0 < δ < 1`,
`1 / log (1 / δ) ≤ liminf φ(δ, N) / log N`. -/
theorem one_div_log_one_div_le_liminf_phi_div_log' {δ : unitInterval} (hδ : 0 < (δ : ℝ))
    (hδ' : (δ : ℝ) < 1) :
    1 / log (1 / δ) ≤ liminf (fun N : ℕ ↦ (phi δ N : ℝ) / log N) atTop :=
  one_div_log_one_div_le_liminf_phi_div_log hδ hδ'

/-! ### Conjecture 4.10 and Question 4.12 of Kra, Moreira, Richter and Robertson -/

/-- **Conjecture 4.10 of Kra, Moreira, Richter and Robertson.** For fixed `0 < δ < 1`,
`limsup φ(δ, N) / log N < ∞` and `liminf φ(δ, N) / log N > 0`, with both limits taken in the
extended reals. The conjecture is stated for every `δ > 0`; it fails for `δ = 1`, where
`φ(1, N) = N / 2`. -/
theorem limsup_phi_div_log_lt_top_and_liminf_phi_div_log_pos' {δ : unitInterval}
    (hδ : 0 < (δ : ℝ)) (hδ' : (δ : ℝ) < 1) :
    limsup (fun N : ℕ ↦ ((phi δ N / log N : ℝ) : EReal)) atTop < ⊤ ∧
      0 < liminf (fun N : ℕ ↦ ((phi δ N / log N : ℝ) : EReal)) atTop :=
  limsup_phi_div_log_lt_top_and_liminf_phi_div_log_pos hδ hδ'

/-- **Question 4.12 of Kra, Moreira, Richter and Robertson** asks whether
`liminf φ(δ_N, N) / log N > 0` for some sequence `δ_N → 0`. It is not: the limit inferior is `0`
for every sequence `δ_N → 0`. -/
theorem liminf_phi_div_log_eq_zero' (δ : ℕ → unitInterval)
    (hδ : Tendsto (fun N : ℕ ↦ (δ N : ℝ)) atTop (nhds 0)) :
    liminf (fun N : ℕ ↦ (phi (δ N) N : ℝ) / log N) atTop = 0 :=
  liminf_phi_div_log_eq_zero δ hδ

end DenseSetsWithoutLargeSumsets
