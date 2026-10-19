/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DenseSetsWithoutLargeSumsets.DenseSubsetsWithoutLargeSumsets
public import DenseSetsWithoutLargeSumsets.SumsetThreshold.Growth
public import DenseSetsWithoutLargeSumsets.SumsetThreshold.VanishingDensity

/-!
# Dense sets without large sumsets: proofs

Proofs of the statements of `Challenge.lean` from the library. The definitions `interval` and
`pairEvent` are those of `Common.lean`, and `sumsetThresholdSet` and `phi` those of
`SumsetThreshold/Basic.lean`.
-/

public section

open Filter Real
open scoped Finset Pointwise

namespace DenseSetsWithoutLargeSumsets

/-- **Dense sets without large sumsets** (Theorem 1.1). For every `0 < γ ≤ 1` and `0 < c < 1`
there is `α > 0` such that, for all large `n` and every `n ^ (-α) < δ ≤ 1 - c`, some `S ⊆ [n]`
with `|S| ≥ δ n` contains no sumset `A + B` with `A, B ⊆ [n]` and
`|A|, |B| ≥ (3 + γ) * log n / log (1 / δ)`. -/
theorem exists_dense_subset_forall_add_not_subset {γ c : ℝ} (hγ : 0 < γ) (hγ' : γ ≤ 1)
    (hc : 0 < c) (hc' : c < 1) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop, ∀ δ : ℝ, (n : ℝ) ^ (-α) < δ → δ ≤ 1 - c →
      ∃ S ⊆ Finset.Icc 1 n, δ * n ≤ #S ∧ ∀ A ⊆ Finset.Icc 1 n, ∀ B ⊆ Finset.Icc 1 n,
        ⌈(3 + γ) * log n / log (1 / δ)⌉₊ ≤ #A → ⌈(3 + γ) * log n / log (1 / δ)⌉₊ ≤ #B →
          ¬ A + B ⊆ S := by
  refine ⟨denseSubsetDensityExponent γ c, denseSubsetDensityExponent_pos hγ hc hc', ?_⟩
  filter_upwards [eventually_forall_exists_dense_subset_without_large_sumsets hγ hγ' hc hc']
    with n hn δ hδ hδ'
  obtain ⟨S, hS, hcard, hfree⟩ :=
    hn ⟨δ, (rpow_nonneg n.cast_nonneg _).trans hδ.le, by linarith⟩ hδ hδ'
  exact ⟨S, hS, hcard, fun A hA B hB hA' hB' hAB ↦ hfree ⟨A, B, hA, hB, hA', hB', hAB⟩⟩

/-- **Corollary 1.2.** For every `0 < γ ≤ 1` and `0 < c < 1` there is `α > 0` such that, for all
large `n` and every `n ^ (-α) ≤ δ ≤ 1 - c`,
`(1 - γ) / log (1 / δ) ≤ φ(δ, n) / log n ≤ (3 + γ) / log (1 / δ)`. -/
theorem exists_forall_phi_div_log_mem_Icc {γ c : ℝ} (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c)
    (hc' : c < 1) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop, ∀ δ : unitInterval,
      (n : ℝ) ^ (-α) ≤ δ → (δ : ℝ) ≤ 1 - c →
        (phi δ n : ℝ) / log n ∈
          Set.Icc ((1 - γ) / log (1 / δ)) ((3 + γ) / log (1 / δ)) :=
  exists_forall_div_log_le_phi_div_log_le hγ hγ' hc hc'

/-- **Corollary C of Hernández and Hetzel.** For fixed `0 < δ < 1`,
`1 / log (1 / δ) ≤ liminf φ(δ, N) / log N`. -/
theorem one_div_log_one_div_le_liminf_phi_div_log {δ : unitInterval} (hδ : 0 < (δ : ℝ))
    (hδ' : (δ : ℝ) < 1) :
    1 / log (1 / δ) ≤ liminf (fun N : ℕ ↦ (phi δ N : ℝ) / log N) atTop :=
  one_div_log_le_liminf_phi_div_log hδ hδ'

/-- For fixed `0 < δ < 1`, `limsup φ(δ, N) / log N ≤ 3 / log (1 / δ)`. -/
theorem limsup_phi_div_log_le_three_div_log_one_div {δ : unitInterval} (hδ : 0 < (δ : ℝ))
    (hδ' : (δ : ℝ) < 1) :
    limsup (fun N : ℕ ↦ (phi δ N : ℝ) / log N) atTop ≤ 3 / log (1 / δ) :=
  limsup_phi_div_log_le hδ hδ'

/-- **Conjecture 4.10 of Kra, Moreira, Richter and Robertson.** For fixed `0 < δ < 1`,
`limsup φ(δ, N) / log N < ∞` and `liminf φ(δ, N) / log N > 0`. Both limits are taken in the
extended reals, as in the conjecture. The conjecture is stated for every `δ > 0`; the function
`φ(δ, N)` is defined for `δ ≤ 1`, and `φ(1, N) = ⌊N / 2⌋`, so the range is `0 < δ < 1`. -/
theorem limsup_phi_div_log_lt_top_and_liminf_phi_div_log_pos {δ : unitInterval}
    (hδ : 0 < (δ : ℝ)) (hδ' : (δ : ℝ) < 1) :
    limsup (fun N : ℕ ↦ ((phi δ N / log N : ℝ) : EReal)) atTop < ⊤ ∧
      0 < liminf (fun N : ℕ ↦ ((phi δ N / log N : ℝ) : EReal)) atTop :=
  limsup_lt_top_and_liminf_pos_phi_div_log hδ hδ'

/-- **Question 4.12 of Kra, Moreira, Richter and Robertson** asks whether
`liminf φ(δ_N, N) / log N > 0` for some sequence `δ_N → 0`, for instance `δ_N = 1 / log N`. It is
not: `φ(δ_N, N) / log N → 0` for every sequence `δ_N → 0`. -/
theorem tendsto_phi_div_log_nhds_zero_of_tendsto_nhds_zero (δ : ℕ → unitInterval)
    (hδ : Tendsto (fun N : ℕ ↦ (δ N : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ ↦ (phi (δ N) N : ℝ) / log N) atTop (nhds 0) :=
  tendsto_phi_div_log_atTop_nhds_zero δ hδ

end DenseSetsWithoutLargeSumsets
