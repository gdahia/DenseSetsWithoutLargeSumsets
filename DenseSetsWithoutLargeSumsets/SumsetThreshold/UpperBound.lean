/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DenseSetsWithoutLargeSumsets.DenseSubsetsWithoutLargeSumsets
public import DenseSetsWithoutLargeSumsets.SumsetThreshold.Basic

/-!
# The upper bound for `φ(δ, N)`

A set `S ⊆ [N]` with `|S| ≥ δ N` and no sumset `A + B` with `|A|, |B| ≥ k` shows that
`φ(δ, N) < k`. So the main theorem, Theorem 1.1 of *Dense sets without large sumsets*, is the
upper bound `φ(δ, n) < (3 + γ) * log n / log (1 / δ)` for all large `n` and all
`n ^ (-α) < δ ≤ 1 - c`.

## Main statements

* `eventually_forall_phi_lt_log_div_log`: the bound above.
* `limsup_phi_mul_log_div_log_le_three`: `limsup φ(δ, N) * log (1 / δ) / log N ≤ 3` for fixed
  `0 < δ < 1`.
* `limsup_phi_div_log_le_three_div_log_one_div`: `limsup φ(δ, N) / log N ≤ 3 / log (1 / δ)` for
  fixed `0 < δ < 1`.
-/

public section

namespace DenseSetsWithoutLargeSumsets

open Filter Real

variable {γ c : ℝ} {δ : unitInterval}

/-- For all large `n` and every `δ` with `n ^ (-α) < δ ≤ 1 - c`, where
`α = denseSubsetDensityExponent γ c`, we have `φ(δ, n) < (3 + γ) * log n / log (1 / δ)`. -/
lemma eventually_forall_phi_lt_log_div_log (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hc_pos : 0 < c)
    (hc_lt : c < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ δ : unitInterval,
      (n : ℝ) ^ (-denseSubsetDensityExponent γ c) < δ → (δ : ℝ) ≤ 1 - c →
        (phi δ n : ℝ) < (3 + γ) * log n / log (1 / δ) := by
  filter_upwards [eventually_forall_exists_dense_subset_without_large_sumsets hγ_pos hγ_le hc_pos
    hc_lt] with n hn δ hδ hδ'
  exact Nat.lt_ceil.mp (phi_lt_of_existsDenseSetWithoutLargeSumsets
    (k := pairCardThreshold (3 + γ) n δ) (hn δ hδ hδ'))

/-- The bound `φ(δ n, n) < (3 + γ) * log n / log (1 / δ n)` along a sequence of densities. -/
lemma eventually_phi_lt_log_div_log (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hc_pos : 0 < c)
    (hc_lt : c < 1) (δ : ℕ → unitInterval)
    (hδ_lower : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-denseSubsetDensityExponent γ c) < δ n)
    (hδ_upper : ∀ᶠ n : ℕ in atTop, (δ n : ℝ) ≤ 1 - c) :
    ∀ᶠ n : ℕ in atTop, (phi (δ n) n : ℝ) < (3 + γ) * log n / log (1 / δ n) := by
  filter_upwards [eventually_forall_phi_lt_log_div_log hγ_pos hγ_le hc_pos hc_lt, hδ_lower,
    hδ_upper] with n hn h₁ h₂ using hn _ h₁ h₂

lemma log_one_div_nonneg (δ : unitInterval) : 0 ≤ log (1 / δ) := by
  rw [one_div, log_inv]
  exact neg_nonneg.2 (log_nonpos (unitInterval.nonneg δ) (unitInterval.le_one δ))

lemma phi_mul_log_div_log_nonneg (δ : unitInterval) (N : ℕ) :
    0 ≤ (phi δ N : ℝ) * log (1 / δ) / log N :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg _) (log_one_div_nonneg δ)) (log_natCast_nonneg N)

/-- For fixed `0 < δ < 1` and all large `N`, `φ(δ, N) * log (1 / δ) / log N ≤ 3 + γ`. -/
lemma eventually_phi_mul_log_div_log_le (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1)
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) :
    ∀ᶠ N : ℕ in atTop, (phi δ N : ℝ) * log (1 / δ) / log N ≤ 3 + γ := by
  have hα := denseSubsetDensityExponent_pos hγ_pos (sub_pos.2 hδ_lt) (sub_lt_self 1 hδ_pos)
  filter_upwards [eventually_forall_phi_lt_log_div_log hγ_pos hγ_le (sub_pos.2 hδ_lt)
      (sub_lt_self 1 hδ_pos),
    tendsto_natCast_atTop_atTop.eventually
      ((tendsto_rpow_neg_atTop hα).eventually_lt_const hδ_pos),
    eventually_ge_atTop 2] with N hN hδN hN₂
  rw [div_le_iff₀ (log_pos (mod_cast hN₂))]
  exact ((lt_div_iff₀ (log_one_div_pos hδ_pos hδ_lt)).mp (hN δ hδN (sub_sub_cancel 1 _).ge)).le

/-- For fixed `0 < δ < 1`, `limsup φ(δ, N) * log (1 / δ) / log N ≤ 3`. -/
lemma limsup_phi_mul_log_div_log_le_three (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) :
    limsup (fun N : ℕ ↦ (phi δ N : ℝ) * log (1 / δ) / log N) atTop ≤ 3 := by
  refine le_of_forall_gt_imp_ge_of_dense ?_
  intro a ha
  refine limsup_le_of_le (isCoboundedUnder_le_of_le _ (phi_mul_log_div_log_nonneg δ)) ?_
  filter_upwards [eventually_phi_mul_log_div_log_le hδ_pos hδ_lt (γ := min (a - 3) 1)
    (lt_min (by linarith) one_pos) (min_le_right _ _)] with N hN
  linarith [min_le_left (a - 3) (1 : ℝ)]

/-- For fixed `0 < δ < 1` and all large `N`, `φ(δ, N) / log N ≤ (3 + γ) / log (1 / δ)`. -/
lemma eventually_phi_div_log_le (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) (hγ_pos : 0 < γ)
    (hγ_le : γ ≤ 1) :
    ∀ᶠ N : ℕ in atTop, (phi δ N : ℝ) / log N ≤ (3 + γ) / log (1 / δ) := by
  filter_upwards [eventually_phi_mul_log_div_log_le hδ_pos hδ_lt hγ_pos hγ_le] with N hN
  rwa [le_div_iff₀ (log_one_div_pos hδ_pos hδ_lt), div_mul_eq_mul_div]

/-- For fixed `0 < δ < 1`, the ratio `φ(δ, N) / log N` is bounded above. -/
lemma isBoundedUnder_le_phi_div_log (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) :
    IsBoundedUnder (· ≤ ·) atTop fun N : ℕ ↦ (phi δ N : ℝ) / log N :=
  isBoundedUnder_of_eventually_le (eventually_phi_div_log_le hδ_pos hδ_lt one_pos le_rfl)

/-- For fixed `0 < δ < 1`, `limsup φ(δ, N) / log N ≤ 3 / log (1 / δ)`. -/
theorem limsup_phi_div_log_le_three_div_log_one_div (hδ_pos : 0 < (δ : ℝ))
    (hδ_lt : (δ : ℝ) < 1) :
    limsup (fun N : ℕ ↦ (phi δ N : ℝ) / log N) atTop ≤ 3 / log (1 / δ) := by
  have hℓ := log_one_div_pos hδ_pos hδ_lt
  refine le_of_forall_gt_imp_ge_of_dense ?_
  intro a ha
  rw [div_lt_iff₀ hℓ] at ha
  refine limsup_le_of_le (isCoboundedUnder_le_of_le _ (phi_div_log_nonneg δ)) ?_
  filter_upwards [eventually_phi_div_log_le hδ_pos hδ_lt (γ := min (a * log (1 / δ) - 3) 1)
    (lt_min (by linarith) one_pos) (min_le_right _ _)] with N hN
  exact hN.trans ((div_le_iff₀ hℓ).2 (by linarith [min_le_left (a * log (1 / δ) - 3) (1 : ℝ)]))

end DenseSetsWithoutLargeSumsets
