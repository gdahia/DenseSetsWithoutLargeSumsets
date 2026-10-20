/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DenseSetsWithoutLargeSumsets.SumsetThreshold.Basic
import DenseSetsWithoutLargeSumsets.SumsetThreshold.UpperBound
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# `φ(δ_N, N)` for densities tending to zero

Question 4.12 of Kra, Moreira, Richter and Robertson (*Problems on infinite sumset configurations
in the integers and beyond*, arXiv:2311.06197) asks whether `liminf φ(δ_N, N) / log N > 0` for some
sequence `δ_N → 0`, and whether one can take `δ_N = 1 / log N`. The answer to both is negative:
`φ(δ_N, N) / log N → 0` for every sequence `δ_N → 0`.

For a fixed `0 < y < 1` the upper bound gives `φ(y, N) / log N ≤ 4 / log (1 / y)` for all large
`N`, and `φ(δ_N, N) ≤ φ(y, N)` as soon as `δ_N ≤ y`. The right side tends to `0` as `y → 0`.

## Main definitions

* `logDensity N`: the density `1 / log N`, as an element of the unit interval.

## Main statements

* `tendsto_phi_div_log_nhds_zero_of_tendsto_nhds_zero`: `φ(δ_N, N) / log N → 0` for every
  `δ_N → 0`.
* `liminf_phi_div_log_eq_zero`: the `liminf` of Question 4.12 is `0`.
* `liminf_phi_logDensity_div_log_eq_zero`: the same for `δ_N = 1 / log N`.
* `eventually_phi_logDensity_lt_log_div_log_log`: `φ(1 / log N, N) < 4 * log N / log (log N)` for
  all large `N`.
-/

@[expose] public section

namespace DenseSetsWithoutLargeSumsets

open Filter Real

/-- If `δ_N → 0` and `0 < y < 1`, then `φ(δ_N, N) / log N ≤ 4 / log (1 / y)` for all large `N`. -/
lemma eventually_phi_div_log_le_of_tendsto (δ : ℕ → unitInterval)
    (hδ : Tendsto (fun N : ℕ ↦ (δ N : ℝ)) atTop (nhds 0)) {y : unitInterval}
    (hy_pos : 0 < (y : ℝ)) (hy_lt : (y : ℝ) < 1) :
    ∀ᶠ N : ℕ in atTop, (phi (δ N) N : ℝ) / log N ≤ 4 / log (1 / y) := by
  filter_upwards [hδ.eventually_lt_const hy_pos,
    eventually_phi_div_log_le hy_pos hy_lt one_pos le_rfl] with N hN hy
  rw [(by norm_num : (3 + 1 : ℝ) = 4)] at hy
  exact (div_le_div_of_nonneg_right (Nat.cast_le.2 (phi_mono hN.le))
    (log_natCast_nonneg N)).trans hy

/-- For every sequence of densities `δ_N → 0`, `φ(δ_N, N) / log N → 0`. -/
theorem tendsto_phi_div_log_nhds_zero_of_tendsto_nhds_zero (δ : ℕ → unitInterval)
    (hδ : Tendsto (fun N : ℕ ↦ (δ N : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ ↦ (phi (δ N) N : ℝ) / log N) atTop (nhds 0) := by
  refine tendsto_order.mpr
    ⟨fun a ha ↦ .of_forall fun N ↦ ha.trans_le (phi_div_log_nonneg _ _), ?_⟩
  intro a ha
  have hy : 4 / log (1 / exp (-(8 / a))) < a := by
    rw [one_div, log_inv, log_exp, neg_neg, div_div_eq_mul_div, div_lt_iff₀ (by norm_num)]
    linarith
  have hexp : exp (-(8 / a)) < 1 := exp_lt_one_iff.2 (neg_lt_zero.2 (by positivity))
  filter_upwards [eventually_phi_div_log_le_of_tendsto δ hδ
    (y := ⟨exp (-(8 / a)), (exp_pos _).le, hexp.le⟩) (exp_pos _) hexp] with N hN
    using hN.trans_lt hy

/-- The answer to the first part of Question 4.12: for every sequence of densities `δ_N → 0`,
`liminf φ(δ_N, N) / log N = 0`. -/
theorem liminf_phi_div_log_eq_zero (δ : ℕ → unitInterval)
    (hδ : Tendsto (fun N : ℕ ↦ (δ N : ℝ)) atTop (nhds 0)) :
    liminf (fun N : ℕ ↦ (phi (δ N) N : ℝ) / log N) atTop = 0 :=
  (tendsto_phi_div_log_nhds_zero_of_tendsto_nhds_zero δ hδ).liminf_eq

/-! ### The sequence `δ_N = 1 / log N` -/

/-- The density `1 / log N` of Question 4.12, projected to the unit interval. It equals
`1 / log N` for `N ≥ 3`. -/
noncomputable def logDensity (N : ℕ) : unitInterval :=
  Set.projIcc 0 1 zero_le_one (1 / log N)

variable {N : ℕ}

lemma one_le_log_of_three_le (hN : 3 ≤ N) : 1 ≤ log N := by
  rw [le_log_iff_exp_le (by positivity)]
  exact exp_one_lt_three.le.trans (mod_cast hN)

lemma coe_logDensity (hN : 3 ≤ N) : (logDensity N : ℝ) = 1 / log N := by
  have hlog := one_le_log_of_three_le hN
  rw [logDensity, Set.projIcc_of_mem _ ⟨by positivity, (div_le_one (by linarith)).mpr hlog⟩]

lemma tendsto_coe_logDensity :
    Tendsto (fun N : ℕ ↦ (logDensity N : ℝ)) atTop (nhds 0) := by
  refine (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with N hN
  rw [Pi.inv_apply, coe_logDensity hN, one_div, Function.comp_apply]

/-- `φ(1 / log N, N) / log N → 0`. -/
lemma tendsto_phi_logDensity_div_log_atTop_nhds_zero :
    Tendsto (fun N : ℕ ↦ (phi (logDensity N) N : ℝ) / log N) atTop (nhds 0) :=
  tendsto_phi_div_log_nhds_zero_of_tendsto_nhds_zero _ tendsto_coe_logDensity

/-- The answer to the second part of Question 4.12: `liminf φ(1 / log N, N) / log N = 0`. -/
theorem liminf_phi_logDensity_div_log_eq_zero :
    liminf (fun N : ℕ ↦ (phi (logDensity N) N : ℝ) / log N) atTop = 0 :=
  tendsto_phi_logDensity_div_log_atTop_nhds_zero.liminf_eq

lemma eventually_log_lt_rpow {α : ℝ} (hα : 0 < α) : ∀ᶠ x : ℝ in atTop, log x < x ^ α := by
  filter_upwards [(isLittleO_log_rpow_atTop hα).def one_half_pos, eventually_gt_atTop 1]
    with x hx hx₁
  rw [norm_of_nonneg (log_nonneg hx₁.le), norm_of_nonneg (rpow_nonneg (by linarith) _)] at hx
  linarith [rpow_pos_of_pos (zero_lt_one.trans hx₁) α]

/-- For every `α > 0` and all large `N`, `N ^ (-α) < 1 / log N`. -/
lemma eventually_rpow_neg_lt_coe_logDensity {α : ℝ} (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-α) < logDensity N := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_log_lt_rpow hα),
    eventually_ge_atTop 3] with N hN hN₃
  rw [coe_logDensity hN₃, rpow_neg N.cast_nonneg, ← one_div]
  exact one_div_lt_one_div_of_lt (one_pos.trans_le (one_le_log_of_three_le hN₃)) hN

lemma eventually_coe_logDensity_le_half :
    ∀ᶠ N : ℕ in atTop, (logDensity N : ℝ) ≤ 1 - 1 / 2 := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (tendsto_log_atTop.eventually_ge_atTop 2),
    eventually_ge_atTop 3] with N hN hN₃
  rw [coe_logDensity hN₃]
  linarith [one_div_le_one_div_of_le two_pos hN]

/-- For all large `N`, `φ(1 / log N, N) < 4 * log N / log (log N)`. -/
lemma eventually_phi_logDensity_lt_log_div_log_log :
    ∀ᶠ N : ℕ in atTop, (phi (logDensity N) N : ℝ) < 4 * log N / log (log N) := by
  filter_upwards [eventually_phi_lt_log_div_log (γ := 1) (c := 1 / 2) one_pos le_rfl
      (by norm_num) (by norm_num) logDensity
      (eventually_rpow_neg_lt_coe_logDensity
        (denseSubsetDensityExponent_pos one_pos (by norm_num) (by norm_num)))
      eventually_coe_logDensity_le_half,
    eventually_ge_atTop 3] with N hN hN₃
  rwa [coe_logDensity hN₃, one_div_one_div, (by norm_num : (3 + 1 : ℝ) = 4)] at hN

end DenseSetsWithoutLargeSumsets
