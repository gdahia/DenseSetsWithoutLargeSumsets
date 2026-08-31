/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.SumsetGrowth
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.FreimanDimension
import DenseSetsWithoutLargeSumsets.Probability
import DenseSetsWithoutLargeSumsets.Common
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.GeneralizedArithmeticProgression
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.LargeSumsetsFromMediumSizedSubsets.MediumSizedSubsets
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.Chang.Reduction
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.NumberTheory.Bertrand

/-!
Analytic estimates relating the size thresholds to logarithms of `n`.

A long sequence of elementary inequalities converting membership above `lowerSizeThreshold`
or `lowerGapThreshold` into log-scale bounds (e.g. `fifteen_lt_log_of_lowerAnalyticThreshold`,
`density_coeff_log_lt_exp_neg_mul_q`, `lowerGapSqrtScale_log_bound`) that the later counting
arguments consume.
-/

namespace DenseSetsWithoutLargeSumsets

open Nat hiding div_pos
open scoped Pointwise

noncomputable section

private lemma mul_log_Ax_le_self_of_two_mul_log {A T x : ℝ}
    (hA : 0 < A) (hT : 0 < T) (hx : 0 < x)
    (hmain : 2 * T * Real.log (A * T) ≤ x) :
    T * Real.log (A * x) ≤ x := by
  rw [← mul_div_cancel_left₀ x hT.ne', mul_div_assoc]
  apply mul_le_mul_of_nonneg_left
  · rw [← mul_assoc]
    rw [Real.log_mul (by positivity) (by positivity)]
    nlinarith [log_le_half_self (div_pos hx hT),
      (by
        rw [div_div, mul_comm T 2]
        rw [le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hT)]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmain :
        Real.log (A * T) ≤ (x / T) / 2)]
  · exact hT.le

private lemma lower_log_le_quarter_self_of_sixteen_le {x : ℝ} (hx : 16 ≤ x) :
    Real.log x ≤ x / 4 := by
  apply (by
    have hlog_eq : Real.log x = 2 * Real.log (Real.sqrt x) := by
      nth_rw 1 [← Real.sq_sqrt (by nlinarith : 0 ≤ x)]
      rw [Real.log_pow]
      norm_num
    rw [hlog_eq]
    nlinarith [log_le_half_self (Real.sqrt_pos.2 (by nlinarith : 0 < x))] :
    Real.log x ≤ Real.sqrt x).trans
  rw [Real.sqrt_le_left (by nlinarith : 0 ≤ x / 4)]
  nlinarith [mul_nonneg (by nlinarith : 0 ≤ x) (by nlinarith : 0 ≤ x - 16)]

private lemma log_fiftysix_gt_seven_div_two : (7 / 2 : ℝ) < Real.log (56 : ℝ) := by
  have h56 := Real.log_mul (by norm_num : (8 : ℝ) ≠ 0)
    (by norm_num : (7 : ℝ) ≠ 0)
  have h8 := Real.log_pow (2 : ℝ) 3
  norm_num at h56 h8
  nlinarith [h56, h8, Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1),
    Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 6)]

private lemma log_eightyfour_gt_four : (4 : ℝ) < Real.log (84 : ℝ) := by
  have h84 := Real.log_mul (by norm_num : (7 : ℝ) ≠ 0)
    (by norm_num : (12 : ℝ) ≠ 0)
  have h12 := Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
    (by norm_num : (4 : ℝ) ≠ 0)
  have h7prod := Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
    (by norm_num : (7 / 4 : ℝ) ≠ 0)
  have h4pow := Real.log_pow (2 : ℝ) 2
  norm_num at h84 h12 h7prod h4pow
  have h7 : (62 / 33 : ℝ) < Real.log 7 := by
    nlinarith [h7prod, h4pow,
      Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1),
      Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
  have h4 : (4 / 3 : ℝ) < Real.log 4 := by
    nlinarith [h4pow,
      Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1)]
  nlinarith [h84, h12, h7, h4,
    Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1)]

lemma fifteen_lt_log_of_lowerAnalyticThreshold {C γ : ℝ} {n : ℕ}
    (hn : lowerSizeThreshold C γ < n) :
    (15 : ℝ) < Real.log (n : ℝ) := by
  apply (by nlinarith [log_fiftysix_gt_seven_div_two] :
    (15 : ℝ) < 4 * Real.log (56 : ℝ) + 1).trans
  rw [← Real.log_exp (4 * Real.log (56 : ℝ) + 1)]
  apply Real.log_lt_log (Real.exp_pos _)
  exact (Real.exp_le_exp.mpr (le_max_left _ _)).trans_lt
    ((lowerAnalyticThreshold_le_lowerSizeThreshold C γ).trans_lt hn)

lemma pairCardThreshold_pos_of_density {τ : ℝ} {n : ℕ} {δ : unitInterval}
    (hτ : 0 < τ) (hδ : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) (hn : 1 < n) :
    0 < pairCardThreshold τ n δ := by
  rw [pairCardThreshold, Nat.ceil_pos]
  apply div_pos
  · apply mul_pos
    · exact hτ
    · apply Real.log_pos
      exact_mod_cast hn
  · apply Real.log_pos
    rw [one_lt_div hδ]
    exact hδ_lt

lemma one_lt_densityCoefficient {γ c : ℝ} (hγ_pos : 0 < γ)
    (hc_pos : 0 < c) (hc_lt : c < 1) :
    1 < densityCoefficient (2 + γ) c :=
  densityCoefficient_gt_one (by linarith) hc_pos hc_lt

private lemma one_le_lowerGapSqrtScale {C γ c : ℝ} (hγ_pos : 0 < γ)
    (hγ_le : γ ≤ 1) (hC : 0 < 2 * C) (hε : 0 < ε γ)
    (hc_pos : 0 < c) (hc_lt : c < 1) :
    1 ≤ lowerGapSqrtScale C γ c hC hε := by
  rw [lowerGapSqrtScale, le_div_iff₀ hε]
  have hsqrt : 1 ≤ Real.sqrt (densityCoefficient (2 + γ) c) := by
    rw [Real.one_le_sqrt]
    exact (one_lt_densityCoefficient hγ_pos hc_pos hc_lt).le
  nlinarith [one_le_lowerBltConstant hC hε,
    ε_le_one_twelfth hγ_pos hγ_le,
    mul_nonneg (by nlinarith [one_le_lowerBltConstant hC hε] :
      0 ≤ lowerBltConstant C γ hC hε - 1)
      (by nlinarith [hsqrt] : 0 ≤ Real.sqrt (densityCoefficient (2 + γ) c) - 1)]

lemma κ_ge_six_of_one_le {C : ℝ} (hC : 1 ≤ C) : 6 ≤ κ C := by
  unfold κ
  nlinarith [sq_nonneg (C - 1)]

lemma two_le_κ_of_one_le {C : ℝ} (hC : 1 ≤ C) : 2 ≤ κ C := by
  exact (by norm_num : (2 : ℝ) ≤ 6).trans (κ_ge_six_of_one_le hC)

private lemma chang_size_threshold_pos (C : ℝ) :
    0 < Real.exp (changContainerExponent (κ C)) :=
  Real.exp_pos _

lemma lowerDensityExponent_pos_of_one_le {C γ : ℝ} (hγ : 0 < γ) (hC : 1 ≤ C) :
    0 < lowerDensityExponent C γ := by
  unfold lowerDensityExponent
  apply div_pos
  · apply lt_min
    · apply div_pos
      · apply mul_pos
        · linarith
        · exact ε_pos hγ
      · apply mul_pos
        · norm_num
        · apply sq_pos_of_pos
          exact zero_lt_one.trans_le hC
    · apply div_pos
      · linarith
      · positivity
  · norm_num

private lemma lowerDensityExponent_le_first_component_half (C γ : ℝ) :
    lowerDensityExponent C γ ≤ (((2 + γ) * ε γ) / (12 * C ^ (2 : ℕ))) / 2 := by
  unfold lowerDensityExponent
  apply div_le_div_of_nonneg_right
  · apply min_le_left
  · norm_num

private lemma lowerDensityExponent_le_second_component_half (C γ : ℝ) :
    lowerDensityExponent C γ ≤
      ((2 + γ) / (2 * Real.exp (changContainerExponent (κ C)))) / 2 := by
  unfold lowerDensityExponent
  apply div_le_div_of_nonneg_right
  · apply min_le_right
  · norm_num

lemma one_le_sumset_card_coefficient_of_small_pair_sumset
    {G : Type*} [DecidableEq G] [Add G]
    [IsRightCancelAdd G]
    {A B : Finset G} {k : ℕ} {C : ℝ}
    (hk : 0 < k) (hAcard : A.card = k) (hBcard : B.card = k)
    (hAB : (A + B).card ≤ C * k) : 1 ≤ C := by
  nlinarith [hAB,
    (by
      exact_mod_cast (by
        rw [← hAcard]
        exact Finset.card_le_card_add_right
          (Finset.card_pos.mp (by rw [hBcard]; exact hk)) :
          k ≤ (A + B).card) :
          (k : ℝ) ≤ (A + B).card),
    (by exact_mod_cast hk : (0 : ℝ) < k)]

lemma freiman_image_sum_card {G H : Type*} [DecidableEq G] [DecidableEq H]
    [AddCommMonoid G] [AddCommMonoid H]
    {X A B : Finset G} {Y : Set H} {f : G → H}
    (hiso : IsAddFreimanIso 2 (X : Set G) Y f)
    (hAX : A ⊆ X) (hBX : B ⊆ X) :
    (A.image f + B.image f).card = (A + B).card := by
  classical
  apply Eq.trans (b := ((A ×ˢ B).image (fun p : G × G => f p.1 + f p.2)).card)
  · apply congrArg Finset.card
    ext y
    constructor
    · intro hy
      rw [Finset.mem_add] at hy
      obtain ⟨a', ha', b', hb', rfl⟩ := hy
      rw [Finset.mem_image] at ha' hb'
      obtain ⟨a, ha, rfl⟩ := ha'
      obtain ⟨b, hb, rfl⟩ := hb'
      exact Finset.mem_image.2 ⟨(a, b), by simp [ha, hb], by simp⟩
    · intro hy
      rw [Finset.mem_image] at hy
      obtain ⟨p, hp, rfl⟩ := hy
      rw [Finset.mem_product] at hp
      rw [Finset.mem_add]
      exact ⟨f p.1, Finset.mem_image.2 ⟨p.1, hp.1, rfl⟩,
        f p.2, Finset.mem_image.2 ⟨p.2, hp.2, rfl⟩, rfl⟩
  · refine Eq.trans
      (b := ((A ×ˢ B).image (fun p : G × G => p.1 + p.2)).card) ?_ ?_
    · apply card_image_eq_of_kernel_iff
      intro x hx y hy
      rw [Finset.mem_product] at hx hy
      exact hiso.add_eq_add (hAX hx.1) (hBX hx.2) (hAX hy.1) (hBX hy.2)
    · apply (congrArg Finset.card ?_).symm
      ext x
      constructor
      · intro hx
        rw [Finset.mem_add] at hx
        obtain ⟨a, ha, b, hb, rfl⟩ := hx
        exact Finset.mem_image.2 ⟨(a, b), by simp [ha, hb], rfl⟩
      · intro hx
        rw [Finset.mem_image] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        rw [Finset.mem_product] at hp
        rw [Finset.mem_add]
        exact ⟨p.1, hp.1, p.2, hp.2, rfl⟩

private lemma one_div_unitInterval_lt_rpow_lowerDensityExponent {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hn_pos : 0 < n) (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) :
    1 / (δ : ℝ) < (n : ℝ) ^ (lowerDensityExponent C γ) := by
  rw [Real.rpow_neg (le_of_lt (by exact_mod_cast hn_pos : 0 < (n : ℝ)))] at hδ_lower
  simpa [one_div] using
    one_div_lt_one_div_of_lt (inv_pos.mpr
      (Real.rpow_pos_of_pos (by exact_mod_cast hn_pos : 0 < (n : ℝ)) _)) hδ_lower

private lemma log_one_div_unitInterval_lt_lowerDensityExponent_mul_log {γ C : ℝ} {n : ℕ} {δ :
  unitInterval}
    (hn_pos : 0 < n) (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) :
    Real.log (1 / δ) < lowerDensityExponent C γ * Real.log (n : ℝ) := by
  apply (Real.log_lt_log (by
    apply div_pos
    · norm_num
    · exact (Real.rpow_pos_of_pos (by exact_mod_cast hn_pos : 0 < (n : ℝ)) _).trans hδ_lower)
    (one_div_unitInterval_lt_rpow_lowerDensityExponent hn_pos hδ_lower)).trans_eq
  rw [Real.log_rpow (by exact_mod_cast hn_pos : 0 < (n : ℝ))]

lemma log_one_div_unitInterval_pos {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hn_pos : 0 < n) (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ))
    (hδ_upper : (δ : ℝ) < 1) :
    0 < Real.log (1 / δ) := by
  apply Real.log_pos
  rw [one_lt_div (by
    exact (Real.rpow_pos_of_pos (by exact_mod_cast hn_pos : 0 < (n : ℝ)) _).trans hδ_lower)]
  linarith

lemma pairCardThreshold_arg_le {γ : ℝ} {n : ℕ} {δ : unitInterval} :
    (2 + γ) * Real.log (n : ℝ) / Real.log (1 / δ) ≤
      (pairCardThreshold (2 + γ) n δ : ℝ) := by
  rw [pairCardThreshold]
  apply Nat.le_ceil

private lemma lowerDensityExponent_le_gamma_div_ninetysix_sq {C γ : ℝ}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) :
    lowerDensityExponent C γ ≤ γ / (96 * C ^ (2 : ℕ)) := by
  apply (lowerDensityExponent_le_first_component_half C γ).trans_eq
  unfold ε
  field_simp [(sq_pos_of_pos (zero_lt_one.trans_le hC_one)).ne', (by linarith : γ + 2 ≠ 0)]
  ring

private lemma two_mul_ceil_κ_sub_one_pos {C : ℝ} (hC_one : 1 ≤ C) :
    0 < 2 * ⌈κ C⌉₊ - 1 := by
  apply Nat.sub_pos_of_lt
  exact_mod_cast (by
    nlinarith [(κ_ge_six_of_one_le hC_one).trans (Nat.le_ceil (κ C))] :
    (1 : ℝ) < 2 * (⌈κ C⌉₊ : ℝ))

private lemma two_mul_ceil_κ_sub_one_le_fourteen_sq {C : ℝ} (hC_one : 1 ≤ C) :
    ((2 * ⌈κ C⌉₊ - 1 : ℕ) : ℝ) ≤ 14 * C ^ (2 : ℕ) := by
  apply (by exact_mod_cast (Nat.sub_le (2 * ⌈κ C⌉₊) 1) :
    ((2 * ⌈κ C⌉₊ - 1 : ℕ) : ℝ) ≤ 2 * (⌈κ C⌉₊ : ℝ)).trans
  apply (mul_le_mul_of_nonneg_left
    (le_of_lt (Nat.ceil_lt_add_one
      ((by norm_num : (0 : ℝ) ≤ 6).trans (κ_ge_six_of_one_le hC_one))))
    (by norm_num : (0 : ℝ) ≤ 2)).trans
  unfold κ
  nlinarith [sq_nonneg (C - 1)]

private lemma two_mul_ceil_κ_sub_one_mul_lowerDensityExponent_lt {C γ : ℝ}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) :
    ((2 * ⌈κ C⌉₊ - 1 : ℕ) : ℝ) * lowerDensityExponent C γ < 2 + γ := by
  apply lt_of_le_of_lt (b := (7 / 48) * γ)
  · refine le_trans (b := (14 * C ^ (2 : ℕ)) * lowerDensityExponent C γ) ?_ ?_
    · apply mul_le_mul_of_nonneg_right
      · exact two_mul_ceil_κ_sub_one_le_fourteen_sq hC_one
      · exact (lowerDensityExponent_pos_of_one_le hγ_pos hC_one).le
    · refine le_trans (b := (14 * C ^ (2 : ℕ)) * (γ / (96 * C ^ (2 : ℕ)))) ?_ ?_
      · apply mul_le_mul_of_nonneg_left
        · exact lowerDensityExponent_le_gamma_div_ninetysix_sq hγ_pos hC_one
        · positivity
      · field_simp [(sq_pos_of_pos (zero_lt_one.trans_le hC_one)).ne']
        ring_nf
        exact le_rfl
  · nlinarith

private lemma pairCardThreshold_gt_of_mul_lowerDensityExponent_lt {γ C R : ℝ} {n : ℕ} {δ :
  unitInterval}
    (_hR_pos : 0 < R) (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn_one : 1 < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hRα_lt : R * lowerDensityExponent C γ < 2 + γ) :
    R < (pairCardThreshold (2 + γ) n δ : ℝ) := by
  refine lt_of_lt_of_le ?_ pairCardThreshold_arg_le
  apply lt_trans (b := (2 + γ) * Real.log (n : ℝ) /
      (lowerDensityExponent C γ * Real.log (n : ℝ)))
  · rw [lt_div_iff₀ (mul_pos (lowerDensityExponent_pos_of_one_le hγ_pos hC_one)
      (Real.log_pos (by exact_mod_cast hn_one : (1 : ℝ) < n)))]
    nlinarith [mul_lt_mul_of_pos_right hRα_lt
      (Real.log_pos (by exact_mod_cast hn_one : (1 : ℝ) < n))]
  · apply div_lt_div_of_pos_left
    · apply mul_pos
      · linarith
      · apply Real.log_pos
        exact_mod_cast hn_one
    · apply log_one_div_unitInterval_pos
      · exact zero_lt_one.trans hn_one
      · exact hδ_lower
      · exact hδ_upper
    · apply log_one_div_unitInterval_lt_lowerDensityExponent_mul_log
      · exact zero_lt_one.trans hn_one
      · exact hδ_lower

private lemma two_mul_chang_size_threshold_mul_lowerDensityExponent_lt {γ C : ℝ}
    (hγ_pos : 0 < γ) :
    (2 * (Real.exp (changContainerExponent (κ C)))) * lowerDensityExponent C γ <
      2 + γ := by
  have hT : (0 : ℝ) < Real.exp (changContainerExponent (κ C)) := chang_size_threshold_pos C
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left
    (lowerDensityExponent_le_second_component_half C γ) (by positivity))
  rw [div_div, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
  nlinarith

lemma two_mul_chang_size_threshold_lt_pairCardThreshold {γ C : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn_one : 1 < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    2 * (Real.exp (changContainerExponent (κ C))) <
      (pairCardThreshold (2 + γ) n δ : ℝ) := by
  apply pairCardThreshold_gt_of_mul_lowerDensityExponent_lt
  · apply mul_pos
    · norm_num
    · exact chang_size_threshold_pos C
  · exact hγ_pos
  · exact hC_one
  · exact hn_one
  · exact hδ_lower
  · exact hδ_upper
  · exact two_mul_chang_size_threshold_mul_lowerDensityExponent_lt hγ_pos

private lemma fourteen_mul_sq_div_ε_mul_lowerDensityExponent_lt {γ C : ℝ}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) :
    (14 * C ^ (2 : ℕ) / ε γ) * lowerDensityExponent C γ < 2 + γ := by
  apply lt_of_le_of_lt (b := 14 * (2 + γ) / 24)
  · refine le_trans (b :=
      (14 * C ^ (2 : ℕ) / ε γ) *
        (((2 + γ) * ε γ) / (24 * C ^ (2 : ℕ)))) ?_ ?_
    · apply mul_le_mul_of_nonneg_left
      · refine (lowerDensityExponent_le_first_component_half C γ).trans_eq ?_
        ring
      · apply div_nonneg
        · positivity
        · exact (ε_pos hγ_pos).le
    · field_simp [(ε_pos hγ_pos).ne',
        (sq_pos_of_pos (zero_lt_one.trans_le hC_one)).ne']
      exact le_refl (1 : ℝ)
  · nlinarith

lemma fourteen_mul_sq_lt_ε_mul_pairCardThreshold {γ C : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (_hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn_one : 1 < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    14 * C ^ (2 : ℕ) < ε γ * (pairCardThreshold (2 + γ) n δ : ℝ) := by
  rw [mul_comm (ε γ) ((pairCardThreshold (2 + γ) n δ : ℕ) : ℝ)]
  rw [← div_lt_iff₀ (ε_pos hγ_pos)]
  apply pairCardThreshold_gt_of_mul_lowerDensityExponent_lt
  · apply div_pos
    · apply mul_pos
      · norm_num
      · apply pow_pos
        exact zero_lt_one.trans_le hC_one
    · exact ε_pos hγ_pos
  · exact hγ_pos
  · exact hC_one
  · exact hn_one
  · exact hδ_lower
  · exact hδ_upper
  · exact fourteen_mul_sq_div_ε_mul_lowerDensityExponent_lt hγ_pos hC_one

lemma two_mul_ceil_κ_sub_one_le_ε_mul_pairCardThreshold {γ C : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn_one : 1 < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    ((2 * ⌈κ C⌉₊ - 1 : ℕ) : ℝ) ≤
      ε γ * (pairCardThreshold (2 + γ) n δ : ℝ) := by
  exact (two_mul_ceil_κ_sub_one_le_fourteen_sq hC_one).trans
    (le_of_lt
      (fourteen_mul_sq_lt_ε_mul_pairCardThreshold hγ_pos hγ_le hC_one hn_one hδ_lower
        hδ_upper))

lemma two_mul_ceil_κ_sub_one_le_pairCardThreshold {γ C : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn_one : 1 < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    2 * ⌈κ C⌉₊ - 1 ≤ pairCardThreshold (2 + γ) n δ := by
  apply le_of_lt
  exact_mod_cast pairCardThreshold_gt_of_mul_lowerDensityExponent_lt
    (R := ((2 * ⌈κ C⌉₊ - 1 : ℕ) : ℝ))
    (by
      exact_mod_cast two_mul_ceil_κ_sub_one_pos hC_one :
        (0 : ℝ) < ((2 * ⌈κ C⌉₊ - 1 : ℕ) : ℝ))
    hγ_pos hC_one hn_one hδ_lower hδ_upper
    (two_mul_ceil_κ_sub_one_mul_lowerDensityExponent_lt hγ_pos hC_one)

private lemma old_model_threshold_lt_nat {C γ : ℝ} {n : ℕ} (hn : lowerSizeThreshold C γ < n) :
    ((36 * Real.exp (changExponent C)) ^ (2 : ℕ)) < (n : ℝ) := by
  exact (old_model_threshold_le_lowerSizeThreshold C γ).trans_lt hn

lemma old_model_threshold_nat_pos {C γ : ℝ} {n : ℕ} (hn : lowerSizeThreshold C γ < n) :
    0 < (n : ℝ) := by
  exact (by positivity : (0 : ℝ) < (36 * Real.exp (changExponent C)) ^ (2 : ℕ)).trans
    (old_model_threshold_lt_nat hn)

private lemma log_nat_le_two_sqrt_of_old_model_threshold {C γ : ℝ} {n : ℕ}
    (hn : lowerSizeThreshold C γ < n) :
    Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
  simpa [Real.sqrt_eq_rpow, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    Real.log_le_rpow_div (x := (n : ℝ)) (ε := (1 / 2 : ℝ))
      (le_of_lt (old_model_threshold_nat_pos hn)) (by norm_num)

lemma density_coeff_log_lt_exp_neg_mul_q {C γ c : ℝ} {n q : ℕ}
    (hγ_pos : 0 < γ) (hc_pos : 0 < c) (hc_lt : c < 1)
    (hn : lowerGapThreshold C γ c < n) (hq_lower : 2 * n ≤ q) :
    2 * densityCoefficient (2 + γ) c * Real.log (n : ℝ) <
      Real.exp (-(changExponent C)) * q := by
  let K := densityCoefficient (2 + γ) c
  have hK_pos : 0 < K := by
    dsimp [K, densityCoefficient]
    have : 0 < Real.log (1 / (1 - c)) := by
      apply Real.log_pos
      rw [one_lt_div] <;> linarith
    positivity
  have hn_old : lowerSizeThreshold C γ < n := (lowerSizeThreshold_le_lowerGapThreshold C γ
    c).trans_lt hn
  have hsquare : (2 * K * Real.exp (changExponent C)) ^ (2 : ℕ) < (n : ℝ) := by
    refine (le_max_left _ _ |>.trans (le_max_right (lowerSizeThreshold C γ) _)).trans_lt hn
  have hfactor : 2 * K * Real.exp (changExponent C) < Real.sqrt (n : ℝ) := by
    simpa [Real.sqrt_sq (by positivity : 0 ≤ 2 * K * Real.exp (changExponent C))] using
      Real.sqrt_lt_sqrt (sq_nonneg (2 * K * Real.exp (changExponent C))) hsquare
  apply (mul_le_mul_of_nonneg_left (log_nat_le_two_sqrt_of_old_model_threshold hn_old)
    (mul_nonneg (by norm_num) hK_pos.le)).trans_lt
  have hsqrt : 4 * K * Real.sqrt (n : ℝ) <
      2 * Real.exp (-(changExponent C)) * (n : ℝ) := by
    apply lt_of_eq_of_lt (b :=
      (2 * K * Real.exp (changExponent C)) *
        (2 * (Real.exp (-(changExponent C)) * Real.sqrt (n : ℝ))))
    · rw [Real.exp_neg]
      field_simp
      ring
    · refine (mul_lt_mul_of_pos_right hfactor
        (mul_pos (by norm_num) (mul_pos (Real.exp_pos _) (Real.sqrt_pos.2 ?_)))).trans_eq ?_
      · exact old_model_threshold_nat_pos hn_old
      · conv_rhs => rw [← Real.sq_sqrt (le_of_lt (old_model_threshold_nat_pos hn_old))]
        ring
  refine lt_of_eq_of_lt ?_ (hsqrt.trans_le ?_)
  · ring
  · nlinarith [mul_le_mul_of_nonneg_left
      (by exact_mod_cast hq_lower : (2 * n : ℝ) ≤ q)
      (le_of_lt (Real.exp_pos (-(changExponent C))))]

lemma lowerLogScale_log_bound_of_gap {C γ c : ℝ} {n : ℕ}
    (hC : 0 < 2 * C) (hε : 0 < ε γ)
    (hn : lowerGapThreshold C γ c < n) :
    lowerLogScale γ * Real.log
        (max 42 (3 * densityCoefficient (2 + γ) c) * lowerConstant C γ hC hε *
          Real.log (n : ℝ)) ≤
      Real.log (n : ℝ) := by
  have hn_old : lowerSizeThreshold C γ < n := (lowerSizeThreshold_le_lowerGapThreshold C γ
    c).trans_lt hn
  apply mul_log_Ax_le_self_of_two_mul_log
  · exact mul_pos (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) (lowerConstant_pos C γ hC hε)
  · exact lowerLogScale_pos hε
  · exact (by norm_num : (0 : ℝ) < 15).trans
      (fifteen_lt_log_of_lowerAnalyticThreshold hn_old)
  rw [← lowerConstantDefault_eq C γ hC hε]
  apply le_of_lt
  rw [← Real.log_exp (2 * lowerLogScale γ * Real.log
    (max 42 (3 * densityCoefficient (2 + γ) c) * lowerConstantDefault C γ *
      lowerLogScale γ))]
  apply Real.log_lt_log (Real.exp_pos _)
  apply (Real.exp_le_exp.mpr (le_max_left
    (2 * lowerLogScale γ * Real.log
      (max 42 (3 * densityCoefficient (2 + γ) c) * lowerConstantDefault C γ * lowerLogScale γ))
    ((4 * lowerGapSqrtScaleDefault C γ c * Real.log
      (2 * max 42 (3 * densityCoefficient (2 + γ) c) * lowerConstantDefault C γ *
        lowerGapSqrtScaleDefault C γ c)) ^ (2 : ℕ)))).trans_lt
  exact ((le_max_right
    ((2 * densityCoefficient (2 + γ) c * Real.exp (changExponent C)) ^ (2 : ℕ))
    (Real.exp (max
      (2 * lowerLogScale γ * Real.log
        (max 42 (3 * densityCoefficient (2 + γ) c) * lowerConstantDefault C γ * lowerLogScale γ))
      ((4 * lowerGapSqrtScaleDefault C γ c * Real.log
        (2 * max 42 (3 * densityCoefficient (2 + γ) c) * lowerConstantDefault C γ *
          lowerGapSqrtScaleDefault C γ c)) ^ (2 : ℕ))))).trans
    (le_max_right (lowerSizeThreshold C γ) _)).trans_lt hn

private lemma lowerGapSqrtScale_threshold_bound {C γ c : ℝ} {n : ℕ}
    (hC : 0 < 2 * C) (hε : 0 < ε γ)
    (hn : lowerGapThreshold C γ c < n) :
    4 * lowerGapSqrtScale C γ c hC hε * Real.log
        (2 * max 42 (3 * densityCoefficient (2 + γ) c) * lowerConstant C γ hC hε *
          lowerGapSqrtScale C γ c hC hε) ≤
      Real.sqrt (Real.log (n : ℝ)) := by
  apply Real.le_sqrt_of_sq_le
  rw [← lowerConstantDefault_eq C γ hC hε, ← lowerGapSqrtScaleDefault_eq C γ c hC hε]
  apply le_of_lt
  rw [← Real.log_exp ((4 * lowerGapSqrtScaleDefault C γ c * Real.log
    (2 * max 42 (3 * densityCoefficient (2 + γ) c) * lowerConstantDefault C γ *
      lowerGapSqrtScaleDefault C γ c)) ^ (2 : ℕ))]
  apply Real.log_lt_log (Real.exp_pos _)
  apply (Real.exp_le_exp.mpr (le_max_right
    (2 * lowerLogScale γ * Real.log
      (max 42 (3 * densityCoefficient (2 + γ) c) * lowerConstantDefault C γ * lowerLogScale γ))
    ((4 * lowerGapSqrtScaleDefault C γ c * Real.log
      (2 * max 42 (3 * densityCoefficient (2 + γ) c) * lowerConstantDefault C γ *
        lowerGapSqrtScaleDefault C γ c)) ^ (2 : ℕ)))).trans_lt
  exact ((le_max_right
    ((2 * densityCoefficient (2 + γ) c * Real.exp (changExponent C)) ^ (2 : ℕ))
    (Real.exp (max
      (2 * lowerLogScale γ * Real.log
        (max 42 (3 * densityCoefficient (2 + γ) c) * lowerConstantDefault C γ * lowerLogScale γ))
      ((4 * lowerGapSqrtScaleDefault C γ c * Real.log
        (2 * max 42 (3 * densityCoefficient (2 + γ) c) * lowerConstantDefault C γ *
          lowerGapSqrtScaleDefault C γ c)) ^ (2 : ℕ))))).trans
    (le_max_right (lowerSizeThreshold C γ) _)).trans_lt hn

lemma lowerGapSqrtScale_log_bound {C γ c : ℝ} {n : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC : 0 < 2 * C) (hε : 0 < ε γ)
    (hc_pos : 0 < c) (hc_lt : c < 1)
    (hn : lowerGapThreshold C γ c < n) :
    lowerGapSqrtScale C γ c hC hε * Real.log
        (max 42 (3 * densityCoefficient (2 + γ) c) * lowerConstant C γ hC hε *
          Real.log (n : ℝ)) ≤
      Real.sqrt (Real.log (n : ℝ)) := by
  let M := max 42 (3 * densityCoefficient (2 + γ) c)
  have hM : (42 : ℝ) ≤ M := le_max_left _ _
  have hM_pos : 0 < M := (by norm_num : (0 : ℝ) < 42).trans_le hM
  have hK_pos : 0 < densityCoefficient (2 + γ) c :=
    zero_lt_one.trans (one_lt_densityCoefficient hγ_pos hc_pos hc_lt)
  have hn_old : lowerSizeThreshold C γ < n := (lowerSizeThreshold_le_lowerGapThreshold C γ
    c).trans_lt hn
  have hlog_pos : 0 < Real.log (n : ℝ) :=
    (by norm_num : (0 : ℝ) < 15).trans
      (fifteen_lt_log_of_lowerAnalyticThreshold hn_old)
  rw [← mul_div_cancel_left₀ (Real.sqrt (Real.log (n : ℝ)))
    (lowerGapSqrtScale_pos hC hε hK_pos).ne', mul_div_assoc]
  apply mul_le_mul_of_nonneg_left
  · refine (Real.log_le_log
      (x := M * lowerConstant C γ hC hε * Real.log (n : ℝ))
      (y := (2 * M * lowerConstant C γ hC hε * lowerGapSqrtScale C γ c hC hε *
        (Real.sqrt (Real.log (n : ℝ)) / lowerGapSqrtScale C γ c hC hε)) ^ (2 : ℕ))
      (mul_pos (mul_pos hM_pos (lowerConstant_pos C γ hC hε)) hlog_pos) ?_).trans ?_
    · refine le_trans (b := (2 * M) ^ (2 : ℕ) * (lowerConstant C γ hC hε) ^ (2 : ℕ) *
          Real.log (n : ℝ)) ?_ ?_
      · apply mul_le_mul_of_nonneg_right
        · nlinarith [hM, one_le_lowerConstant hC hε,
            mul_nonneg hM_pos.le (by nlinarith [one_le_lowerConstant hC hε] :
              0 ≤ lowerConstant C γ hC hε - 1)]
        · exact hlog_pos.le
      · field_simp [(lowerGapSqrtScale_pos hC hε hK_pos).ne']
        rw [Real.sq_sqrt hlog_pos.le]
    · rw [Real.log_pow]
      rw [Real.log_mul (by
        exact mul_ne_zero
          (mul_ne_zero (mul_ne_zero (by norm_num) hM_pos.ne')
            (lowerConstant_pos C γ hC hε).ne')
          (lowerGapSqrtScale_pos hC hε hK_pos).ne') (by
        exact (div_pos (Real.sqrt_pos.2 hlog_pos) (lowerGapSqrtScale_pos hC hε hK_pos)).ne')]
      have hthreshold :
          4 * Real.log
              (2 * M * lowerConstant C γ hC hε * lowerGapSqrtScale C γ c hC hε) ≤
            Real.sqrt (Real.log (n : ℝ)) / lowerGapSqrtScale C γ c hC hε := by
        rw [le_div_iff₀ (lowerGapSqrtScale_pos hC hε hK_pos)]
        simpa [M, mul_assoc, mul_left_comm, mul_comm] using
          lowerGapSqrtScale_threshold_bound (C := C) (γ := γ) (c := c) hC hε hn
      have hfour : (4 : ℝ) ≤ Real.log
          (2 * M * lowerConstant C γ hC hε * lowerGapSqrtScale C γ c hC hε) := by
        apply (le_of_lt log_eightyfour_gt_four).trans
        apply Real.log_le_log (by norm_num)
        nlinarith [one_le_lowerConstant hC hε,
          one_le_lowerGapSqrtScale hγ_pos hγ_le hC hε hc_pos hc_lt,
          mul_nonneg (by nlinarith [hM] : 0 ≤ 2 * M - 84)
            (by nlinarith [one_le_lowerConstant hC hε,
              one_le_lowerGapSqrtScale hγ_pos hγ_le hC hε hc_pos hc_lt] :
              0 ≤ lowerConstant C γ hC hε * lowerGapSqrtScale C γ c hC hε)]
      nlinarith [hthreshold,
        lower_log_le_quarter_self_of_sixteen_le (by nlinarith [hfour, hthreshold])]
  · exact (lowerGapSqrtScale_pos hC hε hK_pos).le

end

end DenseSetsWithoutLargeSumsets
