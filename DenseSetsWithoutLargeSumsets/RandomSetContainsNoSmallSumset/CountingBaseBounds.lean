/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.ProperGAP
public import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.ZModModel
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.ThresholdEstimates
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.WitnessPairs

/-!
# The base of the counting bounds

Let `k = pairCardThreshold (3 + γ) n δ`, let `L = lowerConstant C γ` and let
`β = lowerBltConstant C γ`. The number of proper progressions and the number of pairs of small
subsets of a progression are both bounded by powers of `3 * L * k`. This file bounds the
quantities of the counting argument by `3 * L * k`, and bounds `log (3 * L * k)` in terms of
`log n`.

## Main definitions

* `lowerModelGAPs`: the proper progressions in `ZMod q` of dimension between `1` and `k` with at
  most `⌈changCarrierBound (2 * k) (κ C)⌉₊` points.
* `bltLargePreimage`: the elements of `A` whose cast to `ℤ` lies in `T`.

## Main statements

* `lower_counting_base_log_le_epsilon_log_div_eight`: `log (3 * L * k) ≤ ε γ * log n / 8`.
* `lower_c_sqrt_counting_base_log_le_epsilon_log_div_eight`:
  `β * √k * log (3 * L * k) ≤ ε γ * log n / 8`.
-/

@[expose] public section

namespace DenseSetsWithoutLargeSumsets

open Finset Real ChangFreimanRuzsa

noncomputable section

/-- The proper progressions in `ZMod q` of dimension between `1` and
`k = pairCardThreshold (3 + γ) n δ` with at most `⌈changCarrierBound (2 * k) (κ C)⌉₊` points,
where `q = zmodModelQ`. -/
abbrev lowerModelGAPs {γ C : ℝ} {n : ℕ} (δ : unitInterval)
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hn : lowerSizeThreshold C γ < n) :
    Finset (GAP (ZMod (zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn))) := by
  classical
  exact (Finset.Icc 1 (pairCardThreshold (3 + γ) n δ)).biUnion fun d ↦
    properGAPsZModOfDim d
        ⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊
        (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).pos

/-- The elements of `A` whose cast to `ℤ` lies in `T`. -/
abbrev bltLargePreimage (A : Finset ℕ) (T : Finset ℤ) : Finset ℕ :=
  A.filter fun a ↦ (a : ℤ) ∈ T

lemma bltLargePreimage_subset (A : Finset ℕ) (T : Finset ℤ) : bltLargePreimage A T ⊆ A :=
  filter_subset _ _

lemma natCastImage_bltLargePreimage_eq_of_subset {A : Finset ℕ} {T : Finset ℤ}
    (hT : T ⊆ natCastImage A) :
    natCastImage (bltLargePreimage A T) = T :=
  natCastImage_filter_mem_eq_of_subset hT

lemma bltLargePreimage_large_of_blt {γ : ℝ} {A : Finset ℕ} {T : Finset ℤ} {k : ℕ}
    (hAcard : #A = k) (hT : T ⊆ natCastImage A)
    (hTlarge : (1 - ε γ) * (#(natCastImage A) : ℝ) ≤ (#T : ℝ)) :
    (1 - ε γ) * (k : ℝ) ≤ (#(bltLargePreimage A T) : ℝ) := by
  rwa [← natCastImage_card (bltLargePreimage A T), natCastImage_bltLargePreimage_eq_of_subset hT,
    ← hAcard, ← natCastImage_card A]

lemma natCastImage_nonempty_of_card_eq {A : Finset ℕ} {k : ℕ} (hAcard : #A = k) (hk : 0 < k) :
    (natCastImage A).Nonempty :=
  card_pos.1 (by rwa [natCastImage_card, hAcard])

lemma two_le_pairCardThreshold_of_one_le {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    2 ≤ pairCardThreshold (3 + γ) n δ := by
  have hκ : 6 ≤ ⌈κ C⌉₊ := mod_cast (κ_ge_six_of_one_le hC_one).trans (Nat.le_ceil _)
  have h := two_mul_ceil_κ_sub_one_le_pairCardThreshold hγ_pos hC_one
    (one_lt_nat_of_lowerSizeThreshold_lt hn) hδ_lower hδ_upper
  grind

private lemma four_le_pairCardThreshold {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    (4 : ℝ) ≤ pairCardThreshold (3 + γ) n δ := by
  linarith [fourteen_mul_sq_lt_ε_mul_pairCardThreshold hγ_pos hC_one
      (one_lt_nat_of_lowerSizeThreshold_lt hn) hδ_lower hδ_upper,
    mul_le_mul_of_nonneg_right (ε_le_one_twelfth hγ_pos hγ_le)
      (Nat.cast_nonneg (pairCardThreshold (3 + γ) n δ)),
    one_le_pow₀ hC_one (n := 2)]

private lemma two_le_lowerBltConstant_mul_sqrt {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    2 ≤ lowerBltConstant C γ hC_two hε * √(pairCardThreshold (3 + γ) n δ : ℝ) := by
  have h : 2 ≤ √(pairCardThreshold (3 + γ) n δ : ℝ) := le_sqrt_of_sq_le
    (by linarith [four_le_pairCardThreshold hγ_pos hγ_le hC_one hn hδ_lower hδ_upper])
  nlinarith [one_le_lowerBltConstant hC_two hε]

lemma lower_blt_ceiling_succ_le_two_mul {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    ((⌈lowerBltConstant C γ hC_two hε * √(pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ + 1 : ℕ) : ℝ) ≤
      2 * lowerBltConstant C γ hC_two hε * √(pairCardThreshold (3 + γ) n δ : ℝ) := by
  have h := two_le_lowerBltConstant_mul_sqrt hγ_pos hγ_le hC_one hn hδ_lower hδ_upper hC_two hε
  push_cast
  linarith [Nat.ceil_lt_add_one (zero_le_two.trans h)]

private lemma changCarrierBound_two_mul_le {γ C : ℝ} (k : ℕ) (hC_two : 0 < 2 * C)
    (hε : 0 < ε γ) :
    changCarrierBound (2 * k) (κ C) ≤ 2 * (lowerConstant C γ hC_two hε * k) := by
  rw [changCarrierBound, Nat.cast_mul, Nat.cast_two, mul_left_comm]
  gcongr
  exact le_max_left _ _

private lemma two_le_lowerConstant_mul_pairCardThreshold {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    2 ≤ lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ) := by
  have hk : (2 : ℝ) ≤ pairCardThreshold (3 + γ) n δ :=
    mod_cast two_le_pairCardThreshold_of_one_le hγ_pos hC_one hn hδ_lower hδ_upper
  nlinarith [one_le_lowerConstant hC_two hε]

lemma changCarrierBound_ceil_succ_le_three_mul_lowerConstant {γ C : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    ((⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ + 1 : ℕ) : ℝ) ≤
      3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ) := by
  have h : 0 ≤ changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C) :=
    mul_nonneg (exp_pos _).le (Nat.cast_nonneg _)
  push_cast
  linarith [Nat.ceil_lt_add_one h,
    changCarrierBound_two_mul_le (pairCardThreshold (3 + γ) n δ) hC_two hε,
    two_le_lowerConstant_mul_pairCardThreshold hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε]

lemma lower_exponent_coefficient {γ : ℝ} (hγ_pos : 0 < γ) :
    2 * (1 + ε γ) ≤ (1 - 3 * ε γ) * (3 + γ) := by
  unfold ε
  field_simp
  nlinarith

lemma one_le_lower_counting_base {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    1 ≤ 3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ) := by
  linarith [two_le_lowerConstant_mul_pairCardThreshold hγ_pos hC_one hn hδ_lower hδ_upper hC_two
    hε]

lemma lower_counting_base_pos {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    0 < 3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ) :=
  zero_lt_one.trans_le (one_le_lower_counting_base hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε)

lemma changCarrierBound_ceil_le_lower_counting_base {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    (⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ : ℝ) ≤
      3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ) := by
  have h := changCarrierBound_ceil_succ_le_three_mul_lowerConstant hγ_pos hC_one hn hδ_lower
    hδ_upper hC_two hε
  push_cast at h
  linarith

lemma blt_ceiling_succ_le_lower_counting_base {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    ((⌈lowerBltConstant C γ hC_two hε * √(pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ + 1 : ℕ) : ℝ) ≤
      3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ) := by
  have hk := four_le_pairCardThreshold hγ_pos hγ_le hC_one hn hδ_lower hδ_upper
  have hL := (lowerConstant_pos C γ hC_two hε).le
  have hs : √(pairCardThreshold (3 + γ) n δ : ℝ) ≤ pairCardThreshold (3 + γ) n δ :=
    sqrt_le_self_iff.2 (Or.inr (by linarith))
  refine (lower_blt_ceiling_succ_le_two_mul hγ_pos hγ_le hC_one hn hδ_lower hδ_upper hC_two
    hε).trans ?_
  linarith [mul_le_mul (lowerBltConstant_le_lowerConstant hC_two hε) hs (sqrt_nonneg _) hL,
    mul_nonneg hL (zero_le_four.trans hk)]

lemma zmodModelQ_le_n_mul_lower_counting_base {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    (zmodModelQ hγ_pos C_pos hn : ℝ) ≤
      (n : ℝ) * (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ)) := by
  have hq : (zmodModelQ hγ_pos C_pos hn : ℝ) ≤ 4 * n := mod_cast zmodModelQ_upper hγ_pos C_pos hn
  nlinarith [old_model_threshold_nat_pos hn,
    two_le_lowerConstant_mul_pairCardThreshold hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε]

private lemma lower_counting_base_le {γ C c : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hc_pos : 0 < c) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper_c : (δ : ℝ) ≤ 1 - c)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ) ≤
      max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstant C γ hC_two hε * log n := by
  have hL := (lowerConstant_pos C γ hC_two hε).le
  linarith [mul_le_mul_of_nonneg_left
      (pairCardThreshold_le_density_log_of_lower_density hγ_pos hc_pos hn hδ_lower hδ_upper_c)
      (mul_nonneg zero_le_three hL),
    mul_le_mul_of_nonneg_right (le_max_right 42 (3 * densityCoefficient (3 + γ) c))
      (mul_nonneg hL (log_natCast_nonneg n))]

/-- The logarithm of the base `3 * L * k` is at most `ε γ * log n / 8`. -/
lemma lower_counting_base_log_le_epsilon_log_div_eight {γ C c : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C)
    (hc_pos : 0 < c) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    log (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ)) ≤
      ε γ * log (n : ℝ) / 8 := by
  have h := lowerLogScale_log_bound_of_gap (c := c) hC_two hε hn_gap
  rw [lowerLogScale, div_mul_eq_mul_div, div_le_iff₀ hε] at h
  linarith [log_le_log (lower_counting_base_pos hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε)
    (lower_counting_base_le hγ_pos hc_pos hn hδ_lower hδ_upper_c hC_two hε)]

/-- With `β = lowerBltConstant C γ`, the product `β * √k * log (3 * L * k)` is at most
`ε γ * log n / 8`. -/
lemma lower_c_sqrt_counting_base_log_le_epsilon_log_div_eight {γ C c : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    lowerBltConstant C γ hC_two hε * √(pairCardThreshold (3 + γ) n δ : ℝ) *
        log (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ)) ≤
      ε γ * log (n : ℝ) / 8 := by
  have hβ : 0 ≤ lowerBltConstant C γ hC_two hε := zero_le_one.trans (one_le_lowerBltConstant _ _)
  have hk := sqrt_le_sqrt
    (pairCardThreshold_le_density_log_of_lower_density hγ_pos hc_pos hn hδ_lower hδ_upper_c)
  rw [sqrt_mul (zero_le_one.trans (one_lt_densityCoefficient hγ_pos hc_pos hc_lt).le)] at hk
  have h₁ := mul_le_mul (mul_le_mul_of_nonneg_left hk hβ)
    (log_le_log (lower_counting_base_pos hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε)
      (lower_counting_base_le hγ_pos hc_pos hn hδ_lower hδ_upper_c hC_two hε))
    (log_nonneg (one_le_lower_counting_base hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε))
    (by positivity)
  have h₂ := mul_le_mul_of_nonneg_right
    (lowerGapSqrtScale_log_bound hγ_pos hγ_le hC_two hε hc_pos hc_lt hn_gap)
    (sqrt_nonneg (log n))
  rw [mul_self_sqrt (log_natCast_nonneg n), lowerGapSqrtScale, div_mul_eq_mul_div,
    div_mul_eq_mul_div, div_le_iff₀ hε] at h₂
  linarith

end

end DenseSetsWithoutLargeSumsets
