/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.NumberTheory.Bertrand
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.LargeSubsetsGAP
import DenseSetsWithoutLargeSumsets.Probability
import DenseSetsWithoutLargeSumsets.Common
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.FreimanDimension
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.GeneralizedArithmeticProgression
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.LargeSumsetsFromMediumSizedSubsets.MediumSizedSubsets
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.Chang.Reduction

/-!
Bookkeeping constants for counting proper GAPs and BLT pairs.

Introduces `lowerModelGAPs` and `bltLargePreimage`, and bounds the common base
`3 * lowerConstant C γ * pairCardThreshold (3 + γ) n δ` that both the GAP count and the BLT
fingerprint count are measured against, culminating in the two log bounds
(`lower_counting_base_log_le_epsilon_log_div_eight`,
`lower_c_sqrt_counting_base_log_le_epsilon_log_div_eight`) feeding the exponent estimate.
-/

namespace DenseSetsWithoutLargeSumsets

open Nat hiding div_pos
open scoped Pointwise

noncomputable section

abbrev lowerModelGAPs {γ C : ℝ} {n : ℕ} (δ : unitInterval)
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hn : lowerSizeThreshold C γ < n) :
    Finset (ProperGAP (ZMod (zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn))) := by
  classical
  exact (Finset.Icc 1 (pairCardThreshold (3 + γ) n δ)).biUnion fun d =>
    properGAPsZModOfDim d
        ⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊
        (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).pos

abbrev bltLargePreimage (A : Finset ℕ) (T : Finset ℤ) : Finset ℕ :=
  A.filter fun a => (a : ℤ) ∈ T

lemma bltLargePreimage_subset (A : Finset ℕ) (T : Finset ℤ) :
    bltLargePreimage A T ⊆ A := by
  intro a ha
  rw [bltLargePreimage, Finset.mem_filter] at ha
  exact ha.1

lemma natCastImage_bltLargePreimage_eq_of_subset {A : Finset ℕ} {T : Finset ℤ}
    (hT : T ⊆ natCastImage A) :
    natCastImage (bltLargePreimage A T) = T := by
  unfold bltLargePreimage
  exact natCastImage_filter_mem_eq_of_subset hT

private lemma bltLargePreimage_card_eq_of_subset {A : Finset ℕ} {T : Finset ℤ}
    (hT : T ⊆ natCastImage A) :
    (bltLargePreimage A T).card = T.card := by
  rw [← natCastImage_card (bltLargePreimage A T), natCastImage_bltLargePreimage_eq_of_subset hT]

lemma bltLargePreimage_large_of_blt {γ : ℝ} {A : Finset ℕ} {T : Finset ℤ}
    {k : ℕ}
    (hAcard : A.card = k) (hT : T ⊆ natCastImage A)
    (hTlarge : (1 - ε γ) * ((natCastImage A).card : ℝ) ≤ (T.card : ℝ)) :
    (1 - ε γ) * (k : ℝ) ≤ ((bltLargePreimage A T).card : ℝ) := by
  simpa [natCastImage_card A, hAcard, bltLargePreimage_card_eq_of_subset hT] using hTlarge

lemma natCastImage_nonempty_of_card_eq {A : Finset ℕ} {k : ℕ}
    (hAcard : A.card = k) (hk : 0 < k) :
    (natCastImage A).Nonempty := by
  apply Finset.card_pos.mp
  rw [natCastImage_card, hAcard]
  exact hk

private lemma two_le_two_mul_ceil_κ_sub_one {C : ℝ} (hC_one : 1 ≤ C) :
    2 ≤ 2 * ⌈κ C⌉₊ - 1 := by
  exact (by norm_num : 2 ≤ 2 * 6 - 1).trans
    (Nat.sub_le_sub_right
      (Nat.mul_le_mul_left 2 (by
        exact_mod_cast (κ_ge_six_of_one_le hC_one).trans (Nat.le_ceil (κ C))))
      1)

lemma two_le_pairCardThreshold_of_one_le {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    2 ≤ pairCardThreshold (3 + γ) n δ := by
  exact (two_le_two_mul_ceil_κ_sub_one hC_one).trans
    (two_mul_ceil_κ_sub_one_le_pairCardThreshold hγ_pos hC_one
      (one_lt_nat_of_lowerSizeThreshold_lt hn)
      hδ_lower hδ_upper)

private lemma four_le_pairCardThreshold_of_one_le {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    4 ≤ pairCardThreshold (3 + γ) n δ := by
  apply le_of_lt
  exact_mod_cast (by
    nlinarith [fourteen_mul_sq_lt_ε_mul_pairCardThreshold hγ_pos hγ_le hC_one
      (one_lt_nat_of_lowerSizeThreshold_lt hn) hδ_lower hδ_upper,
      ε_le_one_twelfth hγ_pos hγ_le,
      sq_nonneg (C - 1)] :
      (4 : ℝ) < pairCardThreshold (3 + γ) n δ)

private lemma two_le_blt_sqrt_pairCardThreshold {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    2 ≤ lowerBltConstant C γ hC_two hε *
        Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ) := by
  nlinarith [one_le_lowerBltConstant hC_two hε,
    Real.le_sqrt_of_sq_le (x := (2 : ℝ))
      (y := (pairCardThreshold (3 + γ) n δ : ℝ)) (by
      convert (by
        exact_mod_cast four_le_pairCardThreshold_of_one_le hγ_pos hγ_le hC_one hn hδ_lower
          hδ_upper :
          (4 : ℝ) ≤ pairCardThreshold (3 + γ) n δ) using 1
      norm_num)]

lemma lower_blt_ceiling_succ_le_two_mul {γ C : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    ((⌈lowerBltConstant C γ hC_two hε *
          Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ + 1 : ℕ) : ℝ) ≤
      2 * lowerBltConstant C γ hC_two hε *
        Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ) := by
  rw [Nat.cast_add, Nat.cast_one]
  nlinarith [Nat.ceil_lt_add_one
    (a := lowerBltConstant C γ hC_two hε *
      Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)) (mul_nonneg
    ((zero_le_one' ℝ).trans (one_le_lowerBltConstant hC_two hε))
    (Real.sqrt_nonneg (pairCardThreshold (3 + γ) n δ : ℝ))),
    two_le_blt_sqrt_pairCardThreshold hγ_pos hγ_le hC_one hn hδ_lower hδ_upper hC_two
      hε]

lemma changCarrierBound_ceil_succ_le_three_mul_lowerConstant {γ C : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    ((⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ + 1 : ℕ) : ℝ) ≤
      3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ) := by
  simp [changCarrierBound]
  nlinarith [Nat.ceil_lt_add_one
    (a := Real.exp (changTheoremExponent (κ C)) *
      (2 * (pairCardThreshold (3 + γ) n δ : ℝ)))
    (mul_nonneg (Real.exp_pos _).le (by positivity :
      0 ≤ 2 * (pairCardThreshold (3 + γ) n δ : ℝ))),
    le_max_left (Real.exp (changTheoremExponent (κ C)))
      (4 * lowerBltConstant C γ hC_two hε),
    mul_le_mul_of_nonneg_right
      (le_max_left (Real.exp (changTheoremExponent (κ C)))
        (4 * lowerBltConstant C γ hC_two hε))
      (by positivity : 0 ≤ 2 * (pairCardThreshold (3 + γ) n δ : ℝ)),
    (by
      rw [lowerConstant_eq C γ hC_two hε]
      exact (mul_le_mul_of_nonneg_right
        (le_max_left (Real.exp (changTheoremExponent (κ C)))
          (4 * lowerBltConstant C γ hC_two hε))
        (by positivity : 0 ≤ 2 * (pairCardThreshold (3 + γ) n δ : ℝ))).trans_eq (by ring) :
      Real.exp (changTheoremExponent (κ C)) *
          (2 * (pairCardThreshold (3 + γ) n δ : ℝ)) ≤
        2 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ)),
    one_le_lowerConstant hC_two hε,
    (by
      exact_mod_cast two_le_pairCardThreshold_of_one_le hγ_pos hC_one hn hδ_lower hδ_upper :
        (2 : ℝ) ≤ pairCardThreshold (3 + γ) n δ),
    (by
      rw [← one_mul (2 : ℝ)]
      exact mul_le_mul (one_le_lowerConstant hC_two hε)
        (by
          exact_mod_cast two_le_pairCardThreshold_of_one_le hγ_pos hC_one hn hδ_lower
            hδ_upper :
            (2 : ℝ) ≤ pairCardThreshold (3 + γ) n δ)
        (by norm_num) ((zero_le_one' ℝ).trans (one_le_lowerConstant hC_two hε)) :
      (2 : ℝ) ≤ lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ)),
    two_le_pairCardThreshold_of_one_le hγ_pos hC_one hn hδ_lower hδ_upper]

lemma lower_exponent_coefficient {γ : ℝ} (hγ_pos : 0 < γ) (_hγ_le : γ ≤ 1) :
    2 * (1 + ε γ) ≤ (1 - 3 * ε γ) * (3 + γ) := by
  unfold ε
  field_simp [(by positivity : 0 < 4 * (γ + 2)).ne']
  nlinarith

lemma one_le_lower_counting_base {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    1 ≤ 3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ) := by
  refine (by norm_num : (1 : ℝ) ≤ 3 * 2).trans ?_
  nlinarith [(by
    rw [← one_mul (2 : ℝ)]
    exact mul_le_mul (one_le_lowerConstant hC_two hε)
      (by
        exact_mod_cast two_le_pairCardThreshold_of_one_le hγ_pos hC_one hn hδ_lower hδ_upper :
        (2 : ℝ) ≤ pairCardThreshold (3 + γ) n δ)
      (by norm_num) ((zero_le_one' ℝ).trans (one_le_lowerConstant hC_two hε)) :
    (2 : ℝ) ≤ lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ))]

private lemma four_le_lower_counting_base {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    4 ≤ 3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ) := by
  refine (by norm_num : (4 : ℝ) ≤ 3 * 2).trans ?_
  nlinarith [(by
    rw [← one_mul (2 : ℝ)]
    exact mul_le_mul (one_le_lowerConstant hC_two hε)
      (by
        exact_mod_cast two_le_pairCardThreshold_of_one_le hγ_pos hC_one hn hδ_lower hδ_upper :
        (2 : ℝ) ≤ pairCardThreshold (3 + γ) n δ)
      (by norm_num) ((zero_le_one' ℝ).trans (one_le_lowerConstant hC_two hε)) :
    (2 : ℝ) ≤ lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ))]

lemma lower_counting_base_pos {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    0 < 3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ) := by
  exact zero_lt_one.trans_le
    (one_le_lower_counting_base hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε)

lemma lower_chang_carrier_ceil_pos {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (_hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    0 < ⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ := by
  rw [Nat.ceil_pos]
  rw [changCarrierBound]
  apply mul_pos
  · exact Real.exp_pos _
  · exact_mod_cast Nat.mul_pos (by norm_num : 0 < 2)
      (pairCardThreshold_pos_of_lower_density hγ_pos hn hδ_lower hδ_upper)

lemma changCarrierBound_ceil_le_lower_counting_base {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    (⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ : ℝ) ≤
      3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ) := by
  exact (by exact_mod_cast
      Nat.le_succ ⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ :
      (⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ : ℝ) ≤
        (⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ + 1 : ℕ)).trans
    (changCarrierBound_ceil_succ_le_three_mul_lowerConstant hγ_pos hC_one hn hδ_lower hδ_upper
      hC_two hε)

lemma blt_ceiling_succ_le_lower_counting_base {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    ((⌈lowerBltConstant C γ hC_two hε *
          Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ + 1 : ℕ) : ℝ) ≤
      3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ) := by
  refine (lower_blt_ceiling_succ_le_two_mul hγ_pos hγ_le hC_one hn hδ_lower hδ_upper
    hC_two hε).trans ?_
  nlinarith [
    (mul_le_mul (lowerBltConstant_le_lowerConstant hC_two hε)
      (by
        rw [Real.sqrt_le_left (by positivity :
          0 ≤ (pairCardThreshold (3 + γ) n δ : ℝ))]
        have hk_one : (1 : ℝ) ≤ pairCardThreshold (3 + γ) n δ := by
          exact_mod_cast ((by norm_num : 1 ≤ 2).trans
            (two_le_pairCardThreshold_of_one_le hγ_pos hC_one hn hδ_lower hδ_upper))
        nlinarith)
      (Real.sqrt_nonneg (pairCardThreshold (3 + γ) n δ : ℝ))
      ((zero_le_one' ℝ).trans (one_le_lowerConstant hC_two hε)) :
      lowerBltConstant C γ hC_two hε *
          Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ) ≤
        lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ)),
    lowerConstant_pos C γ hC_two hε,
    pairCardThreshold_pos_of_lower_density hγ_pos hn hδ_lower hδ_upper]

lemma zmodModelQ_le_n_mul_lower_counting_base {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    (zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn : ℝ) ≤
      (n : ℝ) * (3 * lowerConstant C γ hC_two hε *
        (pairCardThreshold (3 + γ) n δ : ℝ)) := by
  refine (by
      exact_mod_cast zmodModelQ_upper (γ := γ) (C := C) (n := n) hγ_pos C_pos hn :
        (zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn : ℝ) ≤
          4 * (n : ℝ)).trans ?_
  rw [mul_comm (4 : ℝ) (n : ℝ)]
  exact mul_le_mul_of_nonneg_left
    (four_le_lower_counting_base hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε)
    (le_of_lt (old_model_threshold_nat_pos hn))

lemma lower_counting_base_log_le_epsilon_log_div_eight {γ C c : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (_hγ_le : γ ≤ 1) (hC_one : 1 ≤ C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    Real.log (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ)) ≤
      ε γ * Real.log (n : ℝ) / 8 := by
  refine (Real.log_le_log
    (x := 3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ))
    (y := max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstant C γ hC_two hε *
      Real.log (n : ℝ))
    (lower_counting_base_pos hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε) ?_).trans ?_
  · have hk := pairCardThreshold_le_density_log_of_lower_density hγ_pos hc_pos hn hδ_lower
      hδ_upper_c
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      linarith [fifteen_lt_log_of_lowerAnalyticThreshold hn]
    nlinarith [mul_le_mul_of_nonneg_left hk
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (lowerConstant_pos C γ hC_two hε).le),
      mul_le_mul_of_nonneg_right (le_max_right (42 : ℝ)
        (3 * densityCoefficient (3 + γ) c))
        (mul_nonneg (lowerConstant_pos C γ hC_two hε).le hlog_nonneg)]
  · have hT₁ := lowerLogScale_log_bound_of_gap (C := C) (γ := γ) (c := c) (n := n)
      hC_two hε hn_gap
    rw [lowerLogScale] at hT₁
    rw [div_mul_eq_mul_div] at hT₁
    rw [div_le_iff₀ hε] at hT₁
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
    nlinarith

lemma lower_c_sqrt_counting_base_log_le_epsilon_log_div_eight {γ C c : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    lowerBltConstant C γ hC_two hε *
        Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ) *
        Real.log (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ)) ≤
      ε γ * Real.log (n : ℝ) / 8 := by
  refine (mul_le_mul_of_nonneg_left
      (Real.log_le_log
        (x := 3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ))
        (y := max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstant C γ hC_two hε *
          Real.log (n : ℝ))
        (lower_counting_base_pos hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε) ?_) ?_).trans ?_
  · have hk := pairCardThreshold_le_density_log_of_lower_density hγ_pos hc_pos hn hδ_lower
      hδ_upper_c
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      linarith [fifteen_lt_log_of_lowerAnalyticThreshold hn]
    nlinarith [mul_le_mul_of_nonneg_left hk
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (lowerConstant_pos C γ hC_two hε).le),
      mul_le_mul_of_nonneg_right (le_max_right (42 : ℝ)
        (3 * densityCoefficient (3 + γ) c))
        (mul_nonneg (lowerConstant_pos C γ hC_two hε).le hlog_nonneg)]
  · exact mul_nonneg ((zero_le_one' ℝ).trans (one_le_lowerBltConstant hC_two hε))
      (Real.sqrt_nonneg (pairCardThreshold (3 + γ) n δ : ℝ))
  · refine (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt
          (pairCardThreshold_le_density_log_of_lower_density hγ_pos hc_pos hn hδ_lower
            hδ_upper_c))
        ((zero_le_one' ℝ).trans (one_le_lowerBltConstant hC_two hε))) ?_).trans ?_
    · apply Real.log_nonneg
      have hbase : (1 : ℝ) ≤ lowerConstant C γ hC_two hε * Real.log (n : ℝ) := by
        rw [← one_mul (1 : ℝ)]
        exact mul_le_mul (one_le_lowerConstant hC_two hε)
          ((by norm_num : (1 : ℝ) < 15).le.trans
            (le_of_lt (fifteen_lt_log_of_lowerAnalyticThreshold hn)))
          (by norm_num) ((zero_le_one' ℝ).trans (one_le_lowerConstant hC_two hε))
      refine hbase.trans ?_
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right
        ((by norm_num : (1 : ℝ) ≤ 42).trans
          (le_max_left (42 : ℝ) (3 * densityCoefficient (3 + γ) c)))
        (zero_le_one.trans hbase)
    · rw [Real.sqrt_mul
        (zero_lt_one.trans (one_lt_densityCoefficient hγ_pos hc_pos hc_lt)).le]
      have hT₂ := lowerGapSqrtScale_log_bound hγ_pos hγ_le hC_two hε hc_pos hc_lt hn_gap
      rw [lowerGapSqrtScale, div_mul_eq_mul_div] at hT₂
      rw [div_le_iff₀ hε] at hT₂
      have := mul_le_mul_of_nonneg_right hT₂ (Real.sqrt_nonneg (Real.log (n : ℝ)))
      have hsquare : Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (Real.log (n : ℝ)) =
          Real.log (n : ℝ) := by
        rw [← pow_two, Real.sq_sqrt (le_of_lt ((by norm_num : (0 : ℝ) < 15).trans
          (fifteen_lt_log_of_lowerAnalyticThreshold hn)))]
      nlinarith [this, hsquare]


end

end DenseSetsWithoutLargeSumsets
