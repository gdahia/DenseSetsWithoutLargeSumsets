/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.CountingBaseBounds
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.FreimanDimension
import DenseSetsWithoutLargeSumsets.Probability
import DenseSetsWithoutLargeSumsets.Common
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.GeneralizedArithmeticProgression
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.LargeSumsetsFromMediumSizedSubsets.MediumSizedSubsets
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.Chang.Reduction
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.NumberTheory.Bertrand

/-!
The exponent bound on a single dimension-`d` summand.

Combines the counting bounds on proper GAPs and BLT fingerprints with the probability decay
`δ ^ (dim * k)` into the single estimate `lower_gap_dim_summand_le`, bounding each term of the
sum over dimensions by `n ^ (-(ε γ / 2))`.
-/

namespace DenseSetsWithoutLargeSumsets

open Nat hiding div_pos
open scoped Pointwise

noncomputable section

private lemma natCast_pow_le_exp_log_of_le {a m : ℕ} {B : ℝ}
    (hB_pos : 0 < B) (ha : (a : ℝ) ≤ B) :
    ((a ^ m : ℕ) : ℝ) ≤ Real.exp ((m : ℝ) * Real.log B) := by
  rw [Nat.cast_pow]
  apply (pow_le_pow_left₀ (by positivity : 0 ≤ (a : ℝ)) ha m).trans_eq
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hB_pos]
  ring_nf

private lemma lower_positive_log_budget {γ C c : ℝ} {n : ℕ} {δ : unitInterval}
    {d : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ)
    (hd : d ∈ Finset.Icc 1 (pairCardThreshold (2 + γ) n δ)) :
    (2 * ((d : ℝ) + 1) +
        4 * lowerBltConstant C γ hC_two hε *
          Real.sqrt (pairCardThreshold (2 + γ) n δ : ℝ)) *
        Real.log (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (2 + γ) n δ : ℝ)) ≤
      (ε γ / 2) * ((d : ℝ) + 1) * Real.log (n : ℝ) := by
  rw [add_mul]
  have hd_one : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hmain' :
      2 * ((d : ℝ) + 1) *
          Real.log (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (2 + γ) n δ : ℝ)) ≤
        (ε γ / 4) * ((d : ℝ) + 1) * Real.log (n : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left
      (lower_counting_base_log_le_epsilon_log_div_eight hγ_pos hγ_le hC_one hc_pos hc_lt hn
        hn_gap hδ_lower hδ_upper hδ_upper_c hC_two hε)
      (by positivity : 0 ≤ 2 * ((d : ℝ) + 1))]
  have hsqrt' :
      4 * lowerBltConstant C γ hC_two hε *
          Real.sqrt (pairCardThreshold (2 + γ) n δ : ℝ) *
          Real.log (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (2 + γ) n δ : ℝ)) ≤
        ε γ * Real.log (n : ℝ) / 2 := by
    nlinarith [lower_c_sqrt_counting_base_log_le_epsilon_log_div_eight
      hγ_pos hγ_le hC_one hc_pos hc_lt hn hn_gap hδ_lower hδ_upper hδ_upper_c hC_two hε]
  have htail :
      ε γ * Real.log (n : ℝ) / 2 ≤
        (ε γ / 4) * ((d : ℝ) + 1) * Real.log (n : ℝ) := by
    ring_nf
    nlinarith [mul_nonneg hε.le
      (le_of_lt ((by norm_num : (0 : ℝ) < 15).trans
        (fifteen_lt_log_of_lowerAnalyticThreshold hn)))]
  nlinarith [hmain', hsqrt', htail]

private lemma lower_negative_log_margin {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    {d : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (_hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hd : d ∈ Finset.Icc 1 (pairCardThreshold (2 + γ) n δ)) :
    (1 + ε γ) * ((d : ℝ) + 1) * Real.log (n : ℝ) ≤
      (1 - 3 * ε γ) * (d : ℝ) * (pairCardThreshold (2 + γ) n δ : ℝ) *
        Real.log (1 / δ) := by
  have hlog_inv_pos := log_one_div_unitInterval_pos
    (zero_lt_one.trans (one_lt_nat_of_lowerSizeThreshold_lt hn)) hδ_lower hδ_upper
  have harg := pairCardThreshold_arg_le (γ := γ) (n := n) (δ := δ)
  rw [div_le_iff₀ hlog_inv_pos] at harg
  have hd_one : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hx_nonneg : 0 ≤ Real.log (n : ℝ) := by
    linarith [fifteen_lt_log_of_lowerAnalyticThreshold hn]
  have hleft :
      2 * (1 + ε γ) * (d : ℝ) * Real.log (n : ℝ) ≤
        (1 - 3 * ε γ) * (d : ℝ) *
          (pairCardThreshold (2 + γ) n δ : ℝ) * Real.log (1 / δ) := by
    nlinarith [
      mul_le_mul_of_nonneg_right (lower_exponent_coefficient hγ_pos hγ_le)
        (mul_nonneg (by positivity : 0 ≤ (d : ℝ)) hx_nonneg),
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left harg (by positivity : 0 ≤ (d : ℝ)))
        (one_sub_three_mul_ε_pos hγ_pos hγ_le).le]
  suffices hcompress :
      (1 + ε γ) * ((d : ℝ) + 1) * Real.log (n : ℝ) ≤
        2 * (1 + ε γ) * (d : ℝ) * Real.log (n : ℝ) by
    exact hcompress.trans hleft
  ring_nf
  nlinarith [mul_nonneg (by nlinarith [ε_pos hγ_pos] : 0 ≤ 1 + ε γ)
    hx_nonneg]

private lemma lower_summand_exponent_le {γ C c : ℝ} {n : ℕ} {δ : unitInterval}
    {d : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ)
    (hd : d ∈ Finset.Icc 1 (pairCardThreshold (2 + γ) n δ)) :
    ((d : ℝ) + 1) * (Real.log (n : ℝ) +
        2 * Real.log (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (2 + γ) n δ : ℝ))) +
        4 * lowerBltConstant C γ hC_two hε *
          Real.sqrt (pairCardThreshold (2 + γ) n δ : ℝ) *
          Real.log (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (2 + γ) n δ : ℝ)) -
        (1 - 3 * ε γ) * (d : ℝ) *
          (pairCardThreshold (2 + γ) n δ : ℝ) * Real.log (1 / δ) ≤
      -(ε γ / 2) * Real.log (n : ℝ) := by
  have hneg := lower_negative_log_margin hγ_pos hγ_le hC_one hn hδ_lower hδ_upper hd
  have hd_one : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hpos' :
      2 * ((d : ℝ) + 1) *
          Real.log (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (2 + γ) n δ : ℝ)) +
          4 * lowerBltConstant C γ hC_two hε *
            Real.sqrt (pairCardThreshold (2 + γ) n δ : ℝ) *
            Real.log (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (2 + γ) n δ : ℝ)) ≤
        (ε γ / 2) * ((d : ℝ) + 1) * Real.log (n : ℝ) := by
    simpa [add_mul] using
      lower_positive_log_budget hγ_pos hγ_le hC_one hc_pos hc_lt hn hn_gap hδ_lower
        hδ_upper hδ_upper_c hC_two hε hd
  have hlast :
      -(ε γ / 2) * ((d : ℝ) + 1) * Real.log (n : ℝ) ≤
        -(ε γ / 2) * Real.log (n : ℝ) := by
    nlinarith [
      mul_le_mul_of_nonneg_left (by nlinarith [hd_one] : (1 : ℝ) ≤ (d : ℝ) + 1)
        (by nlinarith [hε, fifteen_lt_log_of_lowerAnalyticThreshold hn] :
          0 ≤ (ε γ / 2) * Real.log (n : ℝ))]
  nlinarith [hpos', hneg, hlast]

private lemma lower_fingerprint_factor_le_exp {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    ((((⌈lowerBltConstant C γ hC_two hε *
          Real.sqrt (pairCardThreshold (2 + γ) n δ : ℝ)⌉₊ + 1) *
        (⌈changCarrierBound (2 * pairCardThreshold (2 + γ) n δ) (κ C)⌉₊ + 1) ^
          ⌈lowerBltConstant C γ hC_two hε *
            Real.sqrt (pairCardThreshold (2 + γ) n δ : ℝ)⌉₊ : ℕ) : ℝ) *
      (((⌈lowerBltConstant C γ hC_two hε *
          Real.sqrt (pairCardThreshold (2 + γ) n δ : ℝ)⌉₊ + 1) *
        (⌈changCarrierBound (2 * pairCardThreshold (2 + γ) n δ) (κ C)⌉₊ + 1) ^
          ⌈lowerBltConstant C γ hC_two hε *
            Real.sqrt (pairCardThreshold (2 + γ) n δ : ℝ)⌉₊ : ℕ) : ℝ)) ≤
      Real.exp (4 * lowerBltConstant C γ hC_two hε *
        Real.sqrt (pairCardThreshold (2 + γ) n δ : ℝ) *
        Real.log (3 * lowerConstant C γ hC_two hε *
          (pairCardThreshold (2 + γ) n δ : ℝ))) := by
  let M := ⌈lowerBltConstant C γ hC_two hε *
    Real.sqrt (pairCardThreshold (2 + γ) n δ : ℝ)⌉₊
  let s := ⌈changCarrierBound (2 * pairCardThreshold (2 + γ) n δ) (κ C)⌉₊
  let B := 3 * lowerConstant C γ hC_two hε * (pairCardThreshold (2 + γ) n δ : ℝ)
  let T := lowerBltConstant C γ hC_two hε *
    Real.sqrt (pairCardThreshold (2 + γ) n δ : ℝ)
  have hB_pos : 0 < B := by
    dsimp [B]
    exact lower_counting_base_pos hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε
  have hB_one : 1 ≤ B := by
    dsimp [B]
    exact one_le_lower_counting_base hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε
  have hlogB_nonneg : 0 ≤ Real.log B := Real.log_nonneg hB_one
  have hMsucc_le_T : ((M + 1 : ℕ) : ℝ) ≤ 2 * T := by
    dsimp [M, T]
    simpa [mul_assoc] using
      lower_blt_ceiling_succ_le_two_mul hγ_pos hγ_le hC_one hn hδ_lower hδ_upper
        hC_two hε
  have hMsucc_le_B : ((M + 1 : ℕ) : ℝ) ≤ B := by
    dsimp [M, B]
    exact blt_ceiling_succ_le_lower_counting_base hγ_pos hγ_le hC_one hn hδ_lower hδ_upper hC_two hε
  have hs_succ_le_B : ((s + 1 : ℕ) : ℝ) ≤ B := by
    dsimp [s, B]
    exact changCarrierBound_ceil_succ_le_three_mul_lowerConstant hγ_pos hC_one hn hδ_lower
      hδ_upper hC_two hε
  have hMexp : ((M + 1 : ℕ) : ℝ) ≤ Real.exp (Real.log B) := by
    rw [Real.exp_log hB_pos]
    exact hMsucc_le_B
  have hpow :
      (((s + 1) ^ M : ℕ) : ℝ) ≤ Real.exp ((M : ℝ) * Real.log B) :=
    natCast_pow_le_exp_log_of_le hB_pos hs_succ_le_B
  have hone :
      (((M + 1) * (s + 1) ^ M : ℕ) : ℝ) ≤
        Real.exp (((M + 1 : ℕ) : ℝ) * Real.log B) := by
    rw [Nat.cast_mul]
    apply (mul_le_mul hMexp hpow (by positivity) (by positivity)).trans_eq
    rw [← Real.exp_add]
    congr 1
    rw [Nat.cast_add, Nat.cast_one]
    ring
  apply (mul_le_mul hone hone (by positivity) (by positivity)).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [hMsucc_le_T, hlogB_nonneg]

private lemma lower_gap_count_le_exp {γ C : ℝ} {n : ℕ} {δ : unitInterval} {d : ℕ}
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    ((properGAPsZModOfDim d
        ⌈changCarrierBound (2 * pairCardThreshold (2 + γ) n δ) (κ C)⌉₊
        (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).pos).card : ℝ) ≤
      Real.exp (((d : ℝ) + 1) * (Real.log (n : ℝ) +
        2 * Real.log (3 * lowerConstant C γ hC_two hε *
          (pairCardThreshold (2 + γ) n δ : ℝ)))) := by
  let q := zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn
  let s := ⌈changCarrierBound (2 * pairCardThreshold (2 + γ) n δ) (κ C)⌉₊
  let B := 3 * lowerConstant C γ hC_two hε * (pairCardThreshold (2 + γ) n δ : ℝ)
  have hB_pos : 0 < B := by
    dsimp [B]
    exact lower_counting_base_pos hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε
  have hB_one : 1 ≤ B := by
    dsimp [B]
    exact one_le_lower_counting_base hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε
  have hlogB_nonneg : 0 ≤ Real.log B := Real.log_nonneg hB_one
  have hn_pos : 0 < (n : ℝ) := old_model_threshold_nat_pos hn
  have hq_le : (q : ℝ) ≤ (n : ℝ) * B := by
    dsimp [q, B]
    exact zmodModelQ_le_n_mul_lower_counting_base hγ_pos C_pos hC_one hn hδ_lower hδ_upper hC_two hε
  have hs_pos : 0 < s := by
    dsimp [s]
    exact lower_chang_carrier_ceil_pos hγ_pos hC_one hn hδ_lower hδ_upper
  have hs_le : (s : ℝ) ≤ B := by
    dsimp [s, B]
    exact changCarrierBound_ceil_le_lower_counting_base hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε
  apply (by
    dsimp [q, s]
    exact_mod_cast properGAPsZModOfDim_card
      (lower_chang_carrier_ceil_pos hγ_pos hC_one hn hδ_lower hδ_upper)
      (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).pos :
    ((properGAPsZModOfDim d
        ⌈changCarrierBound (2 * pairCardThreshold (2 + γ) n δ) (κ C)⌉₊
        (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).pos).card : ℝ) ≤
      ((q ^ (d + 1) * s ^ d : ℕ) : ℝ)).trans
  have hqpow :
      (((q ^ (d + 1) : ℕ) : ℝ)) ≤
        Real.exp (((d + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) * B)) :=
    natCast_pow_le_exp_log_of_le (mul_pos hn_pos hB_pos) hq_le
  have hspow :
      (((s ^ d : ℕ) : ℝ)) ≤ Real.exp ((d : ℝ) * Real.log B) :=
    natCast_pow_le_exp_log_of_le hB_pos hs_le
  apply (by
    rw [Nat.cast_mul]
    exact mul_le_mul hqpow hspow (by positivity) (by positivity) :
    ((q ^ (d + 1) * s ^ d : ℕ) : ℝ) ≤
      Real.exp (((d + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) * B)) *
        Real.exp ((d : ℝ) * Real.log B)).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [Real.log_mul hn_pos.ne' hB_pos.ne']
  rw [Nat.cast_add, Nat.cast_one]
  nlinarith

lemma lower_gap_dim_summand_le {γ C c : ℝ} {n : ℕ} {δ : unitInterval} {d : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (C_pos : 0 < C) (hC_one : 1 ≤ C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ)
    (hd : d ∈ Finset.Icc 1 (pairCardThreshold (2 + γ) n δ)) :
    ((properGAPsZModOfDim d
        ⌈changCarrierBound (2 * pairCardThreshold (2 + γ) n δ) (κ C)⌉₊
        (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).pos).card : ℝ) *
        ((((⌈lowerBltConstant C γ hC_two hε *
              Real.sqrt (pairCardThreshold (2 + γ) n δ : ℝ)⌉₊ + 1) *
            (⌈changCarrierBound (2 * pairCardThreshold (2 + γ) n δ) (κ C)⌉₊ + 1) ^
              ⌈lowerBltConstant C γ hC_two hε *
                Real.sqrt (pairCardThreshold (2 + γ) n δ : ℝ)⌉₊ : ℕ) : ℝ) *
          (((⌈lowerBltConstant C γ hC_two hε *
              Real.sqrt (pairCardThreshold (2 + γ) n δ : ℝ)⌉₊ + 1) *
            (⌈changCarrierBound (2 * pairCardThreshold (2 + γ) n δ) (κ C)⌉₊ + 1) ^
              ⌈lowerBltConstant C γ hC_two hε *
                Real.sqrt (pairCardThreshold (2 + γ) n δ : ℝ)⌉₊ : ℕ) : ℝ)) *
        Real.exp (-((1 - 3 * ε γ) * (d : ℝ) *
            (pairCardThreshold (2 + γ) n δ : ℝ)) * Real.log (1 / δ)) ≤
      (n : ℝ) ^ (-(ε γ / 2)) := by
  apply (mul_le_mul_of_nonneg_right
      (mul_le_mul
        (lower_gap_count_le_exp hγ_pos C_pos hC_one hn hδ_lower hδ_upper hC_two hε)
        (lower_fingerprint_factor_le_exp hγ_pos hγ_le hC_one hn hδ_lower hδ_upper
          hC_two hε)
        (by positivity)
        (by positivity))
      (by positivity)).trans
  rw [← Real.exp_add, ← Real.exp_add]
  rw [Real.rpow_def_of_pos (old_model_threshold_nat_pos hn)]
  rw [mul_comm (Real.log (n : ℝ)) (-(ε γ / 2))]
  apply Real.exp_le_exp.mpr
  simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
    lower_summand_exponent_le hγ_pos hγ_le hC_one hc_pos hc_lt hn hn_gap hδ_lower
      hδ_upper hδ_upper_c hC_two hε hd


end

end DenseSetsWithoutLargeSumsets
