/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.ProperGAP
public import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.ZModModel
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.CountingBaseBounds
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.ThresholdEstimates

/-!
# The bound on the term of each dimension

Let `k = pairCardThreshold (3 + γ) n δ`, let `L = lowerConstant C γ`, let
`β = lowerBltConstant C γ`, let `s = ⌈changCarrierBound (2 * k) (κ C)⌉₊` and let `m = ⌈β * √k⌉₊`.
The union bound over the proper progressions of dimension `d` in `ZMod q` with at most `s`
points, and over the pairs of subsets of size at most `m` of such a progression, has the term

`N * ((m + 1) * (s + 1) ^ m) ^ 2 * exp (-(1 - 3 * ε γ) * d * k * log (1 / δ))`,

where `N ≤ q ^ (d + 1) * s ^ d` is the number of these progressions and `(m + 1) * (s + 1) ^ m`
bounds the number of these subsets. Since `q ≤ n * (3 * L * k)`, `s + 1 ≤ 3 * L * k` and
`m + 1 ≤ min (3 * L * k) (2 * β * √k)`, this term is at most

`exp ((d + 1) * (log n + 2 * log (3 * L * k)) + 4 * β * √k * log (3 * L * k)
  - (1 - 3 * ε γ) * d * k * log (1 / δ))`.

## Main statements

* `lower_gap_dim_summand_le`: for `1 ≤ d ≤ k`, the term of dimension `d` is at most
  `n ^ (-(ε γ / 2))`.
-/

@[expose] public section

namespace DenseSetsWithoutLargeSumsets

open Finset Real

noncomputable section

private lemma natCast_pow_le_exp {a m : ℕ} {B : ℝ} (hB : 0 < B) (ha : (a : ℝ) ≤ B) :
    ((a ^ m : ℕ) : ℝ) ≤ exp (m * log B) := by
  rw [mul_comm, ← rpow_def_of_pos hB, rpow_natCast, Nat.cast_pow]
  exact pow_le_pow_left₀ a.cast_nonneg ha m

private lemma natCast_pow_mul_pow_le_exp {q s d : ℕ} {N B : ℝ} (hN : 0 < N) (hB : 1 ≤ B)
    (hq : (q : ℝ) ≤ N * B) (hs : (s : ℝ) ≤ B) :
    ((q ^ (d + 1) * s ^ d : ℕ) : ℝ) ≤ exp ((d + 1) * (log N + 2 * log B)) := by
  have hB₀ : 0 < B := by linarith
  rw [Nat.cast_mul]
  refine (mul_le_mul (natCast_pow_le_exp (mul_pos hN hB₀) hq) (natCast_pow_le_exp hB₀ hs)
    (by positivity) (by positivity)).trans ?_
  rw [← exp_add, exp_le_exp, log_mul hN.ne' hB₀.ne']
  push_cast
  linarith [log_nonneg hB]

private lemma natCast_succ_mul_pow_le_exp {m s : ℕ} {B T : ℝ} (hB : 1 ≤ B)
    (hm : ((m + 1 : ℕ) : ℝ) ≤ B) (hs : ((s + 1 : ℕ) : ℝ) ≤ B) (hT : ((m + 1 : ℕ) : ℝ) ≤ 2 * T) :
    (((m + 1) * (s + 1) ^ m : ℕ) : ℝ) ≤ exp (2 * T * log B) := by
  have hB₀ : 0 < B := by linarith
  have h := mul_le_mul_of_nonneg_right hT (log_nonneg hB)
  rw [Nat.cast_mul]
  refine (mul_le_mul (hm.trans_eq (exp_log hB₀).symm) (natCast_pow_le_exp hB₀ hs) (by positivity)
    (by positivity)).trans ?_
  rw [← exp_add, exp_le_exp]
  push_cast at h
  linarith

private lemma lower_negative_log_margin {γ C : ℝ} {n : ℕ} {δ : unitInterval} {d : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hd : (1 : ℝ) ≤ d) :
    (1 + ε γ) * ((d : ℝ) + 1) * log n ≤
      (1 - 3 * ε γ) * d * (pairCardThreshold (3 + γ) n δ : ℝ) * log (1 / δ) := by
  have hk := pairCardThreshold_arg_le (γ := γ) (n := n) (δ := δ)
  rw [div_le_iff₀ (log_one_div_unitInterval_pos
    (zero_lt_one.trans (one_lt_nat_of_lowerSizeThreshold_lt hn)) hδ_lower hδ_upper)] at hk
  have hd₀ : (0 : ℝ) ≤ d := zero_le_one.trans hd
  linarith [mul_le_mul_of_nonneg_left hk
      (mul_nonneg (one_sub_three_mul_ε_pos hγ_pos hγ_le).le hd₀),
    mul_le_mul_of_nonneg_right (lower_exponent_coefficient hγ_pos)
      (mul_nonneg hd₀ (log_natCast_nonneg n)),
    mul_nonneg (mul_nonneg (by linarith [ε_pos hγ_pos] : 0 ≤ 1 + ε γ) (log_natCast_nonneg n))
      (sub_nonneg.2 hd)]

private lemma lower_summand_exponent_le {γ C c : ℝ} {n : ℕ} {δ : unitInterval} {d : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ)
    (hd : d ∈ Finset.Icc 1 (pairCardThreshold (3 + γ) n δ)) :
    ((d : ℝ) + 1) * (log n +
        2 * log (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ))) +
        4 * lowerBltConstant C γ hC_two hε * √(pairCardThreshold (3 + γ) n δ : ℝ) *
          log (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ)) -
        (1 - 3 * ε γ) * d * (pairCardThreshold (3 + γ) n δ : ℝ) * log (1 / δ) ≤
      -(ε γ / 2) * log n := by
  obtain ⟨hd₁, -⟩ := mem_Icc.1 hd
  rify at hd₁
  have hlog := mul_nonneg hε.le (log_natCast_nonneg n)
  linarith [lower_negative_log_margin hγ_pos hγ_le hn hδ_lower hδ_upper hd₁,
    mul_le_mul_of_nonneg_left
      (lower_counting_base_log_le_epsilon_log_div_eight hγ_pos hC_one hc_pos hn hn_gap
        hδ_lower hδ_upper hδ_upper_c hC_two hε) (by positivity : 0 ≤ 2 * ((d : ℝ) + 1)),
    lower_c_sqrt_counting_base_log_le_epsilon_log_div_eight hγ_pos hγ_le hC_one hc_pos hc_lt hn
      hn_gap hδ_lower hδ_upper hδ_upper_c hC_two hε,
    mul_nonneg hlog (sub_nonneg.2 hd₁)]

/-- Let `k = pairCardThreshold (3 + γ) n δ`, `s = ⌈changCarrierBound (2 * k) (κ C)⌉₊` and
`m = ⌈lowerBltConstant C γ * √k⌉₊`. For `1 ≤ d ≤ k`, the number of proper progressions of
dimension `d` in `ZMod q` with at most `s` points, times `((m + 1) * (s + 1) ^ m) ^ 2`, times
`exp (-(1 - 3 * ε γ) * d * k * log (1 / δ))`, is at most `n ^ (-(ε γ / 2))`. -/
lemma lower_gap_dim_summand_le {γ C c : ℝ} {n : ℕ} {δ : unitInterval} {d : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (C_pos : 0 < C) (hC_one : 1 ≤ C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ)
    (hd : d ∈ Finset.Icc 1 (pairCardThreshold (3 + γ) n δ)) :
    (#(properGAPsZModOfDim d
        ⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊
        (zmodModelQ_prime hγ_pos C_pos hn).pos) : ℝ) *
        ((((⌈lowerBltConstant C γ hC_two hε * √(pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ + 1) *
            (⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ + 1) ^
              ⌈lowerBltConstant C γ hC_two hε * √(pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ : ℕ) : ℝ) *
          (((⌈lowerBltConstant C γ hC_two hε * √(pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ + 1) *
            (⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ + 1) ^
              ⌈lowerBltConstant C γ hC_two hε * √(pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ : ℕ) : ℝ)) *
        exp (-((1 - 3 * ε γ) * (d : ℝ) * (pairCardThreshold (3 + γ) n δ : ℝ)) * log (1 / δ)) ≤
      (n : ℝ) ^ (-(ε γ / 2)) := by
  have hn₀ := old_model_threshold_nat_pos hn
  have hB := one_le_lower_counting_base hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε
  have hgap := ((Nat.cast_le (α := ℝ)).2 (properGAPsZModOfDim_card (d := d)
    (zmodModelQ_prime hγ_pos C_pos hn).pos)).trans (natCast_pow_mul_pow_le_exp hn₀ hB
      (zmodModelQ_le_n_mul_lower_counting_base hγ_pos C_pos hC_one hn hδ_lower hδ_upper hC_two hε)
      (changCarrierBound_ceil_le_lower_counting_base hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε))
  have hsub := natCast_succ_mul_pow_le_exp hB
    (blt_ceiling_succ_le_lower_counting_base hγ_pos hγ_le hC_one hn hδ_lower hδ_upper hC_two hε)
    (changCarrierBound_ceil_succ_le_three_mul_lowerConstant hγ_pos hC_one hn hδ_lower hδ_upper
      hC_two hε)
    ((lower_blt_ceiling_succ_le_two_mul hγ_pos hγ_le hC_one hn hδ_lower hδ_upper hC_two
      hε).trans_eq (mul_assoc _ _ _))
  refine (mul_le_mul_of_nonneg_right (mul_le_mul hgap (mul_le_mul hsub hsub (by positivity)
    (by positivity)) (by positivity) (by positivity)) (by positivity)).trans ?_
  rw [← exp_add, ← exp_add, ← exp_add, rpow_def_of_pos hn₀, exp_le_exp]
  linarith [lower_summand_exponent_le hγ_pos hγ_le hC_one hc_pos hc_lt hn hn_gap hδ_lower hδ_upper
    hδ_upper_c hC_two hε hd]

end

end DenseSetsWithoutLargeSumsets
