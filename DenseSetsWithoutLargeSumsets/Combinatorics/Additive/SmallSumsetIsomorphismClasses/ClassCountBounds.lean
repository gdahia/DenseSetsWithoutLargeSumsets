/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.SmallSumsetIsomorphismClasses.CoreAndCovers

/-!
# Bounds for small-sumset Freiman classes

This submodule proves the analytic class-count estimates and the final realization bound.
-/

namespace DenseSetsWithoutLargeSumsets

open scoped Pointwise

noncomputable section

/-- The analytic absorption step in Green's Proposition 18(a).  This is deliberately separate
from the combinatorial assembly so it can be delegated as a pure inequality problem. -/
private lemma log_natCast_le_three_div_two_hundred_mul_rpow {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) :
    Real.log t ≤ (3 / 200 : ℝ) * (t : ℝ) ^ ((1 : ℝ) / 480) := by
  have ht_real : ((2 : ℝ) ^ (9000 : ℕ)) ≤ t := by
    have ht_nat : 2 ^ (9000 : ℕ) ≤ t := by
      rw [smallSumsetClassCountThreshold_def] at ht
      exact ht
    exact_mod_cast ht_nat
  have hlog_two_lower : (1 / 2 : ℝ) < Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hthreshold_exp : Real.exp ((480 : ℝ)) ≤ (2 : ℝ) ^ (9000 : ℕ) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (9000 : ℕ)),
      Real.exp_le_exp, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hq_power : (420000 : ℝ) ≤
      ((2 : ℝ) ^ (9000 : ℕ)) ^ ((1 : ℝ) / 480) := by
    apply (pow_le_pow_iff_left₀ (by positivity : (0 : ℝ) ≤ 420000)
      (Real.rpow_nonneg (by positivity) _) (by norm_num : (4 : ℕ) ≠ 0)).mp
    conv_rhs =>
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        ← Real.rpow_natCast (2 : ℝ) 9000, ← Real.rpow_mul (by positivity)]
      norm_num
    norm_num
  have hthreshold_log :
      Real.log ((2 : ℝ) ^ (9000 : ℕ)) ≤ (6246 : ℝ) := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith [Real.log_two_lt_d9]
  have hratio_threshold :
      Real.log ((2 : ℝ) ^ (9000 : ℕ)) /
          (((2 : ℝ) ^ (9000 : ℕ)) ^ ((1 : ℝ) / 480)) ≤ (3 / 200 : ℝ) := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).mpr
    nlinarith
  have hthreshold_mem : (2 : ℝ) ^ (9000 : ℕ) ∈
      Set.Ici (Real.exp ((1 / 480 : ℝ))⁻¹) := by
    rw [Set.mem_Ici]
    norm_num only [one_div, inv_inv]
    exact hthreshold_exp
  have ht_mem : (t : ℝ) ∈ Set.Ici (Real.exp ((1 / 480 : ℝ))⁻¹) := by
      rw [Set.mem_Ici]
      norm_num only [one_div, inv_inv]
      exact hthreshold_exp.trans ht_real
  have hratio := Real.log_div_self_rpow_antitoneOn (by norm_num : (0 : ℝ) < 1 / 480)
    hthreshold_mem ht_mem ht_real
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (by
    exact lt_of_lt_of_le (by positivity : (0 : ℝ) < (2 : ℝ) ^ (9000 : ℕ)) ht_real) _)).mp
      (hratio.trans hratio_threshold)

private lemma cast_choose_le_classCountScale_mul_exp {t m d : ℕ} (ht : 0 < t)
    (htm : t ≤ m) :
    (m.choose (t - d) : ℝ) ≤
      ((Real.exp 1 * (m : ℝ)) / (t : ℝ)) ^ t * Real.exp d := by
  let k := t - d
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast ht.trans_le htm
  have ht_real : (0 : ℝ) < t := by exact_mod_cast ht
  have hbase_one : 1 ≤ (Real.exp 1 * (m : ℝ)) / (t : ℝ) := by
    rw [le_div_iff₀ ht_real]
    have hexp_one : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith [(by exact_mod_cast htm : (t : ℝ) ≤ m)]
  by_cases hk : k = 0
  · change (m.choose k : ℝ) ≤ _
    simp only [hk, Nat.choose_zero_right, Nat.cast_one]
    have hpow : 1 ≤ ((Real.exp 1 * (m : ℝ)) / (t : ℝ)) ^ t :=
      one_le_pow₀ hbase_one
    nlinarith [Real.exp_pos (d : ℝ), Real.one_le_exp (Nat.cast_nonneg d)]
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
    have hk_le_t : k ≤ t := Nat.sub_le _ _
    have hsqrt_one : (1 : ℝ) ≤ √(2 * Real.pi * k) := by
      rw [← Real.sqrt_one]
      apply Real.sqrt_le_sqrt
      have hpi : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
      nlinarith [(by exact_mod_cast hk_pos : (1 : ℝ) ≤ k)]
    have hfac : ((k : ℝ) / Real.exp 1) ^ k ≤ (k.factorial : ℝ) := by
      exact (le_mul_of_one_le_left (by positivity) hsqrt_one).trans
        (Stirling.le_factorial_stirling k)
    have hchoose_scale : (m.choose k : ℝ) ≤
        ((Real.exp 1 * (m : ℝ)) / (k : ℝ)) ^ k := by
      refine (Nat.choose_le_pow_div k m).trans ?_
      rw [div_pow]
      convert
        (div_le_div_iff_of_pos_left (by positivity : 0 < (m : ℝ) ^ k)
          (by positivity : 0 < (k.factorial : ℝ))
          (by positivity : 0 < ((k : ℝ) / Real.exp 1) ^ k)).mpr hfac using 1
      rw [mul_pow, div_pow]
      field_simp
    have ht_eq : t = k + d := by
      dsimp only [k]
      omega
    have hratio : ((t : ℝ) / (k : ℝ)) ^ k ≤ Real.exp d := by
      convert Real.one_sub_div_pow_le_exp_neg (n := k) (t := -(d : ℝ)) (by
        exact (neg_nonpos.mpr (Nat.cast_nonneg d)).trans (Nat.cast_nonneg k)) using 1
      · congr 1
        rw [ht_eq]
        push_cast
        field_simp
        ring
      · norm_num
    change (m.choose k : ℝ) ≤ _
    refine hchoose_scale.trans ?_
    convert mul_le_mul (pow_le_pow_right₀ hbase_one hk_le_t) hratio
      (by positivity) (by positivity) using 1
    rw [← mul_pow]
    congr 1
    field_simp

private lemma four_hundred_twenty_thousand_le_rpow {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) :
    (420000 : ℝ) ≤ (t : ℝ) ^ ((1 : ℝ) / 480) := by
  have ht_real : ((2 : ℝ) ^ (9000 : ℕ)) ≤ t := by
    have ht_nat : 2 ^ (9000 : ℕ) ≤ t := by
      rw [smallSumsetClassCountThreshold_def] at ht
      exact ht
    exact_mod_cast ht_nat
  have hthreshold : (420000 : ℝ) ≤
      ((2 : ℝ) ^ (9000 : ℕ)) ^ ((1 : ℝ) / 480) := by
    apply (pow_le_pow_iff_left₀ (by positivity : (0 : ℝ) ≤ 420000)
      (Real.rpow_nonneg (by positivity) _) (by norm_num : (4 : ℕ) ≠ 0)).mp
    conv_rhs =>
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        ← Real.rpow_natCast (2 : ℝ) 9000, ← Real.rpow_mul (by positivity)]
      norm_num
    norm_num
  exact hthreshold.trans (Real.rpow_le_rpow (by positivity) ht_real (by norm_num))

private lemma coreClassCost_le {t m : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (m : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
    16 * (coreCardBound t m : ℝ) * Real.log t ≤
      (97 / 100 : ℝ) * (t : ℝ) ^ ((31 : ℝ) / 32) := by
  have ht_pos : 0 < t :=
    Nat.zero_lt_of_lt (one_lt_of_smallSumsetClassCountThreshold_le ht)
  have ht_real : (0 : ℝ) < t := by exact_mod_cast ht_pos
  let q : ℝ := (t : ℝ) ^ ((1 : ℝ) / 480)
  let A : ℝ := (t : ℝ) ^ ((29 : ℝ) / 30)
  let E : ℝ := (t : ℝ) ^ ((31 : ℝ) / 32)
  have hq : 420000 ≤ q := four_hundred_twenty_thousand_le_rpow ht
  have hlog : Real.log t ≤ (3 / 200 : ℝ) * q :=
    log_natCast_le_three_div_two_hundred_mul_rpow ht
  have hAq : A * q = E := by
    dsimp only [A, q, E]
    rw [← Real.rpow_add ht_real]
    congr 1
    norm_num
  have hA_large : 420000 ≤ A := by
    exact hq.trans (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (one_lt_of_smallSumsetClassCountThreshold_le ht).le) (by norm_num))
  have hcore_real : (coreCardBound t m : ℝ) ≤ 4 * A + 1 := by
    unfold coreCardBound
    refine (Nat.ceil_lt_add_one (mul_nonneg
      (mul_nonneg (by norm_num) (coreSamplingRate_pos ht).le)
      (Nat.cast_nonneg m))).le.trans ?_
    have hsampling : coreSamplingRate t * (t : ℝ) ^ ((31 : ℝ) / 30) = A := by
      dsimp only [A]
      unfold coreSamplingRate
      rw [← Real.rpow_add ht_real]
      congr 1
      norm_num
    nlinarith [mul_le_mul_of_nonneg_left hm
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (coreSamplingRate_pos ht).le)]
  have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg (by exact_mod_cast ht_pos)
  have hfirst := mul_le_mul_of_nonneg_right hcore_real hlog_nonneg
  have hsecond := mul_le_mul_of_nonneg_left hlog
    (by positivity : 0 ≤ 16 * (4 * A + 1))
  have hq_nonneg : 0 ≤ q := by positivity
  have hA_nonneg : 0 ≤ A := by positivity
  have hsmall : (24 / 100 : ℝ) * q ≤ (1 / 100 : ℝ) * E := by
    nlinarith [hAq, mul_nonneg hA_nonneg hq_nonneg]
  nlinarith [hAq]

private lemma extensionClassCost_le {t m : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (m : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
    5 * ((exceptionCardBound t m : ℝ) + 1) ^ (4 : ℕ) * Real.log t ≤
      (1 / 100 : ℝ) * (t : ℝ) ^ ((31 : ℝ) / 32) := by
  have ht_pos : 0 < t :=
    Nat.zero_lt_of_lt (one_lt_of_smallSumsetClassCountThreshold_le ht)
  have ht_real : (0 : ℝ) < t := by exact_mod_cast ht_pos
  let q : ℝ := (t : ℝ) ^ ((1 : ℝ) / 480)
  let B : ℝ := (t : ℝ) ^ ((7 : ℝ) / 30)
  let C : ℝ := (t : ℝ) ^ ((449 : ℝ) / 480)
  let R : ℝ := (t : ℝ) ^ ((1 : ℝ) / 30)
  let E : ℝ := (t : ℝ) ^ ((31 : ℝ) / 32)
  have hq : 420000 ≤ q := four_hundred_twenty_thousand_le_rpow ht
  have hlog : Real.log t ≤ (3 / 200 : ℝ) * q :=
    log_natCast_le_three_div_two_hundred_mul_rpow ht
  have hR_large : 420000 ≤ R := by
    exact hq.trans (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (one_lt_of_smallSumsetClassCountThreshold_le ht).le) (by norm_num))
  have hCR : C * R = E := by
    dsimp only [C, R, E]
    rw [← Real.rpow_add ht_real]
    congr 1
    norm_num
  have hBfourq : B ^ (4 : ℕ) * q = C := by
    dsimp only [B, q, C]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht_real.le,
      ← Real.rpow_add ht_real]
    congr 1
    norm_num
  have hB_one : 1 ≤ B := by
    dsimp only [B]
    exact Real.one_le_rpow (by exact_mod_cast ht_pos) (by norm_num)
  have hexception_real : (exceptionCardBound t m : ℝ) ≤ 4 * B + 1 := by
    unfold exceptionCardBound
    refine (Nat.ceil_lt_add_one (by positivity :
      0 ≤ 4 * (t : ℝ) ^ (-(4 : ℝ) / 5) * (m : ℝ))).le.trans ?_
    have hpower : (t : ℝ) ^ (-(4 : ℝ) / 5) *
        (t : ℝ) ^ ((31 : ℝ) / 30) = B := by
      dsimp only [B]
      rw [← Real.rpow_add ht_real]
      congr 1
      norm_num
    nlinarith [mul_le_mul_of_nonneg_left hm
      (by positivity : 0 ≤ 4 * (t : ℝ) ^ (-(4 : ℝ) / 5))]
  have hDplus : (exceptionCardBound t m : ℝ) + 1 ≤ 6 * B := by
    nlinarith
  have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg (by exact_mod_cast ht_pos)
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
    (exceptionCardBound t m : ℝ) + 1) hDplus 4
  have hfirst := mul_le_mul_of_nonneg_right hpow hlog_nonneg
  have hsecond := mul_le_mul_of_nonneg_left hlog
    (by positivity : 0 ≤ 5 * (6 * B) ^ (4 : ℕ))
  have hC_nonneg : 0 ≤ C := by positivity
  have hR_nonneg : 0 ≤ R := by positivity
  have hsmall : (972 / 10 : ℝ) * C ≤ (1 / 100 : ℝ) * E := by
    nlinarith [hCR, mul_nonneg hC_nonneg hR_nonneg]
  nlinarith [hBfourq]

private lemma exceptionCountCost_le {t m : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (m : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
    (exceptionCardBound t m : ℝ) ≤
      (1 / 1000 : ℝ) * (t : ℝ) ^ ((31 : ℝ) / 32) := by
  have ht_pos : 0 < t :=
    Nat.zero_lt_of_lt (one_lt_of_smallSumsetClassCountThreshold_le ht)
  have ht_real : (0 : ℝ) < t := by exact_mod_cast ht_pos
  let q : ℝ := (t : ℝ) ^ ((1 : ℝ) / 480)
  let B : ℝ := (t : ℝ) ^ ((7 : ℝ) / 30)
  let C : ℝ := (t : ℝ) ^ ((449 : ℝ) / 480)
  let R : ℝ := (t : ℝ) ^ ((1 : ℝ) / 30)
  let E : ℝ := (t : ℝ) ^ ((31 : ℝ) / 32)
  have hq : 420000 ≤ q := four_hundred_twenty_thousand_le_rpow ht
  have hR_large : 420000 ≤ R := by
    exact hq.trans (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (one_lt_of_smallSumsetClassCountThreshold_le ht).le) (by norm_num))
  have hCR : C * R = E := by
    dsimp only [C, R, E]
    rw [← Real.rpow_add ht_real]
    congr 1
    norm_num
  have hB_le_C : B ≤ C := by
    dsimp only [B, C]
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (one_lt_of_smallSumsetClassCountThreshold_le ht).le) (by norm_num)
  have hB_one : 1 ≤ B := by
    dsimp only [B]
    exact Real.one_le_rpow (by exact_mod_cast ht_pos) (by norm_num)
  have hexception_real : (exceptionCardBound t m : ℝ) ≤ 4 * B + 1 := by
    unfold exceptionCardBound
    refine (Nat.ceil_lt_add_one (by positivity :
      0 ≤ 4 * (t : ℝ) ^ (-(4 : ℝ) / 5) * (m : ℝ))).le.trans ?_
    have hpower : (t : ℝ) ^ (-(4 : ℝ) / 5) *
        (t : ℝ) ^ ((31 : ℝ) / 30) = B := by
      dsimp only [B]
      rw [← Real.rpow_add ht_real]
      congr 1
      norm_num
    nlinarith [mul_le_mul_of_nonneg_left hm
      (by positivity : 0 ≤ 4 * (t : ℝ) ^ (-(4 : ℝ) / 5))]
  have hC_nonneg : 0 ≤ C := by positivity
  have hR_nonneg : 0 ≤ R := by positivity
  have hsmall : 5 * C ≤ (1 / 1000 : ℝ) * E := by
    nlinarith [hCR, mul_nonneg hC_nonneg hR_nonneg]
  nlinarith

private lemma coreCardBound_le_t {t m : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (m : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
    coreCardBound t m ≤ t := by
  have ht_pos : 0 < t :=
    Nat.zero_lt_of_lt (one_lt_of_smallSumsetClassCountThreshold_le ht)
  have ht_real : (0 : ℝ) < t := by exact_mod_cast ht_pos
  let q : ℝ := (t : ℝ) ^ ((1 : ℝ) / 480)
  let A : ℝ := (t : ℝ) ^ ((29 : ℝ) / 30)
  let R : ℝ := (t : ℝ) ^ ((1 : ℝ) / 30)
  have hq : 420000 ≤ q := four_hundred_twenty_thousand_le_rpow ht
  have hR_large : 420000 ≤ R := by
    exact hq.trans (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (one_lt_of_smallSumsetClassCountThreshold_le ht).le) (by norm_num))
  have hAR : A * R = (t : ℝ) := by
    dsimp only [A, R]
    rw [← Real.rpow_add ht_real]
    convert Real.rpow_one (t : ℝ) using 1
    all_goals norm_num
  have hcore_real : (coreCardBound t m : ℝ) ≤ 4 * A + 1 := by
    unfold coreCardBound
    refine (Nat.ceil_lt_add_one (mul_nonneg
      (mul_nonneg (by norm_num) (coreSamplingRate_pos ht).le)
      (Nat.cast_nonneg m))).le.trans ?_
    have hsampling : coreSamplingRate t * (t : ℝ) ^ ((31 : ℝ) / 30) = A := by
      dsimp only [A]
      unfold coreSamplingRate
      rw [← Real.rpow_add ht_real]
      congr 1
      norm_num
    nlinarith [mul_le_mul_of_nonneg_left hm
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (coreSamplingRate_pos ht).le)]
  have hA_nonneg : 0 ≤ A := by positivity
  have hA_one : 1 ≤ A := by
    dsimp only [A]
    exact Real.one_le_rpow (by exact_mod_cast ht_pos) (by norm_num)
  have hR_nonneg : 0 ≤ R := by positivity
  have : (coreCardBound t m : ℝ) ≤ t := by
    nlinarith [hAR, mul_nonneg hA_nonneg hR_nonneg]
  exact_mod_cast this

private lemma freimanClassCountTerm_le {t m d l : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) (htm : t ≤ m)
    (hm : (m : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30))
    (hd : d ∈ Finset.range (exceptionCardBound t m + 1))
    (hl : l ∈ Finset.Icc 1 (coreCardBound t m)) :
    (l ^ (16 * l) * m.choose (t - d) *
        (1 + (t - d) ^ 4) ^ ((d + 1) ^ 4) : ℕ) ≤
      ((Real.exp 1 * (m : ℝ)) / (t : ℝ)) ^ t *
        Real.exp ((99 / 100 : ℝ) * (t : ℝ) ^ ((31 : ℝ) / 32)) := by
  have ht_pos : 0 < t :=
    Nat.zero_lt_of_lt (one_lt_of_smallSumsetClassCountThreshold_le ht)
  have ht_real : (0 : ℝ) < t := by exact_mod_cast ht_pos
  have ht_two : (2 : ℝ) ≤ t := by
    exact_mod_cast (one_lt_of_smallSumsetClassCountThreshold_le ht)
  let E : ℝ := (t : ℝ) ^ ((31 : ℝ) / 32)
  let scale : ℝ := ((Real.exp 1 * (m : ℝ)) / (t : ℝ)) ^ t
  have hl_pos : 0 < l := by
    have := (Finset.mem_Icc.mp hl).1
    omega
  have hl_core : l ≤ coreCardBound t m := (Finset.mem_Icc.mp hl).2
  have hcore_code : (l ^ (16 * l) : ℝ) ≤
      Real.exp (16 * (coreCardBound t m : ℝ) * Real.log t) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by exact_mod_cast hl_pos)]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith [mul_le_mul
      (by exact_mod_cast hl_core : (l : ℝ) ≤ coreCardBound t m)
      (Real.log_le_log (by exact_mod_cast hl_pos : (0 : ℝ) < l)
        (by exact_mod_cast hl_core.trans (coreCardBound_le_t ht hm) : (l : ℝ) ≤ t))
      (Real.log_nonneg (by exact_mod_cast hl_pos : (1 : ℝ) ≤ l))
      (Nat.cast_nonneg (coreCardBound t m))]
  have hd_bound : d ≤ exceptionCardBound t m := by
    have := Finset.mem_range.mp hd
    omega
  have hd_real : (d : ℝ) ≤ (1 / 1000 : ℝ) * E :=
    (by exact_mod_cast hd_bound : (d : ℝ) ≤ exceptionCardBound t m).trans
      (exceptionCountCost_le ht hm)
  have hk_le : t - d ≤ t := Nat.sub_le _ _
  have hk_real : ((t - d : ℕ) : ℝ) ≤ t := by exact_mod_cast hk_le
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (t - d)) hk_real 4
  have hbase_le : (1 + ((t - d : ℕ) : ℝ) ^ (4 : ℕ)) ≤
      (t : ℝ) ^ (5 : ℕ) := by
    have hmul := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ (t : ℝ))
    norm_num only [pow_succ] at hmul ⊢
    nlinarith [(by
      exact one_le_pow₀ (by exact_mod_cast ht_pos) : (1 : ℝ) ≤ t ^ (4 : ℕ))]
  have hlog_base : Real.log (1 + ((t - d : ℕ) : ℝ) ^ (4 : ℕ)) ≤
      5 * Real.log t := by
    calc
      Real.log (1 + ((t - d : ℕ) : ℝ) ^ (4 : ℕ)) ≤
          Real.log ((t : ℝ) ^ (5 : ℕ)) := Real.log_le_log (by positivity) hbase_le
      _ = 5 * Real.log t := by rw [Real.log_pow]; norm_num
  have hdplus : ((d + 1 : ℕ) : ℝ) ≤
      (exceptionCardBound t m : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hd_bound 1
  have hdplus_pow := pow_le_pow_left₀ (Nat.cast_nonneg (d + 1)) hdplus 4
  have hextension_code : (((1 + (t - d) ^ 4) ^ ((d + 1) ^ 4) : ℕ) : ℝ) ≤
      Real.exp (5 * ((exceptionCardBound t m : ℝ) + 1) ^ (4 : ℕ) *
        Real.log t) := by
    push_cast
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity)]
    apply Real.exp_le_exp.mpr
    push_cast
    have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg (by exact_mod_cast ht_pos)
    have hlog_base_nonneg :
        0 ≤ Real.log (1 + ((t - d : ℕ) : ℝ) ^ (4 : ℕ)) :=
      Real.log_nonneg (le_add_of_nonneg_right (by positivity))
    have hprod : ((d + 1 : ℕ) : ℝ) ^ (4 : ℕ) *
        Real.log (1 + ((t - d : ℕ) : ℝ) ^ (4 : ℕ)) ≤
          ((exceptionCardBound t m : ℝ) + 1) ^ (4 : ℕ) *
            (5 * Real.log t) := by
      exact mul_le_mul hdplus_pow hlog_base hlog_base_nonneg (by positivity)
    convert hprod using 1 <;> push_cast <;> ring
  have hbinomial_factor := cast_choose_le_classCountScale_mul_exp ht_pos htm (d := d)
  have hcost :
      16 * (coreCardBound t m : ℝ) * Real.log t +
          5 * ((exceptionCardBound t m : ℝ) + 1) ^ (4 : ℕ) * Real.log t + d ≤
        (99 / 100 : ℝ) * E := by
    nlinarith [coreClassCost_le ht hm, extensionClassCost_le ht hm]
  norm_num only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] at hextension_code
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  apply le_trans (b :=
    Real.exp (16 * (coreCardBound t m : ℝ) * Real.log t) *
      (scale * Real.exp d) *
        Real.exp (5 * ((exceptionCardBound t m : ℝ) + 1) ^ (4 : ℕ) * Real.log t))
  · exact mul_le_mul (mul_le_mul hcore_code hbinomial_factor (by positivity) (by positivity))
      hextension_code (by positivity) (by positivity)
  convert mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcost) (by positivity : 0 ≤ scale)
    using 1
  · rw [Real.exp_add, Real.exp_add]
    ring

private lemma classCountSummationRange_le {t m : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (m : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
    ((exceptionCardBound t m + 1) * coreCardBound t m : ℕ) ≤
      Real.exp ((1 / 100 : ℝ) * (t : ℝ) ^ ((31 : ℝ) / 32)) := by
  have ht_pos : 0 < t :=
    Nat.zero_lt_of_lt (one_lt_of_smallSumsetClassCountThreshold_le ht)
  have ht_real : (0 : ℝ) < t := by exact_mod_cast ht_pos
  let q : ℝ := (t : ℝ) ^ ((1 : ℝ) / 480)
  let A : ℝ := (t : ℝ) ^ ((29 : ℝ) / 30)
  let E : ℝ := (t : ℝ) ^ ((31 : ℝ) / 32)
  have hq : 420000 ≤ q := four_hundred_twenty_thousand_le_rpow ht
  have hlog : Real.log t ≤ (3 / 200 : ℝ) * q :=
    log_natCast_le_three_div_two_hundred_mul_rpow ht
  have hAq : A * q = E := by
    dsimp only [A, q, E]
    rw [← Real.rpow_add ht_real]
    congr 1
    norm_num
  have hA_large : 420000 ≤ A := by
    exact hq.trans (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (one_lt_of_smallSumsetClassCountThreshold_le ht).le) (by norm_num))
  have hE_le_t : E ≤ t := by
    dsimp only [E]
    convert Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (one_lt_of_smallSumsetClassCountThreshold_le ht).le :
        (1 : ℝ) ≤ (t : ℝ))
      (by norm_num : (31 : ℝ) / 32 ≤ 1) using 1
    exact (Real.rpow_one (t : ℝ)).symm
  have hD : (exceptionCardBound t m : ℝ) ≤ (1 / 1000 : ℝ) * E :=
    exceptionCountCost_le ht hm
  have hDplus : (exceptionCardBound t m + 1 : ℕ) ≤ t := by
    exact_mod_cast (by
      have ht_two : (2 : ℝ) ≤ t := by
        exact_mod_cast one_lt_of_smallSumsetClassCountThreshold_le ht
      nlinarith : (exceptionCardBound t m : ℝ) + 1 ≤ t)
  have hlog_cost : 2 * Real.log t ≤ (1 / 100 : ℝ) * E := by
    have hq_nonneg : 0 ≤ q := by positivity
    have hA_nonneg : 0 ≤ A := by positivity
    nlinarith [hAq, mul_nonneg hA_nonneg hq_nonneg]
  apply le_trans (b := Real.exp (2 * Real.log t))
  · apply le_trans (b := (t * t : ℝ))
    · exact_mod_cast Nat.mul_le_mul hDplus (coreCardBound_le_t ht hm)
    simp [two_mul, Real.exp_add, Real.exp_log ht_real]
  apply Real.exp_le_exp.mpr
  norm_num
  simpa only [E, Real.exp_log ht_real] using hlog_cost

lemma freimanClassCountBound_le {t m : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) (htm : t ≤ m)
    (hm : (m : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
    (freimanClassCountBound t m : ℝ) ≤
      ((Real.exp 1 * (m : ℝ)) / (t : ℝ)) ^ t *
        Real.exp ((t : ℝ) ^ ((31 : ℝ) / 32)) := by
  let E : ℝ := (t : ℝ) ^ ((31 : ℝ) / 32)
  let scale : ℝ := ((Real.exp 1 * (m : ℝ)) / (t : ℝ)) ^ t
  have hterm (d : ℕ) (hd : d ∈ Finset.range (exceptionCardBound t m + 1))
      (l : ℕ) (hl : l ∈ Finset.Icc 1 (coreCardBound t m)) :
      (l ^ (16 * l) * m.choose (t - d) *
          (1 + (t - d) ^ 4) ^ ((d + 1) ^ 4) : ℕ) ≤
        scale * Real.exp ((99 / 100 : ℝ) * E) :=
    freimanClassCountTerm_le ht htm hm hd hl
  have hrange := classCountSummationRange_le ht hm
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] at hterm
  unfold freimanClassCountBound
  norm_num only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  calc
    ∑ d ∈ Finset.range (exceptionCardBound t m + 1),
        ∑ l ∈ Finset.Icc 1 (coreCardBound t m),
          (l : ℝ) ^ (16 * l) * (m.choose (t - d) : ℝ) *
            (1 + ((t - d : ℕ) : ℝ) ^ 4) ^ ((d + 1) ^ 4) ≤
        ∑ d ∈ Finset.range (exceptionCardBound t m + 1),
          ∑ _ ∈ Finset.Icc 1 (coreCardBound t m),
            scale * Real.exp ((99 / 100 : ℝ) * E) := by
      refine Finset.sum_le_sum fun d hd => ?_
      exact Finset.sum_le_sum fun l hl => hterm d hd l hl
    _ = ((exceptionCardBound t m + 1) * coreCardBound t m : ℕ) *
        (scale * Real.exp ((99 / 100 : ℝ) * E)) := by
      simp
      ring
    _ ≤ Real.exp ((1 / 100 : ℝ) * E) *
        (scale * Real.exp ((99 / 100 : ℝ) * E)) := by
      gcongr
    _ = scale * Real.exp E := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ = ((Real.exp 1 * (m : ℝ)) / (t : ℝ)) ^ t *
        Real.exp ((t : ℝ) ^ ((31 : ℝ) / 32)) := rfl

/-- Green's Proposition 18(a), phrased without quotient types: a finite set of representatives
covers every relevant `2`-relation class. -/
theorem exists_smallRestrictedSumsetFreimanClassCover {t m : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (m : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30)) :
    ∃ representatives : Finset (Finset ℕ),
      CoversFreimanClasses 2 (smallRestrictedSumsetSets t m) representatives ∧
      (representatives.card : ℝ) ≤
        ((Real.exp 1 * (m : ℝ)) / (t : ℝ)) ^ t *
          Real.exp ((t : ℝ) ^ ((31 : ℝ) / 32)) := by
  by_cases htm : t ≤ m
  · obtain ⟨representatives, hcover, hcard⟩ :=
      exists_smallRestrictedSumsetFreimanClassCover_raw t m ht
    refine ⟨representatives, hcover, ?_⟩
    have hcard_real : (representatives.card : ℝ) ≤ freimanClassCountBound t m := by
      exact_mod_cast hcard
    exact hcard_real.trans (freimanClassCountBound_le ht htm hm)
  · refine ⟨(∅ : Finset (Finset ℕ)), ?_, ?_⟩
    · intro A hA
      rcases hA with ⟨hA_card, hsum⟩
      have hA_three : 3 ≤ A.card := by
        rw [hA_card]
        exact ht.trans'
          (two_pow_200_le_smallSumsetClassCountThreshold.trans' (by norm_num))
      have : t ≤ m := by
        rw [← hA_card]
        exact (card_le_card_restrictedSumset_of_three_le A hA_three).trans hsum
      exact (htm this).elim
    · simp only [Finset.card_empty, Nat.cast_zero]
      positivity

/-- Realizations in `[n]` of one fixed `2`-relation class, with the required dimension bound. -/
def freimanClassRealizations (n r t : ℕ) (representative : Finset ℕ) :
    Set (Finset ℕ) :=
  {X | X ⊆ interval n ∧ X.card = t ∧ freimanDim X ≤ r ∧
    FreimanEquivalent 2 X representative}

/-- Green's Lemma 4(i): a fixed class of Freiman dimension at most `r` has at most
`n^(r+1)` realizations in `[n]`. -/
lemma ncard_freimanClassRealizations_le (n r t : ℕ) (representative : Finset ℕ)
    (ht : 0 < t) :
    ((freimanClassRealizations n r t representative).ncard : ℝ) ≤
      (n : ℝ) ^ (r + 1) := by
  classical
  let family := freimanClassRealizations n r t representative
  change (family.ncard : ℝ) ≤ (n : ℝ) ^ (r + 1)
  have hfinite : family.Finite := by
    apply (interval n).powerset.finite_toSet.subset
    intro X hX
    exact Finset.mem_powerset.mpr hX.1
  by_cases hfamily : family = ∅
  · rw [hfamily, Set.ncard_empty]
    norm_num only [Nat.cast_zero]
    exact pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) _
  · let Member := {X : Finset ℕ // X ∈ family}
    letI : Fintype Member := hfinite.fintype
    let X₀ : Member := ⟨Classical.choose (Set.nonempty_iff_ne_empty.mpr hfamily),
      Classical.choose_spec (Set.nonempty_iff_ne_empty.mpr hfamily)⟩
    have hX₀_card : X₀.1.card = t := X₀.2.2.1
    let a : Fin t → ℕ := finsetTuple X₀.1 hX₀_card
    have ha_mem (i : Fin t) : a i ∈ X₀.1 := by
      exact (X₀.1.orderIsoOfFin hX₀_card i).2
    have hiso_exists (X : Member) :
        ∃ f : ℕ → ℕ, IsAddFreimanIso 2 (X₀.1 : Set ℕ) (X.1 : Set ℕ) f := by
      obtain ⟨f₀, hf₀⟩ := X₀.2.2.2.2
      obtain ⟨f, hf⟩ := X.2.2.2.2
      exact ⟨Function.invFunOn f (X.1 : Set ℕ) ∘ f₀, hf.invFunOn.comp hf₀⟩
    let iso (X : Member) : ℕ → ℕ := Classical.choose (hiso_exists X)
    have hiso (X : Member) :
        IsAddFreimanIso 2 (X₀.1 : Set ℕ) (X.1 : Set ℕ) (iso X) :=
      Classical.choose_spec (hiso_exists X)
    let b (X : Member) : Fin t → ℕ := iso X ∘ a
    have hb_range (X : Member) : Set.range (b X) = X.1 := by
      change Set.range (iso X ∘ a) = X.1
      rw [Set.range_comp, range_finsetTuple X₀.1 hX₀_card]
      exact (hiso X).bijOn.image_eq
    have hdim : relationModelDim a ≤ r := by
      exact (relationModelDim_le_freimanDim ht ⟨X₀.1, hX₀_card⟩).trans
        X₀.2.2.2.1
    obtain ⟨anchor, hanchor_span⟩ := exists_determiningCoordinates ht a hdim
    let encoding (X : Member) : Fin (r + 1) → ↑(interval n) := fun i =>
      ⟨b X (anchor i), X.2.1 (by
        have hi : b X (anchor i) ∈ Set.range (b X) := Set.mem_range_self _
        rw [hb_range X] at hi
        exact hi)⟩
    have hrelations (X : Member) (p : RelationIndex t) :
        relationHolds a p ↔ relationHolds (b X) p := by
      have hsum := (hiso X).map_sum_eq_map_sum
        (s := {a p.1, a p.2.1}) (t := {a p.2.2.1, a p.2.2.2})
        (by simpa using ⟨ha_mem p.1, ha_mem p.2.1⟩)
        (by simpa using ⟨ha_mem p.2.2.1, ha_mem p.2.2.2⟩)
        (by simp) (by simp)
      change (iso X (a p.1) + iso X (a p.2.1) =
          iso X (a p.2.2.1) + iso X (a p.2.2.2) ↔
        a p.1 + a p.2.1 = a p.2.2.1 + a p.2.2.2) at hsum
      exact hsum.symm
    have hencoding_injective : Function.Injective encoding := by
      intro X Y hXY
      have hanchors : ∀ i, b X (anchor i) = b Y (anchor i) := by
        intro i
        exact congrArg Subtype.val (congrFun hXY i)
      have htuple : b X = b Y :=
        tuple_eq_of_relations_of_determiningCoordinates a (b X) (b Y) anchor
          hanchor_span (hrelations X) (hrelations Y) hanchors
      apply Subtype.ext
      apply Finset.coe_injective
      rw [← hb_range X, ← hb_range Y, htuple]
    have hcard := Fintype.card_le_of_injective encoding hencoding_injective
    rw [Set.fintypeCard_eq_ncard] at hcard
    rw [Fintype.card_fun, Fintype.card_coe] at hcard
    have hcard_nat : family.ncard ≤ n ^ (r + 1) := by
      simpa [interval] using hcard
    exact_mod_cast hcard_nat

/-- Final assembly of class representatives and their realizations.  Filling this lemma removes
the need to transport the integer problem into `ZMod q`. -/
theorem smallSumsetFreimanDimSets_ncard_le_of_class_cover (n r s t : ℕ)
    (ht : smallSumsetClassCountThreshold ≤ t)
    (hs : (s : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30) / 2) :
    ((smallSumsetFreimanDimSets n r s t).ncard : ℝ) ≤
      (n : ℝ) ^ (r + 1) *
        ((2 * Real.exp 1 * (s : ℝ)) / (t : ℝ)) ^ t *
          Real.exp ((t : ℝ) ^ ((31 : ℝ) / 32)) := by
  classical
  have ht_pos : 0 < t :=
    Nat.zero_lt_of_lt (one_lt_of_smallSumsetClassCountThreshold_le ht)
  have hm : ((2 * s : ℕ) : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  obtain ⟨representatives, hcover, hrepresentatives⟩ :=
    exists_smallRestrictedSumsetFreimanClassCover ht hm
  have hrealizations_finite (B : Finset ℕ) :
      (freimanClassRealizations n r t B).Finite := by
    apply (interval n).powerset.finite_toSet.subset
    intro X hX
    exact Finset.mem_powerset.mpr hX.1
  let realizationFinset (B : Finset ℕ) : Finset (Finset ℕ) :=
    (hrealizations_finite B).toFinset
  let allRealizations : Finset (Finset ℕ) :=
    representatives.biUnion realizationFinset
  have hsubset : smallSumsetFreimanDimSets n r s t ⊆
      (allRealizations : Set (Finset ℕ)) := by
    intro X hX
    have hrestricted : (restrictedSumset X).card ≤ 2 * s := by
      exact (card_restrictedSumset_le_card_add X).trans (hX.2.2.2.trans (by omega))
    obtain ⟨B, hB, hXB⟩ := hcover X ⟨hX.2.1, hrestricted⟩
    rw [Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨B, hB, ?_⟩
    exact (hrealizations_finite B).mem_toFinset.mpr
      ⟨hX.1, hX.2.1, hX.2.2.1, hXB⟩
  have hcard_nat : (smallSumsetFreimanDimSets n r s t).ncard ≤
      representatives.card * n ^ (r + 1) := by
    calc
      (smallSumsetFreimanDimSets n r s t).ncard ≤
          (allRealizations : Set (Finset ℕ)).ncard := Set.ncard_le_ncard hsubset
      _ = allRealizations.card := Set.ncard_coe_finset allRealizations
      _ ≤ ∑ B ∈ representatives, (realizationFinset B).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ representatives, n ^ (r + 1) := by
        refine Finset.sum_le_sum fun B hB => ?_
        change (hrealizations_finite B).toFinset.card ≤ n ^ (r + 1)
        rw [← Set.ncard_eq_toFinset_card (freimanClassRealizations n r t B)
          (hrealizations_finite B)]
        exact_mod_cast ncard_freimanClassRealizations_le n r t B ht_pos
      _ = representatives.card * n ^ (r + 1) := by simp
  have hcard_real : ((smallSumsetFreimanDimSets n r s t).ncard : ℝ) ≤
      (representatives.card : ℝ) * (n : ℝ) ^ (r + 1) := by
    exact_mod_cast hcard_nat
  calc
    ((smallSumsetFreimanDimSets n r s t).ncard : ℝ) ≤
        (representatives.card : ℝ) * (n : ℝ) ^ (r + 1) := hcard_real
    _ = (n : ℝ) ^ (r + 1) * representatives.card := by ring
    _ ≤ (n : ℝ) ^ (r + 1) *
        (((Real.exp 1 * ((2 * s : ℕ) : ℝ)) / (t : ℝ)) ^ t *
          Real.exp ((t : ℝ) ^ ((31 : ℝ) / 32))) :=
      mul_le_mul_of_nonneg_left hrepresentatives (by positivity)
    _ = (n : ℝ) ^ (r + 1) *
        ((2 * Real.exp 1 * (s : ℝ)) / (t : ℝ)) ^ t *
          Real.exp ((t : ℝ) ^ ((31 : ℝ) / 32)) := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      ring


end

end DenseSetsWithoutLargeSumsets
