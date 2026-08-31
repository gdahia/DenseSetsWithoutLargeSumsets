/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.CountingSumsetsOfModerateSize.Enumeration
import DenseSetsWithoutLargeSumsets.SimpleBoundForVeryLargeSumsets

/-!
# Probability bounds for moderate sumsets

This submodule turns the enumeration bounds into the moderate-sumset probability estimate.
-/

namespace DenseSetsWithoutLargeSumsets

open scoped Pointwise

noncomputable section

/-- The event associated with the moderate-sumset range. -/
def moderateSumsetEvent (n k : ℕ) (C : ℝ) (S : Finset ℕ) : Prop :=
  ∃ A B : Finset ℕ,
    A ⊆ interval n ∧ B ⊆ interval n ∧ A.card = k ∧ B.card = k ∧
      C * (k : ℝ) < ((A + B).card : ℝ) ∧
        (A + B).card < k * (k + 1) / 2 ∧ A + B ⊆ S

private def moderateSumsetSumsetSlice (n k m : ℕ) : Finset (Finset ℕ) := by
  classical
  exact
    ((interval (2 * n)).powersetCard m).filter fun Y =>
      ∃ A B : Finset ℕ,
        A ⊆ interval n ∧ B ⊆ interval n ∧
          A.card = k ∧ B.card = k ∧ A + B = Y

private lemma mem_moderateSumsetSumsetSlice {n k m : ℕ} {Y : Finset ℕ} :
    Y ∈ moderateSumsetSumsetSlice n k m ↔
      Y ⊆ interval (2 * n) ∧ Y.card = m ∧
        ∃ A B : Finset ℕ,
          A ⊆ interval n ∧ B ⊆ interval n ∧
            A.card = k ∧ B.card = k ∧ A + B = Y := by
  classical
  rw [moderateSumsetSumsetSlice, Finset.mem_filter, Finset.mem_powersetCard]
  simp only [and_assoc]

private lemma moderateSumsetSumsetSlice_card_le_pairSumsetsFamily (n k m : ℕ) :
    (moderateSumsetSumsetSlice n k m).card ≤ (pairSumsetsFamily n k m).ncard := by
  classical
  rw [← Set.ncard_coe_finset (moderateSumsetSumsetSlice n k m)]
  apply Set.ncard_le_ncard
  · intro Y hY
    change Y ∈ moderateSumsetSumsetSlice n k m at hY
    rw [mem_moderateSumsetSumsetSlice] at hY
    rcases hY.2.2 with ⟨A, B, hAint, hBint, hAcard, hBcard, hYeq⟩
    exact ⟨hY.1, A, B, hAint, hBint, hAcard, hBcard, hYeq, hY.2.1.le⟩
  · apply ((interval (2 * n)).powerset.finite_toSet).subset
    intro Y hY
    exact Finset.mem_powerset.mpr hY.1

private lemma medium_fixed_sumset_probability_le
    (n : ℕ) (δ : unitInterval) (Y : Finset ℕ) :
    let ℙ : MeasureTheory.Measure (Finset ℕ) := binomialFinsetSubset (Set.Icc 1 n) δ
    ℙ.real {S : Finset ℕ | Y ⊆ S} ≤ (δ : ℝ) ^ Y.card := by
  classical
  simpa [interval] using
    (binomialFinsetSubset_real_superset_nat
      (Ω := Set.Icc 1 n) (p := δ) (Set.finite_Icc 1 n) (T := Y))

private def moderateSumsetCardRange (k : ℕ) (C : ℝ) : Finset ℕ :=
  (Finset.Icc 0 (k * k)).filter fun m =>
    C * (k : ℝ) < (m : ℝ) ∧ m < k * (k + 1) / 2

private lemma moderateSumsetCardRange_card_le (k : ℕ) {C : ℝ} :
    (moderateSumsetCardRange k C).card ≤ k * k + 1 := by
  apply (Finset.card_filter_le _ _).trans
  simp [Nat.card_Icc]

private lemma mem_moderateSumsetCardRange {k m : ℕ} {C : ℝ} :
    m ∈ moderateSumsetCardRange k C ↔
      m ≤ k * k ∧ C * (k : ℝ) < (m : ℝ) ∧ m < k * (k + 1) / 2 := by
  rw [moderateSumsetCardRange, Finset.mem_filter, Finset.mem_Icc]
  simp

private lemma moderateSumsetEvent_measure_le_sum
    (n k : ℕ) (C : ℝ) {δ : unitInterval}
    (prob : ℕ → ℝ)
    (hprob_nonneg : ∀ m, 0 ≤ prob m)
    (hprob :
      ∀ m (Y : Finset ℕ), Y ∈ moderateSumsetSumsetSlice n k m →
        let ℙ : MeasureTheory.Measure (Finset ℕ) := binomialFinsetSubset (Set.Icc 1 n) δ
        ℙ.real {S : Finset ℕ | Y ⊆ S} ≤ prob m) :
    let ℙ : MeasureTheory.Measure (Finset ℕ) := binomialFinsetSubset (Set.Icc 1 n) δ
    ℙ.real {S : Finset ℕ | moderateSumsetEvent n k C S} ≤
      ∑ m ∈ moderateSumsetCardRange k C, ((pairSumsetsFamily n k m).ncard : ℝ) * prob m := by
  classical
  let ℙ : MeasureTheory.Measure (Finset ℕ) := binomialFinsetSubset (Set.Icc 1 n) δ
  let M : Finset ℕ := moderateSumsetCardRange k C
  let E : ℕ → Set (Finset ℕ) := fun m =>
    ⋃ Y ∈ moderateSumsetSumsetSlice n k m, {S : Finset ℕ | Y ⊆ S}
  change ℙ.real {S : Finset ℕ | moderateSumsetEvent n k C S} ≤
    ∑ m ∈ M, ((pairSumsetsFamily n k m).ncard : ℝ) * prob m
  apply le_trans (b := ℙ.real (⋃ m ∈ M, E m))
  · rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def]
    apply ENNReal.toReal_mono (MeasureTheory.measure_ne_top ℙ _)
    apply MeasureTheory.measure_mono
    intro S hS
    rcases hS with ⟨A, B, hAint, hBint, hAcard, hBcard, hcond_lower, hcond_upper, hsumS⟩
    let m := (A + B).card
    refine Set.mem_iUnion₂.mpr ⟨m, ?_, ?_⟩
    · rw [mem_moderateSumsetCardRange]
      refine ⟨?_, by simpa [m] using hcond_lower, by simpa [m] using hcond_upper⟩
      dsimp [m]
      apply Finset.card_add_le.trans
      rw [hAcard, hBcard]
    · refine Set.mem_iUnion₂.mpr ⟨A + B, ?_, hsumS⟩
      rw [mem_moderateSumsetSumsetSlice]
      refine ⟨?_, rfl, A, B, hAint, hBint, hAcard, hBcard, rfl⟩
      intro x hx
      rw [Finset.mem_add] at hx
      rcases hx with ⟨a, ha, b, hb, rfl⟩
      specialize hAint ha
      specialize hBint hb
      rw [interval, Finset.mem_Icc] at hAint hBint ⊢
      omega
  · refine (MeasureTheory.measureReal_biUnion_finset_le M E).trans ?_
    refine (Finset.sum_le_sum
      (s := M) (f := fun m => ℙ.real (E m))
      (g := fun m => (moderateSumsetSumsetSlice n k m).card * prob m) ?_).trans ?_
    · intro m hm
      apply (MeasureTheory.measureReal_biUnion_finset_le (moderateSumsetSumsetSlice n k m)
          fun Y => {S : Finset ℕ | Y ⊆ S}).trans
      refine (Finset.sum_le_sum
        (s := moderateSumsetSumsetSlice n k m) (f := fun Y => ℙ.real {S : Finset ℕ | Y ⊆ S})
        (g := fun _ => prob m) ?_).trans_eq ?_
      · intro Y hY
        simpa [ℙ] using hprob m Y hY
      · simp [mul_comm]
    · apply Finset.sum_le_sum
      intro m hm
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast moderateSumsetSumsetSlice_card_le_pairSumsetsFamily n k m
      · exact hprob_nonneg m

private lemma moderateSumsetCardRange_card_le_two_mul_sq {k : ℕ} {C : ℝ} (hk : 1 ≤ k) :
    ((moderateSumsetCardRange k C).card : ℝ) ≤ 2 * (k : ℝ) ^ 2 := by
  norm_cast
  nlinarith [moderateSumsetCardRange_card_le (k := k) (C := C)]

private lemma moderateSumsetEvent_measure_le_of_slice_bound
    (n k : ℕ) (C B : ℝ) {δ : unitInterval}
    (hk : 1 ≤ k)
    (hB_nonneg : 0 ≤ B)
    (hslice :
      ∀ m ∈ moderateSumsetCardRange k C,
        ((pairSumsetsFamily n k m).ncard : ℝ) * (δ : ℝ) ^ m ≤ B) :
    let ℙ : MeasureTheory.Measure (Finset ℕ) := binomialFinsetSubset (Set.Icc 1 n) δ
    ℙ.real {S : Finset ℕ | moderateSumsetEvent n k C S} ≤
      2 * (k : ℝ) ^ 2 * B := by
  classical
  let ℙ : MeasureTheory.Measure (Finset ℕ) := binomialFinsetSubset (Set.Icc 1 n) δ
  refine (moderateSumsetEvent_measure_le_sum n k C (fun m => (δ : ℝ) ^ m)
    (fun m => pow_nonneg δ.2.1 m) ?_).trans ?_
  · intro m Y hY
    rw [mem_moderateSumsetSumsetSlice] at hY
    simpa [ℙ, hY.2.1] using medium_fixed_sumset_probability_le n δ Y
  · refine (Finset.sum_le_sum
      (s := moderateSumsetCardRange k C)
      (f := fun m => ((pairSumsetsFamily n k m).ncard : ℝ) * (δ : ℝ) ^ m)
      (g := fun _ => B) ?_).trans ?_
    · intro m hm
      exact hslice m hm
    · rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (moderateSumsetCardRange_card_le_two_mul_sq (C := C) hk)
        hB_nonneg

private lemma moderateSumsetAuxExponent_pos : 0 < moderateSumsetAuxExponent := by
  norm_num [moderateSumsetAuxExponent]

private lemma log_six_exp_one_le_three :
    Real.log (6 * Real.exp 1) ≤ (3 : ℝ) := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  apply le_trans (b := (Real.exp 1) ^ (2 : ℕ) * Real.exp 1)
  · apply le_of_lt
    apply mul_lt_mul_of_pos_right
    · nlinarith [Real.exp_one_gt_d9]
    · exact Real.exp_pos 1
  · rw [← pow_succ, ← Real.exp_nat_mul]
    norm_num

private lemma medium_small_pack_exp_le {k : ℕ} {q c : ℝ}
    (hk : 1 ≤ k) (hq_pos : 0 < q)
    (hq_large : (2 : ℝ) ^ (12 : ℕ) ≤ q)
    (hc_nonneg : 0 ≤ c) (_hc_le : c ≤ moderateSumsetAuxExponent) :
    (6 * Real.exp 1 * q) ^ (6 * k) * Real.exp ((k : ℝ) ^ (1 - 2 * c)) ≤
      Real.exp ((12 * (k : ℝ)) * Real.log q) := by
  have hkR_one : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hbase_pos : 0 < 6 * Real.exp 1 * q := by positivity
  have hlog_base : Real.log (6 * Real.exp 1 * q) ≤ 3 + Real.log q := by
    rw [Real.log_mul (by positivity : 6 * Real.exp 1 ≠ 0) hq_pos.ne']
    nlinarith [log_six_exp_one_le_three]
  have hlogq_ge : (19 / 6 : ℝ) ≤ Real.log q := by
    refine le_trans (b := Real.log ((2 : ℝ) ^ (12 : ℕ))) ?_
      (Real.log_le_log (by norm_num) hq_large)
    rw [Real.log_pow]
    norm_num
    nlinarith [log_two_gt_half]
  have hkc : (k : ℝ) ^ (1 - 2 * c) ≤ (k : ℝ) := by
    apply le_trans (b := (k : ℝ) ^ (1 : ℝ))
    · apply Real.rpow_le_rpow_of_exponent_le hkR_one
      nlinarith
    · rw [Real.rpow_one]
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hbase_pos, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  norm_num [Nat.cast_mul]
  nlinarith [hkc, hlogq_ge,
    mul_le_mul_of_nonneg_right hlog_base (by positivity : 0 ≤ 6 * (k : ℝ))]

private lemma medium_small_exponential_part_le {γ C q : ℝ} {n k : ℕ}
    (hγ_pos : 0 < γ) (hn : 1 < n) (_hq_pos : 0 < q)
    (hCq : C ≤ q)
    (hbudget : (12 * (k : ℝ)) * Real.log q + Real.log (n : ℝ) ≤
      (γ * q / 2) * Real.log (n : ℝ)) :
    (n : ℝ) ^ (2 * q + 1) * Real.exp ((12 * (k : ℝ)) * Real.log q) *
        (n : ℝ) ^ (-(2 + γ) * q) ≤
      (n : ℝ) ^ (-(γ * C / 2)) := by
  let L := Real.log (n : ℝ)
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hL_pos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast hn)
  rw [Real.rpow_def_of_pos hn_pos, Real.rpow_def_of_pos hn_pos,
    Real.rpow_def_of_pos hn_pos, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  ring_nf at hbudget ⊢
  nlinarith [hbudget, mul_le_mul_of_nonneg_right
    (neg_le_neg (mul_le_mul_of_nonneg_left hCq hγ_pos.le)) hL_pos.le]

private lemma medium_large_exponential_part_le {γ C q c : ℝ} {n k : ℕ}
    (hγ_pos : 0 < γ) (hn : 1 < n) (hk : 1 ≤ k)
    (hkcq : (k : ℝ) ^ c ≤ q)
    (hkcC : C ≤ (k : ℝ) ^ c)
    (hlog_control :
      (24 * (k : ℝ)) * Real.log (k : ℝ) + Real.log (n : ℝ) ≤
        (γ / 2) * (k : ℝ) ^ c * Real.log (n : ℝ)) :
    (n : ℝ) ^ (2 * q + 1) * (k : ℝ) ^ (24 * k) *
        (n : ℝ) ^ (-(2 + γ) * q) ≤
      (n : ℝ) ^ (-(γ * C / 2)) := by
  let L := Real.log (n : ℝ)
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hk_pos : 0 < (k : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 1) hk
  have hL_pos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast hn)
  rw [Real.rpow_def_of_pos hn_pos, ← Real.rpow_natCast,
    Real.rpow_def_of_pos hk_pos, Real.rpow_def_of_pos hn_pos,
    Real.rpow_def_of_pos hn_pos, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  norm_num [Nat.cast_mul] at hlog_control ⊢
  ring_nf at hlog_control ⊢
  nlinarith [hlog_control,
    mul_le_mul_of_nonneg_right
      (neg_le_neg (mul_le_mul_of_nonneg_left hkcq hγ_pos.le)) hL_pos.le,
    mul_le_mul_of_nonneg_right
      (neg_le_neg (mul_le_mul_of_nonneg_left hkcC hγ_pos.le)) hL_pos.le]

def moderateSumsetGapConstant (γ c : ℝ) : ℝ :=
  Real.exp (96 * densityCoefficient (2 + γ) c / γ)

lemma one_le_moderateSumsetGapConstant {γ c : ℝ} (hγ_pos : 0 < γ)
    (hc_pos : 0 < c) (hc_lt : c < 1) :
    1 ≤ moderateSumsetGapConstant γ c := by
  have hq : 1 < densityCoefficient (2 + γ) c :=
    densityCoefficient_gt_one (by linarith) hc_pos hc_lt
  rw [moderateSumsetGapConstant, Real.one_le_exp_iff]
  positivity

private lemma moderateSumsetGapConstant_ge_two_pow_twelve {γ c : ℝ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 2) (hc_pos : 0 < c) (hc_lt : c < 1) :
    (2 : ℝ) ^ (12 : ℕ) ≤ moderateSumsetGapConstant γ c := by
  have hq_gt_one : 1 < densityCoefficient (2 + γ) c :=
    densityCoefficient_gt_one (by linarith) hc_pos hc_lt
  rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ (12 : ℕ)), moderateSumsetGapConstant]
  apply Real.exp_le_exp.mpr
  rw [Real.log_pow]
  have hlog2_lt_one : Real.log (2 : ℝ) < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have ha48 : (48 : ℝ) ≤ 96 * densityCoefficient (2 + γ) c / γ := by
    rw [le_div_iff₀ hγ_pos]
    nlinarith
  nlinarith

private lemma medium_log_ratio_bound_for_gap {γ c q : ℝ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 2) (hc_pos : 0 < c) (hc_lt : c < 1)
    (hqC : moderateSumsetGapConstant γ c ≤ q) :
    12 * densityCoefficient (2 + γ) c * Real.log q + 1 ≤ γ * q / 2 := by
  let Q := densityCoefficient (2 + γ) c
  let a := 96 * Q / γ
  let C := Real.exp a
  have hQ_gt_one : 1 < Q := by
    dsimp only [Q]
    exact densityCoefficient_gt_one (by linarith) hc_pos hc_lt
  have ha_pos : 0 < a := by dsimp [a]; positivity
  have hC : C = moderateSumsetGapConstant γ c := by rfl
  have hCq : C ≤ q := hC.le.trans hqC
  change 12 * Q * Real.log q + 1 ≤ γ * q / 2
  apply le_trans (b := γ * q / 4 + γ * q / 4)
  · apply add_le_add
    · have hq_pos : 0 < q := (Real.exp_pos a).trans_le hCq
      have hC_exp : Real.exp 1 ≤ C := by
        apply Real.exp_le_exp.mpr
        dsimp [a]
        rw [le_div_iff₀ hγ_pos]
        nlinarith
      have hratio : Real.log q / q ≤ Real.log C / C := by
        apply Real.log_div_self_antitoneOn
        · exact hC_exp
        · exact hC_exp.trans hCq
        · exact hCq
      rw [div_le_iff₀ hq_pos] at hratio
      have hratio_C : Real.log C / C ≤ γ / (48 * Q) := by
        rw [Real.log_exp]
        apply (div_le_iff₀ (Real.exp_pos a)).2
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ (by positivity : 0 < 48 * Q)).2
        have hexp_quad : a ^ 2 / 2 ≤ C := by
          dsimp [C]
          nlinarith [Real.quadratic_le_exp_of_nonneg ha_pos.le]
        have h := mul_le_mul_of_nonneg_left hexp_quad hγ_pos.le
        dsimp [a] at h ⊢
        field_simp [hγ_pos.ne'] at h ⊢
        nlinarith
      apply (mul_le_mul_of_nonneg_left
        (hratio.trans (mul_le_mul_of_nonneg_right hratio_C hq_pos.le))
        (by positivity)).trans_eq
      field_simp [ne_of_gt hQ_gt_one]
      ring
    · rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
      have hfour : (4 : ℝ) / γ ≤ C := by
        apply (div_le_iff₀ hγ_pos).2
        apply (by nlinarith [hQ_gt_one] : (4 : ℝ) ≤ 96 * Q).trans
        have ha_le_C : a ≤ C := by
          dsimp [C]
          nlinarith [Real.add_one_le_exp a]
        have h := mul_le_mul_of_nonneg_right ha_le_C hγ_pos.le
        dsimp [a] at h
        field_simp [hγ_pos.ne'] at h
        simpa [mul_comm] using h
      have h := mul_le_mul_of_nonneg_left (hfour.trans hCq) hγ_pos.le
      field_simp [hγ_pos.ne'] at h
      simpa [mul_comm] using h
  · ring_nf
    exact le_rfl

private lemma medium_small_slice_bound {γ gap : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 2)
    (hgap_pos : 0 < gap) (hgap_lt : gap < 1)
    {n k m : ℕ} {δ : unitInterval}
    (hn : 1 < n) (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1)
    (hk : 1 ≤ k)
    (hkdef : k = pairCardThreshold (2 + γ) n δ)
    (hk_le_log : (k : ℝ) ≤ densityCoefficient (2 + γ) gap * Real.log (n : ℝ))
    (hk_large : smallSumsetClassCountThreshold ≤ k)
    (hm : m ∈ moderateSumsetCardRange k (moderateSumsetGapConstant γ gap))
    (hm_small : (m : ℝ) ≤ (k : ℝ) ^ (1 + moderateSumsetAuxExponent)) :
    ((pairSumsetsFamily n k m).ncard : ℝ) * (δ : ℝ) ^ m ≤
      (n : ℝ) ^ (-(γ * moderateSumsetGapConstant γ gap / 2)) := by
  let C := moderateSumsetGapConstant γ gap
  let c := moderateSumsetAuxExponent
  let q := (m : ℝ) / (k : ℝ)
  have hk_pos_nat : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hkR_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos_nat
  have hτ_nonneg : 0 ≤ 2 + γ := by linarith
  have hm_mem : m ≤ k * k ∧ C * (k : ℝ) < (m : ℝ) ∧
      m < k * (k + 1) / 2 := by
    simpa [C] using mem_moderateSumsetCardRange.mp hm
  have hcount :
      ((pairSumsetsFamily n k m).ncard : ℝ) ≤
        (n : ℝ) ^ (2 * (m : ℝ) / (k : ℝ) + 1) *
          ((6 * Real.exp 1 * (m : ℝ)) / (k : ℝ)) ^ (6 * k) *
            Real.exp ((k : ℝ) ^ (1 - 2 * c)) := by
    apply pairSumsetsFamily_ncard_le_of_small_sumset n k m c
    · exact hm_mem.2.2
    · rfl
    · exact hk_large
    · simpa [c] using hm_small
  have hδpow :
      (δ : ℝ) ^ m ≤ (n : ℝ) ^ (-(2 + γ) * (m : ℝ) / (k : ℝ)) := by
    simpa [hkdef] using
      unitInterval_pow_le_exp_div_mul_log n m (2 + γ) δ hτ_nonneg hδ_pos hδ_lt hn
        (by simpa [hkdef] using hk_pos_nat)
  have hCq : C ≤ q := by
    apply le_of_lt
    rw [lt_div_iff₀ hkR_pos]
    simpa [C, q, mul_comm] using hm_mem.2.1
  have hq_pos : 0 < q := by
    exact (Real.exp_pos _).trans_le (by simpa [C, moderateSumsetGapConstant] using hCq)
  have hq_large : (2 : ℝ) ^ (12 : ℕ) ≤ q :=
    (moderateSumsetGapConstant_ge_two_pow_twelve hγ_pos hγ_le hgap_pos hgap_lt).trans
      (by simpa [C] using hCq)
  have hlogq_nonneg : 0 ≤ Real.log q := Real.log_nonneg (by nlinarith [hq_large])
  have hlog_ratio : 12 * densityCoefficient (2 + γ) gap * Real.log q + 1 ≤
      γ * q / 2 :=
    medium_log_ratio_bound_for_gap hγ_pos hγ_le hgap_pos hgap_lt (by simpa [C] using hCq)
  have hpack_exp :
      ((6 * Real.exp 1 * (m : ℝ)) / (k : ℝ)) ^ (6 * k) *
          Real.exp ((k : ℝ) ^ (1 - 2 * c)) ≤
        Real.exp ((12 * (k : ℝ)) * Real.log q) := by
    convert medium_small_pack_exp_le (k := k) (q := q) (c := c) hk hq_pos hq_large
      (le_of_lt moderateSumsetAuxExponent_pos) (by simp [c]) using 1
    dsimp [q]
    field_simp [hkR_pos.ne']
  have hbudget : (12 * (k : ℝ)) * Real.log q + Real.log (n : ℝ) ≤
      (γ * q / 2) * Real.log (n : ℝ) := by
    have hpack := mul_le_mul_of_nonneg_right hk_le_log hlogq_nonneg
    have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    nlinarith [mul_le_mul_of_nonneg_left hpack (by norm_num : (0 : ℝ) ≤ 12),
      mul_le_mul_of_nonneg_right hlog_ratio hL_pos.le]
  have hexp_part :
      (n : ℝ) ^ (2 * q + 1) * Real.exp ((12 * (k : ℝ)) * Real.log q) *
          (n : ℝ) ^ (-(2 + γ) * q) ≤
        (n : ℝ) ^ (-(γ * C / 2)) :=
    medium_small_exponential_part_le hγ_pos hn hq_pos hCq hbudget
  apply (mul_le_mul hcount hδpow (pow_nonneg hδ_pos.le m) (by positivity)).trans
  refine le_trans (b :=
    (n : ℝ) ^ (2 * q + 1) * Real.exp ((12 * (k : ℝ)) * Real.log q) *
      (n : ℝ) ^ (-(2 + γ) * q)) ?_ hexp_part
  convert mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpack_exp
      (by positivity : 0 ≤ (n : ℝ) ^ (2 * q + 1)))
    (by positivity : 0 ≤ (n : ℝ) ^ (-(2 + γ) * q)) using 1
  all_goals
    dsimp [q]
    ring_nf

private lemma medium_large_slice_bound {γ gap : ℝ} (hγ_pos : 0 < γ)
    {n k m : ℕ} {δ : unitInterval}
    (hn : 1 < n) (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1)
    (hk : 1 ≤ k)
    (hkdef : k = pairCardThreshold (2 + γ) n δ)
    (hm : m ∈ moderateSumsetCardRange k (moderateSumsetGapConstant γ gap))
    (hm_not_small : ¬ (m : ℝ) ≤ (k : ℝ) ^ (1 + moderateSumsetAuxExponent))
    (hkcC : moderateSumsetGapConstant γ gap ≤ (k : ℝ) ^ moderateSumsetAuxExponent)
    (hlog_control :
      (24 * (k : ℝ)) * Real.log (k : ℝ) + Real.log (n : ℝ) ≤
        (γ / 2) * (k : ℝ) ^ moderateSumsetAuxExponent * Real.log (n : ℝ)) :
    ((pairSumsetsFamily n k m).ncard : ℝ) * (δ : ℝ) ^ m ≤
      (n : ℝ) ^ (-(γ * moderateSumsetGapConstant γ gap / 2)) := by
  let C := moderateSumsetGapConstant γ gap
  let c := moderateSumsetAuxExponent
  let q := (m : ℝ) / (k : ℝ)
  have hk_pos_nat : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hkR_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos_nat
  have hτ_nonneg : 0 ≤ 2 + γ := by linarith
  have hm_mem : m ≤ k * k ∧ C * (k : ℝ) < (m : ℝ) ∧
      m < k * (k + 1) / 2 := by
    simpa [C] using mem_moderateSumsetCardRange.mp hm
  have hcount :
      ((pairSumsetsFamily n k m).ncard : ℝ) ≤
        (n : ℝ) ^ (2 * (m : ℝ) / (k : ℝ) + 1) * (k : ℝ) ^ (24 * k) :=
    pairSumsetsFamily_ncard_le n k m hm_mem.2.2
  have hδpow :
      (δ : ℝ) ^ m ≤ (n : ℝ) ^ (-(2 + γ) * (m : ℝ) / (k : ℝ)) := by
    simpa [hkdef] using
      unitInterval_pow_le_exp_div_mul_log n m (2 + γ) δ hτ_nonneg hδ_pos hδ_lt hn
        (by simpa [hkdef] using hk_pos_nat)
  have hkcq : (k : ℝ) ^ c ≤ q := by
    apply le_of_lt
    rw [lt_div_iff₀ hkR_pos]
    convert lt_of_not_ge (by simpa [c] using hm_not_small) using 1
    rw [Real.rpow_add hkR_pos, Real.rpow_one]
    ring
  have hexp_part :
      (n : ℝ) ^ (2 * q + 1) * (k : ℝ) ^ (24 * k) *
          (n : ℝ) ^ (-(2 + γ) * q) ≤
        (n : ℝ) ^ (-(γ * C / 2)) :=
    medium_large_exponential_part_le hγ_pos hn hk hkcq (by simpa [C, c] using hkcC)
      (by simpa [c] using hlog_control)
  apply (mul_le_mul hcount hδpow (pow_nonneg hδ_pos.le m) (by positivity)).trans
  convert hexp_part using 1
  all_goals
    first
    | rfl
    | dsimp [q]
      ring_nf

private def moderateSumsetCardScale (γ c : ℝ) : ℝ :=
  max (smallSumsetClassCountThreshold : ℝ)
    (max
      ((max (2 * moderateSumsetGapConstant γ c) ((4 : ℝ) / γ)) ^ ((2 : ℝ) ^ (8 : ℕ)))
      (((49152 * densityCoefficient (2 + γ) c) / γ) ^ ((2 : ℝ) ^ (9 : ℕ))))

def moderateSumsetDensityExponent (γ c : ℝ) : ℝ :=
  (2 + γ) / (2 * moderateSumsetCardScale γ c)

private lemma moderateSumsetCardScale_pos (γ c : ℝ) :
    0 < moderateSumsetCardScale γ c := by
  dsimp [moderateSumsetCardScale]
  exact lt_of_lt_of_le (by exact_mod_cast smallSumsetClassCountThreshold_pos)
    (le_max_left _ _)

lemma moderateSumsetDensityExponent_pos {γ c : ℝ} (hγ_pos : 0 < γ) :
    0 < moderateSumsetDensityExponent γ c := by
  have hscale := moderateSumsetCardScale_pos γ c
  rw [moderateSumsetDensityExponent]
  positivity

private lemma moderateSumsetCardScale_bounds {γ c : ℝ} (hγ_pos : 0 < γ)
    (hc_pos : 0 < c) (hc_lt : c < 1) {k : ℕ}
    (hscale : moderateSumsetCardScale γ c ≤ (k : ℝ)) :
    smallSumsetClassCountThreshold ≤ k ∧
      2 * moderateSumsetGapConstant γ c ≤ (k : ℝ) ^ moderateSumsetAuxExponent ∧
        (4 : ℝ) / γ ≤ (k : ℝ) ^ moderateSumsetAuxExponent ∧
          (49152 * densityCoefficient (2 + γ) c) / γ ≤
            (k : ℝ) ^ (moderateSumsetAuxExponent / 2) := by
  let A := max (2 * moderateSumsetGapConstant γ c) ((4 : ℝ) / γ)
  let B := (49152 * densityCoefficient (2 + γ) c) / γ
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact (mul_nonneg (by norm_num) (Real.exp_pos _).le).trans (le_max_left _ _)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    have hq_pos : 0 < densityCoefficient (2 + γ) c := by
      dsimp [densityCoefficient]
      have : 0 < Real.log (1 / (1 - c)) := by
        apply Real.log_pos
        rw [one_lt_div] <;> linarith
      positivity
    positivity
  have hA_le_kc : A ≤ (k : ℝ) ^ moderateSumsetAuxExponent := by
    apply le_trans
      (b := (A ^ ((2 : ℝ) ^ (8 : ℕ))) ^ moderateSumsetAuxExponent)
    · rw [← Real.rpow_mul hA_nonneg]
      norm_num [moderateSumsetAuxExponent]
    · apply Real.rpow_le_rpow (Real.rpow_nonneg hA_nonneg _)
      · refine (le_max_left (A ^ ((2 : ℝ) ^ (8 : ℕ)))
          (B ^ ((2 : ℝ) ^ (9 : ℕ)))).trans ?_
        apply (le_max_right (smallSumsetClassCountThreshold : ℝ)
          (max (A ^ ((2 : ℝ) ^ (8 : ℕ))) (B ^ ((2 : ℝ) ^ (9 : ℕ))))).trans
        simpa [moderateSumsetCardScale, A, B] using hscale
      · exact moderateSumsetAuxExponent_pos.le
  refine ⟨?_, (le_max_left _ _).trans hA_le_kc,
    (le_max_right _ _).trans hA_le_kc, ?_⟩
  · exact_mod_cast (le_max_left (smallSumsetClassCountThreshold : ℝ) _).trans hscale
  · change B ≤ (k : ℝ) ^ (moderateSumsetAuxExponent / 2)
    apply le_trans
      (b := (B ^ ((2 : ℝ) ^ (9 : ℕ))) ^ (moderateSumsetAuxExponent / 2))
    · rw [← Real.rpow_mul hB_nonneg]
      norm_num [moderateSumsetAuxExponent]
    · apply Real.rpow_le_rpow (Real.rpow_nonneg hB_nonneg _)
      · refine (le_max_right (A ^ ((2 : ℝ) ^ (8 : ℕ)))
          (B ^ ((2 : ℝ) ^ (9 : ℕ)))).trans ?_
        apply (le_max_right (smallSumsetClassCountThreshold : ℝ)
          (max (A ^ ((2 : ℝ) ^ (8 : ℕ))) (B ^ ((2 : ℝ) ^ (9 : ℕ))))).trans
        simpa [moderateSumsetCardScale, A, B] using hscale
      · nlinarith [moderateSumsetAuxExponent_pos]

private lemma pairCardThreshold_ge_scale_of_density_lower {τ R α : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hτ_pos : 0 < τ) (hR_pos : 0 < R)
    (hα : α = τ / (2 * R))
    (hn : 1 < n)
    (hδ_lt : (δ : ℝ) < 1)
    (hδ_lower : (n : ℝ) ^ (-α) < (δ : ℝ)) :
    R ≤ (pairCardThreshold τ n δ : ℝ) := by
  let L := Real.log (n : ℝ)
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hL_pos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast hn)
  have hα_pos : 0 < α := by rw [hα]; positivity
  have hδ_pow_pos : 0 < (n : ℝ) ^ (-α) := Real.rpow_pos_of_pos hn_pos _
  have hδ_pos : 0 < (δ : ℝ) := hδ_pow_pos.trans hδ_lower
  have hlog_inv_pos : 0 < Real.log (1 / δ) := by
    apply Real.log_pos
    rw [one_lt_div hδ_pos]
    exact hδ_lt
  have hinv_lt : 1 / (δ : ℝ) < (n : ℝ) ^ α := by
    have h := one_div_lt_one_div_of_lt hδ_pow_pos hδ_lower
    rw [Real.rpow_neg hn_pos.le] at h
    simpa [one_div] using h
  have hlog_inv_lt : Real.log (1 / δ) < α * L := by
    have hlog := Real.log_lt_log (by positivity : 0 < 1 / (δ : ℝ)) hinv_lt
    rw [Real.log_rpow hn_pos] at hlog
    simpa [L] using hlog
  have hdiv_lt : τ * L / (α * L) < τ * L / Real.log (1 / δ) :=
    div_lt_div_of_pos_left (mul_pos hτ_pos hL_pos) hlog_inv_pos hlog_inv_lt
  rw [hα] at hdiv_lt
  field_simp [hτ_pos.ne', hR_pos.ne', hL_pos.ne'] at hdiv_lt
  apply le_trans (b := τ * L / Real.log (1 / δ))
  · apply le_of_lt
    rw [lt_div_iff₀ hlog_inv_pos]
    nlinarith [hdiv_lt]
  · simpa [pairCardThreshold, L] using
      Nat.le_ceil (τ * Real.log (n : ℝ) / Real.log (1 / δ))

private lemma medium_log_control_of_scale {γ gap : ℝ} (hγ_pos : 0 < γ)
    (hgap_pos : 0 < gap) (hgap_lt : gap < 1)
    {n k : ℕ} (hn : 1 < n) (hk : 1 ≤ k)
    (hk_le_log : (k : ℝ) ≤ densityCoefficient (2 + γ) gap * Real.log (n : ℝ))
    (hfour : (4 : ℝ) / γ ≤ (k : ℝ) ^ moderateSumsetAuxExponent)
    (hB : (49152 * densityCoefficient (2 + γ) gap) / γ ≤
      (k : ℝ) ^ (moderateSumsetAuxExponent / 2)) :
    (24 * (k : ℝ)) * Real.log (k : ℝ) + Real.log (n : ℝ) ≤
      (γ / 2) * (k : ℝ) ^ moderateSumsetAuxExponent * Real.log (n : ℝ) := by
  let c := moderateSumsetAuxExponent
  let a := (k : ℝ) ^ (c / 2)
  let kc := (k : ℝ) ^ c
  let L := Real.log (n : ℝ)
  let q := densityCoefficient (2 + γ) gap
  have hkR_pos : 0 < (k : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 1) hk
  have hL_pos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast hn)
  have hc_half_pos : 0 < c / 2 := by
    dsimp [c]
    nlinarith [moderateSumsetAuxExponent_pos]
  have ha_nonneg : 0 ≤ a := by dsimp [a]; positivity
  have hlog_le : Real.log (k : ℝ) ≤ 512 * a := by
    apply (Real.log_le_rpow_div hkR_pos.le hc_half_pos).trans_eq
    dsimp [a, c]
    norm_num [moderateSumsetAuxExponent]
    field_simp
  rw [div_le_iff₀ hγ_pos] at hB hfour
  have hq_pos : 0 < q := by
    dsimp [q, densityCoefficient]
    have : 0 < Real.log (1 / (1 - gap)) := by
      apply Real.log_pos
      rw [one_lt_div] <;> linarith
    positivity
  have hBmul : 49152 * q ≤ γ * a := by
    simpa [a, c, q, mul_comm] using hB
  have hlog_gamma : (96 * q) * Real.log (k : ℝ) ≤ γ * kc := by
    apply (mul_le_mul_of_nonneg_left hlog_le
      (mul_nonneg (by norm_num) hq_pos.le)).trans
    apply le_trans (b := (49152 * q) * a)
    · ring_nf
      exact le_rfl
    · refine (mul_le_mul_of_nonneg_right hBmul ha_nonneg).trans_eq ?_
      dsimp [a, kc, c]
      rw [mul_assoc]
      rw [← Real.rpow_add hkR_pos]
      congr 1
      ring_nf
  have hdiv : (k : ℝ) / (4 * q) ≤ L / 4 := by
    rw [div_le_iff₀ (by positivity : 0 < 4 * q)]
    exact hk_le_log.trans_eq (by ring)
  have hfirst :
      (24 * (k : ℝ)) * Real.log (k : ℝ) ≤ (γ / 4) * kc * L := by
    nlinarith [mul_le_mul_of_nonneg_right hlog_gamma
        (by positivity : 0 ≤ (k : ℝ) / (4 * q)),
      mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ γ * kc)]
  have hsecond : L ≤ (γ / 4) * kc * L := by
    nth_rewrite 1 [← one_mul L]
    apply mul_le_mul_of_nonneg_right
    · dsimp [kc, c]
      nlinarith [hfour]
    · exact hL_pos.le
  dsimp [L, kc, c] at hfirst hsecond ⊢
  nlinarith [hfirst, hsecond]

lemma pairCardThreshold_ge_two_of_density_lower {τ α : ℝ} {n : ℕ}
    {δ : unitInterval} (hτ_pos : 0 < τ) (hα_le : α ≤ τ / 4)
    (hn : 1 < n) (hδ_lt : (δ : ℝ) < 1)
    (hδ_lower : Real.rpow (n : ℝ) (-α) < (δ : ℝ)) :
    2 ≤ pairCardThreshold τ n δ := by
  apply (Nat.cast_le (α := ℝ)).mp
  refine pairCardThreshold_ge_scale_of_density_lower
    (τ := τ) (R := (2 : ℝ)) (α := τ / 4) hτ_pos ?_ ?_ hn hδ_lt ?_
  · norm_num
  · ring
  · refine lt_of_le_of_lt ?_ hδ_lower
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast le_of_lt hn
    · exact neg_le_neg hα_le

/-- Probability estimate for the moderate-sumset range. -/
theorem moderate_sumset_probability_le
    {γ c : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 2) (hc_pos : 0 < c)
    {n : ℕ} (hn_two : 2 ≤ n)
    {δ : unitInterval}
    (hδ_lower : (n : ℝ) ^ (-moderateSumsetDensityExponent γ c) < (δ : ℝ))
    (hδ_upper : (δ : ℝ) ≤ 1 - c) :
    let k := pairCardThreshold (2 + γ) n δ
    let C := moderateSumsetGapConstant γ c
    let ℙ : MeasureTheory.Measure (Finset ℕ) := binomialFinsetSubset (Set.Icc 1 n) δ
    ℙ.real {S : Finset ℕ | moderateSumsetEvent n k C S} ≤
      2 * (k : ℝ) ^ 2 / (n : ℝ) ^ (γ * C / 2) := by
  let R := moderateSumsetCardScale γ c
  let α := moderateSumsetDensityExponent γ c
  let k := pairCardThreshold (2 + γ) n δ
  let C := moderateSumsetGapConstant γ c
  have hR_pos : 0 < R := by simpa [R] using moderateSumsetCardScale_pos γ c
  have hn : 1 < n := lt_of_lt_of_le (by norm_num) hn_two
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hδ_pos : 0 < (δ : ℝ) :=
    (Real.rpow_pos_of_pos hn_pos (-α)).trans (by simpa [α] using hδ_lower)
  have hc_lt : c < 1 := by linarith
  have hδ_lt : (δ : ℝ) < 1 := by linarith
  have hscale : R ≤ (k : ℝ) := by
    simpa [k, α, R] using
      pairCardThreshold_ge_scale_of_density_lower (τ := 2 + γ) (R := R) (α := α)
        (by linarith) hR_pos rfl hn hδ_lt (by simpa [α] using hδ_lower)
  have hk : 1 ≤ k := by
    apply Nat.succ_le_of_lt
    exact_mod_cast hR_pos.trans_le hscale
  rcases moderateSumsetCardScale_bounds hγ_pos hc_pos hc_lt hscale with ⟨hk_large, htwoC, hfour, hB⟩
  have hk_le_log : (k : ℝ) ≤ densityCoefficient (2 + γ) c * Real.log (n : ℝ) :=
    pairCardThreshold_le_densityCoefficient_mul_log (τ := 2 + γ) (by linarith) hc_pos hn_two
      hδ_pos hδ_upper
  have hlog_control :
      (24 * (k : ℝ)) * Real.log (k : ℝ) + Real.log (n : ℝ) ≤
        (γ / 2) * (k : ℝ) ^ moderateSumsetAuxExponent * Real.log (n : ℝ) :=
    medium_log_control_of_scale hγ_pos hc_pos hc_lt hn hk hk_le_log hfour hB
  have hkcC : C ≤ (k : ℝ) ^ moderateSumsetAuxExponent := by
    exact (by
      have hC_pos : 0 < C := by dsimp [C, moderateSumsetGapConstant]; positivity
      nlinarith [htwoC])
  refine (moderateSumsetEvent_measure_le_of_slice_bound n k C
    ((n : ℝ) ^ (-(γ * C / 2))) hk ?_ ?_).trans_eq ?_
  · positivity
  · intro m hm
    by_cases hm_small : (m : ℝ) ≤ (k : ℝ) ^ (1 + moderateSumsetAuxExponent)
    · simpa [C, k] using
        medium_small_slice_bound hγ_pos hγ_le hc_pos hc_lt hn hδ_pos hδ_lt hk rfl hk_le_log
          hk_large (by simpa [C] using hm) hm_small
    · simpa [C, k] using
        medium_large_slice_bound hγ_pos hn hδ_pos hδ_lt hk rfl
          (by simpa [C] using hm) hm_small hkcC hlog_control
  · dsimp [k, C]
    rw [Real.rpow_neg hn_pos.le]
    ring


end

end DenseSetsWithoutLargeSumsets
