/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Stirling
import Verification.AdditiveCombinatorics.FreimanIsomorphismClasses
import Verification.Common

/-!
# Isomorphism classes with small self-sumsets

This file formalizes Section 4 of Green's paper. It contains the numerical sampling requirements,
the small-core proposition, the extension and restricted-sumset lemmas, and the final count of
Freiman-isomorphism classes with small restricted sumsets.
-/

namespace Verification

open scoped Pointwise

noncomputable section

/-- An explicit threshold above which the small-sumset class estimates apply. -/
irreducible_def smallSumsetClassCountThreshold : ℕ :=
  2 ^ (9000 : ℕ)

lemma two_pow_200_le_smallSumsetClassCountThreshold :
    2 ^ (200 : ℕ) ≤ smallSumsetClassCountThreshold := by
  rw [smallSumsetClassCountThreshold_def]
  exact pow_le_pow_right' (by norm_num) (by norm_num)

lemma smallSumsetClassCountThreshold_pos :
    0 < smallSumsetClassCountThreshold := by
  rw [smallSumsetClassCountThreshold_def]
  positivity

def coreSamplingRate (t : ℕ) : ℝ :=
  (t : ℝ) ^ (-(1 : ℝ) / 15)

def popularSumThreshold (t : ℕ) : ℕ :=
  ⌊(t : ℝ) ^ ((1 : ℝ) / 5)⌋₊

def exceptionPenalty (t : ℕ) : ℝ :=
  (t : ℝ) ^ ((11 : ℝ) / 15)

def coreDecompositionBudget (t m : ℕ) : ℝ :=
  coreSamplingRate t * t + exceptionPenalty t *
    (1 + (popularSumThreshold t : ℝ) * m / t +
      t * (1 - coreSamplingRate t ^ 2) ^ (popularSumThreshold t / 2))

lemma exceptionPenalty_mul_rpow_one_fifth {t : ℕ} (ht : 0 < t) :
    exceptionPenalty t * (t : ℝ) ^ ((1 : ℝ) / 5) =
      coreSamplingRate t * t := by
  unfold coreSamplingRate exceptionPenalty
  have htReal : (0 : ℝ) < t := by exact_mod_cast ht
  rw [← Real.rpow_add htReal]
  conv_rhs =>
    rhs
    rw [← Real.rpow_one (t : ℝ)]
  rw [← Real.rpow_add htReal]
  congr 1
  norm_num

lemma exceptionPenalty_mul_rpow_neg_four_fifths {t : ℕ} (ht : 0 < t) :
    exceptionPenalty t * (t : ℝ) ^ (-(4 : ℝ) / 5) =
      coreSamplingRate t := by
  unfold coreSamplingRate exceptionPenalty
  rw [← Real.rpow_add (by exact_mod_cast ht)]
  congr 1
  norm_num

lemma one_lt_of_smallSumsetClassCountThreshold_le {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) : 1 < t := by
  rw [smallSumsetClassCountThreshold_def] at ht
  exact lt_of_lt_of_le (by norm_num : 1 < 2 ^ (9000 : ℕ)) ht

lemma coreSamplingRate_pos {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) : 0 < coreSamplingRate t := by
  unfold coreSamplingRate
  apply Real.rpow_pos_of_pos
  exact_mod_cast Nat.zero_lt_of_lt (one_lt_of_smallSumsetClassCountThreshold_le ht)

lemma coreSamplingRate_lt_one {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) : coreSamplingRate t < 1 := by
  unfold coreSamplingRate
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast one_lt_of_smallSumsetClassCountThreshold_le ht
  · norm_num

lemma exceptionPenalty_nonneg (t : ℕ) :
    0 ≤ exceptionPenalty t := by
  unfold exceptionPenalty
  positivity

lemma one_hundred_eighty_le_rpow_one_thirtieth {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) :
    (180 : ℝ) ≤ (t : ℝ) ^ ((1 : ℝ) / 30) := by
  have htReal : ((2 ^ (9000 : ℕ) : ℕ) : ℝ) ≤ t := by
    exact_mod_cast (smallSumsetClassCountThreshold_def ▸ ht)
  have h180pow : (180 : ℝ) ≤ (2 : ℝ) ^ (300 : ℕ) := by
    refine ((by norm_num : (180 : ℝ) ≤ 2 ^ (8 : ℕ))).trans ?_
    exact pow_le_pow_right₀ (by norm_num) (by norm_num)
  refine h180pow.trans ?_
  rw [← Real.rpow_natCast]
  norm_num only [Nat.cast_ofNat]
  have hexponent : (300 : ℝ) = 9000 * ((1 : ℝ) / 30) := by norm_num
  rw [hexponent]
  rw [Real.rpow_mul (by positivity)]
  rw [Nat.cast_pow, Nat.cast_ofNat] at htReal
  rw [← Real.rpow_natCast] at htReal
  apply Real.rpow_le_rpow
  · positivity
  · exact htReal
  · norm_num

lemma popularSumThreshold_lower {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) :
    (t : ℝ) ^ ((1 : ℝ) / 5) / 2 ≤ popularSumThreshold t := by
  have hroot : (2 : ℝ) ≤ (t : ℝ) ^ ((1 : ℝ) / 5) := by
    have hpow := Real.rpow_le_rpow (by positivity)
      (one_hundred_eighty_le_rpow_one_thirtieth ht) (by norm_num : (0 : ℝ) ≤ 6)
    have hright : ((t : ℝ) ^ ((1 : ℝ) / 30)) ^ (6 : ℝ) =
        (t : ℝ) ^ ((1 : ℝ) / 5) := by
      rw [← Real.rpow_mul (by positivity)]
      congr 1
      norm_num
    rw [hright] at hpow
    refine ((by norm_num : (2 : ℝ) ≤ 180)).trans ?_
    have h180rpow : (180 : ℝ) ≤ (180 : ℝ) ^ (6 : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 180)
          (by norm_num : (1 : ℝ) ≤ 6)
    exact h180rpow.trans hpow
  have hfloor := Nat.lt_floor_add_one ((t : ℝ) ^ ((1 : ℝ) / 5))
  norm_num only [Nat.cast_add, Nat.cast_one] at hfloor
  change (t : ℝ) ^ ((1 : ℝ) / 5) / 2 ≤
    (popularSumThreshold t : ℝ)
  unfold popularSumThreshold
  linarith

lemma popularSumThreshold_half_lower {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) :
    (t : ℝ) ^ ((1 : ℝ) / 5) / 6 ≤
      (popularSumThreshold t / 2 : ℕ) := by
  have hroot : (4 : ℝ) ≤ (t : ℝ) ^ ((1 : ℝ) / 5) := by
    have hpow := Real.rpow_le_rpow (by positivity)
      (one_hundred_eighty_le_rpow_one_thirtieth ht)
      (by norm_num : (0 : ℝ) ≤ 6)
    have hright : ((t : ℝ) ^ ((1 : ℝ) / 30)) ^ (6 : ℝ) =
        (t : ℝ) ^ ((1 : ℝ) / 5) := by
      rw [← Real.rpow_mul (by positivity)]
      congr 1
      norm_num
    rw [hright] at hpow
    refine ((by norm_num : (4 : ℝ) ≤ 180)).trans ?_
    have h180rpow : (180 : ℝ) ≤ (180 : ℝ) ^ (6 : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 180)
          (by norm_num : (1 : ℝ) ≤ 6)
    exact h180rpow.trans hpow
  have hQ : (2 : ℕ) ≤ popularSumThreshold t := by
    exact_mod_cast
      ((by linarith : (2 : ℝ) ≤ (t : ℝ) ^ ((1 : ℝ) / 5) / 2).trans
        (popularSumThreshold_lower ht))
  have hdiv : popularSumThreshold t ≤
      3 * (popularSumThreshold t / 2) := by
    omega
  nlinarith [popularSumThreshold_lower ht,
    (by exact_mod_cast hdiv : (popularSumThreshold t : ℝ) ≤
      3 * (popularSumThreshold t / 2 : ℕ))]

lemma rpow_one_fifteenth_le_six_mul_log_bound {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) :
    (4 : ℝ) / 5 * Real.log t ≤ (t : ℝ) ^ ((1 : ℝ) / 15) / 6 := by
  let z := (t : ℝ) ^ ((1 : ℝ) / 30)
  have htPos : (0 : ℝ) < t := by
    exact_mod_cast Nat.zero_lt_of_lt (one_lt_of_smallSumsetClassCountThreshold_le ht)
  have hzPos : 0 < z := Real.rpow_pos_of_pos htPos _
  have hz : (180 : ℝ) ≤ z := one_hundred_eighty_le_rpow_one_thirtieth ht
  have hzSquare : 180 * z ≤ z ^ (2 : ℕ) := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right hz hzPos.le
  have hlog := Real.log_le_sub_one_of_pos hzPos
  have hlogIdentity : Real.log t = 30 * Real.log z := by
    rw [Real.log_rpow htPos]
    ring
  have hpowerIdentity : z ^ (2 : ℕ) = (t : ℝ) ^ ((1 : ℝ) / 15) := by
    unfold z
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    norm_num
  rw [hlogIdentity, ← hpowerIdentity]
  nlinarith

lemma coreSamplingRate_sq_mul_rpow_one_fifth {t : ℕ} (ht : 0 < t) :
    coreSamplingRate t ^ (2 : ℕ) * (t : ℝ) ^ ((1 : ℝ) / 5) =
      (t : ℝ) ^ ((1 : ℝ) / 15) := by
  unfold coreSamplingRate
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    ← Real.rpow_add (by exact_mod_cast ht)]
  congr 1
  norm_num

lemma samplingFailureProbability_le {t : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) :
    (1 - coreSamplingRate t ^ 2) ^ (popularSumThreshold t / 2) ≤
      (t : ℝ) ^ (-(4 : ℝ) / 5) := by
  let q := coreSamplingRate t
  let N := popularSumThreshold t / 2
  have htPosNat : 0 < t := Nat.zero_lt_of_lt
    (one_lt_of_smallSumsetClassCountThreshold_le ht)
  have htPos : (0 : ℝ) < t := by exact_mod_cast htPosNat
  have hqPos : 0 < q := coreSamplingRate_pos ht
  have hqLt : q < 1 := coreSamplingRate_lt_one ht
  have hbase : 0 ≤ 1 - q ^ (2 : ℕ) := by
    have hqSq : q ^ (2 : ℕ) ≤ 1 := by nlinarith [sq_nonneg (1 - q)]
    linarith
  have hstep : (1 - q ^ (2 : ℕ)) ^ N ≤
      Real.exp (-(N : ℝ) * q ^ (2 : ℕ)) := by
    refine (pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg (q ^ (2 : ℕ))) N).trans_eq ?_
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hproduct : (t : ℝ) ^ ((1 : ℝ) / 15) / 6 ≤
      (N : ℝ) * q ^ (2 : ℕ) := by
    rw [← coreSamplingRate_sq_mul_rpow_one_fifth htPosNat]
    nlinarith [mul_le_mul_of_nonneg_left (popularSumThreshold_half_lower ht)
      (sq_nonneg q)]
  have hexp : Real.exp (-(N : ℝ) * q ^ (2 : ℕ)) ≤
      Real.exp (-((t : ℝ) ^ ((1 : ℝ) / 15) / 6)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hproduct]
  refine hstep.trans (hexp.trans ?_)
  conv_rhs => rw [Real.rpow_def_of_pos htPos]
  apply Real.exp_le_exp.mpr
  nlinarith [rpow_one_fifteenth_le_six_mul_log_bound ht]


theorem exists_core_decomposition_with_budget (A : Finset ℕ) {t m : ℕ}
    (hA : A.card = t) (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (restrictedSumset A).card ≤ m) :
    ∃ a A₀ Z, a ∈ A ∧ A₀ ⊆ A ∧ Z ⊆ A ∧
      (A \ Z).image (a + ·) ⊆ restrictedSumset A₀ ∧
      (A₀.card : ℝ) + exceptionPenalty t * Z.card ≤
        coreDecompositionBudget t m := by
  have hA0 : A.Nonempty := Finset.card_pos.mp (hA.trans_gt
    (one_lt_of_smallSumsetClassCountThreshold_le ht).le)
  simpa only [coreDecompositionBudget] using exists_core_decomposition A hA hA0 hm
    (popularSumThreshold t) (coreSamplingRate_pos ht)
    (coreSamplingRate_lt_one ht) (exceptionPenalty_nonneg t)

private structure CoreDecompositionWitness (A : Finset ℕ) (t m : ℕ) where
  anchor : ℕ
  core : Finset ℕ
  exceptions : Finset ℕ
  anchor_mem : anchor ∈ A
  core_subset : core ⊆ A
  exceptions_subset : exceptions ⊆ A
  translate_subset : (A \ exceptions).image (anchor + ·) ⊆ restrictedSumset core
  budget : (core.card : ℝ) + exceptionPenalty t * exceptions.card ≤
    coreDecompositionBudget t m

private lemma coreDecompositionWitness_nonempty (A : Finset ℕ) {t m : ℕ}
    (hA : A.card = t) (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (restrictedSumset A).card ≤ m) : Nonempty (CoreDecompositionWitness A t m) := by
  obtain ⟨a, A₀, Z, ha, hA₀, hZ, htranslate, hbudget⟩ :=
    exists_core_decomposition_with_budget A hA ht hm
  exact ⟨⟨a, A₀, Z, ha, hA₀, hZ, htranslate, hbudget⟩⟩

private noncomputable def coreDecompositionWitness (A : Finset ℕ) {t m : ℕ}
    (hA : A.card = t) (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (restrictedSumset A).card ≤ m) : CoreDecompositionWitness A t m :=
  Classical.choice (coreDecompositionWitness_nonempty A hA ht hm)

def FreimanEquivalent (order : ℕ) (A B : Finset ℕ) : Prop :=
  ∃ f : ℕ → ℕ, IsAddFreimanIso order (A : Set ℕ) (B : Set ℕ) f

/-- `representatives` contains a representative of every Freiman class meeting `family`. -/
def CoversFreimanClasses (order : ℕ) (family : Set (Finset ℕ))
    (representatives : Finset (Finset ℕ)) : Prop :=
  ∀ A ∈ family, ∃ B ∈ representatives, FreimanEquivalent order A B

/-- Integer `t`-sets whose restricted sumset has size at most `m`. -/
def smallRestrictedSumsetSets (t m : ℕ) : Set (Finset ℕ) :=
  {A | A.card = t ∧ (restrictedSumset A).card ≤ m}

/-- The integral upper bound for the size of Green's sampled core. -/
def coreCardBound (t m : ℕ) : ℕ :=
  ⌈4 * coreSamplingRate t * m⌉₊

/-- The integral upper bound for the number of exceptional elements. -/
def exceptionCardBound (t m : ℕ) : ℕ :=
  ⌈4 * (t : ℝ) ^ (-(4 : ℝ) / 5) * m⌉₊

/-- A restricted sumset of a sufficiently large integer set contains at least as many elements
as the original set.  This supplies `t ≤ m` to the analytic core-budget estimate. -/
lemma card_le_card_restrictedSumset_of_three_le (A : Finset ℕ) (hA : 3 ≤ A.card) :
    A.card ≤ (restrictedSumset A).card := by
  have hA_nonempty : A.Nonempty := Finset.one_le_card.mp (by omega)
  have hcard_sub_one := card_sub_one_le_card_restrictedSumset hA_nonempty
  by_contra! hlt
  have hcard_eq : (restrictedSumset A).card = A.card - 1 := by omega
  set a := A.min' hA_nonempty
  have ha_mem : a ∈ A := Finset.min'_mem _ hA_nonempty
  have hinj_surj : (A.erase a).image (a + ·) = restrictedSumset A := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [restrictedSumset, Finset.mem_image]
      refine ⟨(a, x), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨ha_mem, Finset.mem_of_mem_erase hx⟩, (Finset.ne_of_mem_erase hx).symm⟩
    · rw [Finset.card_image_of_injective (A.erase a) (add_right_injective a),
        Finset.card_erase_of_mem ha_mem, hcard_eq]
  have hM_ne_a : A.max' hA_nonempty ≠ a := by
    intro h
    apply (by omega : A.card ≠ 1)
    apply Finset.card_eq_one.mpr
    refine ⟨a, ?_⟩
    ext x
    constructor
    · intro hx
      simp only [Finset.mem_singleton]
      apply le_antisymm
      · rw [← h]
        exact Finset.le_max' _ _ hx
      · exact Finset.min'_le _ _ hx
    · intro hx
      simp only [Finset.mem_singleton] at hx
      subst x
      exact ha_mem
  have h_second_nonempty : ((A.erase a).erase (A.max' hA_nonempty)).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem
      (Finset.mem_erase.mpr ⟨hM_ne_a, Finset.max'_mem _ hA_nonempty⟩),
      Finset.card_erase_of_mem ha_mem]
    omega
  set b := ((A.erase a).erase (A.max' hA_nonempty)).max' h_second_nonempty
  have hb_mem := Finset.max'_mem _ h_second_nonempty
  have hb_mem_erase_a : b ∈ A.erase a := Finset.mem_of_mem_erase hb_mem
  have hb_mem_A : b ∈ A := Finset.mem_of_mem_erase hb_mem_erase_a
  set M := A.max' hA_nonempty
  have hsum_in_image : b + M ∈ (A.erase a).image (a + ·) := by
    rw [hinj_surj, restrictedSumset, Finset.mem_image]
    refine ⟨(b, M), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hb_mem_A, Finset.max'_mem _ hA_nonempty⟩, ?_⟩
    change b ≠ A.max' hA_nonempty
    exact Finset.ne_of_mem_erase hb_mem
  obtain ⟨x, hx, hx_eq⟩ := Finset.mem_image.mp hsum_in_image
  nlinarith [Ne.lt_of_le (Finset.ne_of_mem_erase hb_mem_erase_a).symm
      (by simpa [a] using Finset.min'_le A b hb_mem_A),
    Finset.le_max' A x (Finset.mem_of_mem_erase hx),
    Finset.le_max' A b hb_mem_A]
/-- The numerical specialization of Green's alteration budget. -/
lemma coreDecompositionBudget_le_four_mul_samplingRate {t m : ℕ}
    (ht : smallSumsetClassCountThreshold ≤ t) (htm : t ≤ m) :
    coreDecompositionBudget t m ≤ 4 * coreSamplingRate t * m := by
  unfold coreDecompositionBudget
  have ht_pos : 0 < t := Nat.zero_lt_of_lt (one_lt_of_smallSumsetClassCountThreshold_le ht)
  have ht_pos_real : (0 : ℝ) < t := by exact_mod_cast ht_pos
  have htm_real : (t : ℝ) ≤ m := by exact_mod_cast htm
  have htail : (1 - coreSamplingRate t ^ 2) ^ (popularSumThreshold t / 2) ≤
      (t : ℝ) ^ (-(4 : ℝ) / 5) := samplingFailureProbability_le ht
  have hgpt_le : (popularSumThreshold t : ℝ) ≤ (t : ℝ) ^ ((1 : ℝ) / 5) := by
    unfold popularSumThreshold
    have h_nonneg : 0 ≤ (t : ℝ) ^ ((1 : ℝ) / 5) := by positivity
    exact mod_cast Nat.floor_le h_nonneg
  apply le_trans (b := coreSamplingRate t * m + 3 * coreSamplingRate t * m)
  · apply add_le_add
    · exact mul_le_mul_of_nonneg_left htm_real (coreSamplingRate_pos ht).le
    rw [mul_add, mul_add, mul_one]
    apply le_trans (b := (coreSamplingRate t * m + coreSamplingRate t * m) +
      coreSamplingRate t * m)
    · apply add_le_add
      · apply add_le_add
        · unfold exceptionPenalty coreSamplingRate
          apply le_trans (b := (t : ℝ) ^ ((14 : ℝ) / 15))
          · refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast ht_pos) ?_
            norm_num
          convert mul_le_mul_of_nonneg_left htm_real
            (Real.rpow_nonneg ht_pos_real.le (-(1 : ℝ) / 15)) using 1
          conv_rhs =>
            rhs
            rw [← Real.rpow_one (t : ℝ)]
          rw [← Real.rpow_add ht_pos_real]
          congr 1
          norm_num
        · apply le_trans (b := exceptionPenalty t *
            ((t : ℝ) ^ ((1 : ℝ) / 5) * m / t))
          · exact mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right hgpt_le (Nat.cast_nonneg m)) ht_pos_real.le)
              (exceptionPenalty_nonneg t)
          rw [mul_div_assoc, ← mul_assoc, exceptionPenalty_mul_rpow_one_fifth ht_pos]
          field_simp [ht_pos_real.ne']
          exact le_rfl
      · refine (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg t))
          (exceptionPenalty_nonneg t)).trans ?_
        rw [mul_comm (t : ℝ) ((t : ℝ) ^ (-(4 : ℝ) / 5)), ← mul_assoc,
          exceptionPenalty_mul_rpow_neg_four_fifths ht_pos]
        exact mul_le_mul_of_nonneg_left htm_real (coreSamplingRate_pos ht).le
    · ring_nf
      exact le_rfl
  · ring_nf
    exact le_rfl

/-- Green's Proposition 2 with all asymptotic notation replaced by the explicit parameters used
in the class count. -/
theorem exists_core_decomposition_with_card_bounds (A : Finset ℕ) {t m : ℕ}
    (hA : A.card = t) (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (restrictedSumset A).card ≤ m) :
    ∃ a ∈ A, ∃ A₀ ⊆ A, ∃ A₁ ⊆ A,
      A₁.image (a + ·) ⊆ restrictedSumset A₀ ∧
      (A₀.card : ℝ) ≤ 4 * coreSamplingRate t * m ∧
      ((A \ A₁).card : ℝ) ≤ 4 * (t : ℝ) ^ (-(4 : ℝ) / 5) * m := by
  have ht_pos : 0 < t := Nat.zero_lt_of_lt (one_lt_of_smallSumsetClassCountThreshold_le ht)
  have htm : t ≤ m := by
    rw [← hA]
    refine (card_le_card_restrictedSumset_of_three_le A ?_).trans hm
    rw [hA]
    refine le_trans ?_ ht
    exact (by norm_num : 3 ≤ 2 ^ (200 : ℕ)).trans
      two_pow_200_le_smallSumsetClassCountThreshold
  obtain ⟨a, A₀, Z, ha, hA₀, hZ, htranslate, hbudget⟩ :=
    exists_core_decomposition_with_budget A hA ht hm
  refine ⟨a, ha, A₀, hA₀, A \ Z, Finset.sdiff_subset, ?_, ?_, ?_⟩
  · simpa using htranslate
  · nlinarith [hbudget, coreDecompositionBudget_le_four_mul_samplingRate ht htm,
      mul_nonneg (exceptionPenalty_nonneg t) (by positivity : 0 ≤ (Z.card : ℝ))]
  · rw [Finset.sdiff_sdiff_self_left, Finset.inter_eq_right.mpr hZ]
    have hexceptionPenalty_pos : 0 < exceptionPenalty t := by
      unfold exceptionPenalty
      positivity
    apply le_of_mul_le_mul_left (a := exceptionPenalty t) ?_ hexceptionPenalty_pos
    ring_nf
    rw [exceptionPenalty_mul_rpow_neg_four_fifths ht_pos]
    nlinarith [hbudget, coreDecompositionBudget_le_four_mul_samplingRate ht htm,
      (by positivity : 0 ≤ (A₀.card : ℝ))]
/-- Two sets with the same `freimanRelationCode` are `s`-Freiman equivalent. -/
lemma freimanEquivalent_of_canonicalCode_eq {s t : ℕ} (ht : 0 < t) (X Y : SizedNatFinset t)
    (hcode : canonicalFreimanRelationCode (s := s) ht X =
             canonicalFreimanRelationCode (s := s) ht Y) :
    FreimanEquivalent s X.1 Y.1 := by
  obtain ⟨eX, hcodeX⟩ := exists_canonicalLabeling ht X
  obtain ⟨eY, hcodeY⟩ := exists_canonicalLabeling ht Y
  have hcode' : freimanRelationCode (s := s) ht (permutedFinsetTuple X eX) =
               freimanRelationCode (s := s) ht (permutedFinsetTuple Y eY) := by
    rw [hcodeX, hcodeY, hcode]
  set a := permutedFinsetTuple X eX with ha_def
  set b := permutedFinsetTuple Y eY with hb_def
  have ha_inj : Function.Injective a := permutedFinsetTuple_injective X eX
  have hb_inj : Function.Injective b := permutedFinsetTuple_injective Y eY
  have ha_range : (X.1 : Set ℕ) = Set.range a := (range_permutedFinsetTuple X eX).symm
  have hb_range : (Y.1 : Set ℕ) = Set.range b := (range_permutedFinsetTuple Y eY).symm
  have hrelations : ∀ p : FreimanRelationIndex s t,
      freimanRelationHolds a p ↔ freimanRelationHolds b p :=
    freimanRelations_iff_of_code_eq ht hcode'
  haveI : Nonempty (Fin t) := ⟨⟨0, ht⟩⟩
  classical
  let f : ℕ → ℕ := fun x =>
    if hx : x ∈ Set.range a then b (Function.invFun a x) else 0
  have hf_on_range (i : Fin t) : f (a i) = b i := by
    dsimp [f]
    rw [if_pos (Set.mem_range_self i), Function.leftInverse_invFun ha_inj]
  unfold FreimanEquivalent
  refine ⟨f, ?_⟩
  rw [ha_range, hb_range]
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx; rcases hx with ⟨i, rfl⟩; exact ⟨i, (hf_on_range i).symm⟩
    · intro x hx y hy hxy
      rcases hx with ⟨i, rfl⟩; rcases hy with ⟨j, rfl⟩
      rw [hf_on_range i, hf_on_range j] at hxy
      exact congrArg a (hb_inj hxy)
    · intro y hy; rcases hy with ⟨i, rfl⟩; exact ⟨a i, ⟨i, rfl⟩, hf_on_range i⟩
  · intro u v huA hvA hu_card hv_card
    have hu_range (x : ℕ) (hx : x ∈ u) : x ∈ Set.range a := huA hx
    have hv_range (x : ℕ) (hx : x ∈ v) : x ∈ Set.range a := hvA hx
    let u' : Multiset (Fin t) := u.map (Function.invFun a)
    let v' : Multiset (Fin t) := v.map (Function.invFun a)
    have hu_eq_map_a : u = u'.map a := by
      dsimp only [u']
      conv_lhs => rw [← Multiset.map_id u]
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro x hx
      simp [Function.invFun_eq (hu_range x hx)]
    have hv_eq_map_a : v = v'.map a := by
      dsimp only [v']
      conv_lhs => rw [← Multiset.map_id v]
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro x hx
      simp [Function.invFun_eq (hv_range x hx)]
    have hu_map_f_eq_map_b : u.map f = u'.map b := by
      dsimp only [u']
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro x hx
      dsimp [f]
      rw [if_pos (hu_range x hx)]
    have hv_map_f_eq_map_b : v.map f = v'.map b := by
      dsimp only [v']
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro x hx
      dsimp [f]
      rw [if_pos (hv_range x hx)]
    let Lu := u'.sort (· ≤ ·)
    let Lv := v'.sort (· ≤ ·)
    have hLu_len : Lu.length = s := by
      rw [Multiset.length_sort, Multiset.card_map, hu_card]
    have hLv_len : Lv.length = s := by
      rw [Multiset.length_sort, Multiset.card_map, hv_card]
    have sum_eq_sorted (w : Multiset (Fin t)) (g : Fin t → ℕ) :
        (w.map g).sum = ((w.sort (· ≤ ·)).map g).sum := by
      have hsorted : ((w.sort (· ≤ ·) : List (Fin t)) : Multiset (Fin t)) = w :=
        Multiset.sort_eq w (· ≤ ·)
      calc
        (w.map g).sum = (((w.sort (· ≤ ·) : List (Fin t)) : Multiset (Fin t)).map g).sum := by
          rw [hsorted]
        _ = ((w.sort (· ≤ ·)).map g).sum := rfl
    have sorted_sum_eq_fin_sum (L : List (Fin t)) (hL : L.length = s)
        (g : Fin t → ℕ) :
        (L.map g).sum = ∑ i : Fin s, g (L.get ⟨i, by rw [hL]; exact i.isLt⟩) := by
      rw [← List.sum_ofFn]
      congr 1
      apply List.ext_get_iff.mpr
      constructor
      · simp [hL]
      · intro n hn1 hn2
        simp
    let p : Fin s → Fin t := fun i => Lu.get ⟨i.1, by rw [hLu_len]; exact i.2⟩
    let q : Fin s → Fin t := fun i => Lv.get ⟨i.1, by rw [hLv_len]; exact i.2⟩
    have hsum_Lu (g : Fin t → ℕ) : (Lu.map g).sum = ∑ i : Fin s, g (p i) := by
      simpa only [p] using sorted_sum_eq_fin_sum Lu hLu_len g
    have hsum_Lv (g : Fin t → ℕ) : (Lv.map g).sum = ∑ i : Fin s, g (q i) := by
      simpa only [q] using sorted_sum_eq_fin_sum Lv hLv_len g
    constructor
    · intro h
      have hb_holds : freimanRelationHolds b (p, q) := by
        unfold freimanRelationHolds
        rw [← hsum_Lu b, ← sum_eq_sorted u' b, ← hu_map_f_eq_map_b,
          h, hv_map_f_eq_map_b, sum_eq_sorted v' b, hsum_Lv b]
      have ha_holds := (hrelations (p, q)).mpr hb_holds
      unfold freimanRelationHolds at ha_holds
      rw [hu_eq_map_a, sum_eq_sorted u' a, hsum_Lu a, ha_holds,
        ← hsum_Lv a, ← sum_eq_sorted v' a, ← hv_eq_map_a]
    · intro h
      have ha_holds : freimanRelationHolds a (p, q) := by
        unfold freimanRelationHolds
        rw [← hsum_Lu a, ← sum_eq_sorted u' a, ← hu_eq_map_a, h,
          hv_eq_map_a, sum_eq_sorted v' a, hsum_Lv a]
      have hb_holds := (hrelations (p, q)).mp ha_holds
      unfold freimanRelationHolds at hb_holds
      rw [hu_map_f_eq_map_b, sum_eq_sorted u' b, hsum_Lu b, hb_holds,
        ← hsum_Lv b, ← sum_eq_sorted v' b, ← hv_map_f_eq_map_b]

/-- Every nonempty core of size at most `L` belongs to one of at most
`∑ l ≤ L, l^(16*l)` many `8`-relation classes. -/
lemma freimanEquivalent_implies_freimanRelationEquivalent {s t : ℕ} (ht : 0 < t)
    {A B : Finset ℕ} (hA : A.card = t) (hB : B.card = t)
    (h : FreimanEquivalent s A B) :
    FreimanRelationEquivalent (s := s) (⟨A, hA⟩ : SizedNatFinset t)
      (⟨B, hB⟩ : SizedNatFinset t) := by
  obtain ⟨f, hf⟩ := h
  let a := finsetTuple A hA
  let b := finsetTuple B hB
  have ha_inj : Function.Injective a := finsetTuple_injective A hA
  have hb_inj : Function.Injective b := finsetTuple_injective B hB
  have ha_range : (A : Set ℕ) = Set.range a := (range_finsetTuple A hA).symm
  have hb_range : (B : Set ℕ) = Set.range b := (range_finsetTuple B hB).symm
  have hfa_inj : Function.Injective (f ∘ a) := by
    intro i j hij
    apply ha_inj
    apply hf.bijOn.injOn
    · rw [ha_range]
      exact Set.mem_range_self i
    · rw [ha_range]
      exact Set.mem_range_self j
    · exact hij
  have hfa_range : Set.range (f ∘ a) = (B : Set ℕ) := by
    rw [Set.range_comp, ← ha_range, hf.bijOn.image_eq]
  have h_relation_iff (p : FreimanRelationIndex s t) :
      freimanRelationHolds a p ↔ freimanRelationHolds (f ∘ a) p := by
    unfold freimanRelationHolds
    let u : Multiset ℕ :=
      (Finset.univ.val : Multiset (Fin s)).map (fun i : Fin s => a (p.1 i))
    let v : Multiset ℕ :=
      (Finset.univ.val : Multiset (Fin s)).map (fun i : Fin s => a (p.2 i))
    have hsum := hf.map_sum_eq_map_sum
      (s := u) (t := v)
      (by
        intro x hx
        obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hx
        rw [ha_range]
        exact Set.mem_range_self _)
      (by
        intro x hx
        obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hx
        rw [ha_range]
        exact Set.mem_range_self _)
      (by simp [u]) (by simp [v])
    simpa [u, v, Finset.sum_map_val, List.sum_ofFn, Function.comp_apply] using hsum.symm
  haveI : Nonempty (Fin t) := ⟨⟨0, ht⟩⟩
  let e_raw : Fin t → Fin t := fun i => Function.invFun b ((f ∘ a) i)
  have h_e_b (i : Fin t) : b (e_raw i) = (f ∘ a) i := by
    apply Function.invFun_eq
    change (f ∘ a) i ∈ Set.range b
    rw [← hb_range, ← hfa_range]
    exact Set.mem_range_self i
  have h_e_bijective : Function.Bijective e_raw := by
    constructor
    · intro i j hij
      apply hfa_inj
      rw [← h_e_b i, ← h_e_b j, hij]
    · intro k
      obtain ⟨i, hi⟩ : ∃ i, (f ∘ a) i = b k := by
        rw [← Set.mem_range, hfa_range, hb_range]
        exact Set.mem_range_self k
      refine ⟨i, ?_⟩
      dsimp [e_raw]
      change Function.invFun b ((f ∘ a) i) = k
      rw [hi, Function.leftInverse_invFun hb_inj]
  let e : Equiv.Perm (Fin t) := Equiv.ofBijective e_raw h_e_bijective
  have h_e_b' (i : Fin t) : b (e i) = (f ∘ a) i := by
    simpa [e] using h_e_b i
  refine ⟨e, ?_⟩
  intro p
  rw [h_relation_iff p]
  unfold permutedFinsetTuple freimanRelationHolds
  change (∑ i, (f ∘ a) (p.1 i)) = (∑ i, (f ∘ a) (p.2 i)) ↔
    (∑ i, b (e (p.1 i))) = ∑ i, b (e (p.2 i))
  simp_rw [h_e_b']
/-- Sets obtained by adjoining `d` elements to some member of the `4`-class of `base`. -/
def extensionsOfFreimanClass (base : Finset ℕ) (d : ℕ) : Set (Finset ℕ) :=
  {A | ∃ B : Finset ℕ, B ⊆ A ∧ B.card = base.card ∧
    A.card = B.card + d ∧ FreimanEquivalent 4 B base}

private lemma freimanRelationEquivalent_symm {s t : ℕ} {X Y : SizedNatFinset t}
    (h : FreimanRelationEquivalent (s := s) X Y) :
    FreimanRelationEquivalent (s := s) Y X := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, ?_⟩
  intro p
  simpa only [permutedFinsetTuple, freimanRelationHolds_comp_perm,
    freimanRelationHolds, permuteFreimanRelation, Equiv.coe_trans,
    Function.comp_def, Equiv.apply_symm_apply] using
    (he (permuteFreimanRelation e.symm p)).symm

/-- Green's extension lemma in class-cover form. -/
lemma exists_extensionFreimanClassCover (base : Finset ℕ) (d : ℕ)
    (hbase : base.Nonempty) :
    ∃ representatives : Finset (Finset ℕ),
      CoversFreimanClasses 2 (extensionsOfFreimanClass base d) representatives ∧
      representatives.card ≤
        (1 + base.card ^ 4) ^ ((d + 1) ^ 4) := by
  classical
  set l := base.card with hl_def
  have hl : 0 < l := Finset.card_pos.mpr hbase
  have hl_d_pos : 0 < l + d := by omega
  have hbase_card_val : base.card = l := rfl
  let family : Set (SizedNatFinset (l + d)) := {X | X.1 ∈ extensionsOfFreimanClass base d}
  have h_codes_image_finite : Set.Finite
      (canonicalFreimanRelationCode (s := 2) hl_d_pos '' family) :=
    Set.toFinite _
  let codes_finset : Finset (Fin (l + d) → FreimanRelationIndex 2 (l + d)) :=
    h_codes_image_finite.toFinset
  have hcodes_card_eq : codes_finset.card =
      (canonicalFreimanRelationCode (s := 2) hl_d_pos '' family).ncard :=
    (Set.ncard_eq_toFinset_card (hs := h_codes_image_finite)).symm
  have h_exists_forall_code (code : Fin (l + d) → FreimanRelationIndex 2 (l + d))
      (hcode : code ∈ codes_finset) : ∃ X : SizedNatFinset (l + d),
        X ∈ family ∧ canonicalFreimanRelationCode (s := 2) hl_d_pos X = code := by
    have hcode_img : code ∈ canonicalFreimanRelationCode (s := 2) hl_d_pos '' family :=
      h_codes_image_finite.mem_toFinset.mp hcode
    rcases hcode_img with ⟨X, hX, hXcode⟩
    exact ⟨X, hX, hXcode⟩
  have hcodes_card_le : codes_finset.card ≤ (1 + l ^ 4) ^ ((d + 1) ^ 4) := by
    let S : Finset (SizedNatFinset (l + d)) :=
      Finset.image (fun hc : codes_finset =>
        Classical.choose (h_exists_forall_code hc.1 hc.2))
        Finset.univ
    have hS_in_family : ∀ X ∈ S, X ∈ family := by
      intro X hX
      rcases Finset.mem_image.mp hX with ⟨hc, -, rfl⟩
      exact (Classical.choose_spec (h_exists_forall_code hc.1 hc.2)).1
    have h_exists_label (X : SizedNatFinset (l + d)) (hX : X ∈ S) :
        ∃ a : Fin (l + d) → ℕ,
          Function.Injective a ∧ Set.range a = X.1 ∧
            ∀ p : FreimanRelationIndex 4 l,
              freimanRelationHolds (extensionBaseTuple a) p ↔
                freimanRelationHolds (finsetTuple base hbase_card_val) p := by
      have hX_ext : X.1 ∈ extensionsOfFreimanClass base d := hS_in_family X hX
      rcases hX_ext with ⟨B, hB, hB_card, hA_card_sum, hB_equiv⟩
      have hZ : (X.1 \ B).card = d := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hB, X.2, hB_card]
        omega
      obtain ⟨e, he⟩ := freimanRelationEquivalent_symm
        (freimanEquivalent_implies_freimanRelationEquivalent hl hB_card
          hbase_card_val hB_equiv)
      refine ⟨extensionFinsetTuple X.1 B hB_card hZ e,
        extensionFinsetTuple_injective hB_card hZ e,
        range_extensionFinsetTuple hB hB_card hZ e, ?_⟩
      intro p
      rw [extensionBaseTuple_extensionFinsetTuple X.1 B hB_card hZ e]
      exact (he p).symm
    let label (X : SizedNatFinset (l + d)) : Fin (l + d) → ℕ :=
      if hX : X ∈ S then Classical.choose (h_exists_label X hX) else fun _ => 0
    have hlabel_spec (X : SizedNatFinset (l + d)) (hX : X ∈ S) :
        Function.Injective (label X) ∧ Set.range (label X) = X.1 ∧
          ∀ p : FreimanRelationIndex 4 l,
            freimanRelationHolds (extensionBaseTuple (label X)) p ↔
              freimanRelationHolds (finsetTuple base hbase_card_val) p := by
      simp only [label, dif_pos hX]
      exact Classical.choose_spec (h_exists_label X hX)
    have hbound : (S.image fun X =>
        canonicalFreimanRelationCode (s := 2) hl_d_pos X).card ≤
        (1 + l ^ 4) ^ ((d + 1) ^ 4) := by
      refine card_canonicalFreimanRelationCode_image_of_fixed_extensionBase hl S
        (fun X => X) label ?_ ?_ ?_
      · intro X hX
        exact (hlabel_spec X hX).1
      · intro X hX
        exact (hlabel_spec X hX).2.1
      · intro X hX Y hY p
        rw [(hlabel_spec X hX).2.2 p, (hlabel_spec Y hY).2.2 p]
    convert hbound using 1
    congr 1
    ext code
    constructor
    · intro hcode
      let hc : codes_finset := ⟨code, hcode⟩
      refine Finset.mem_image.mpr ⟨Classical.choose
        (h_exists_forall_code hc.1 hc.2), ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨hc, Finset.mem_univ _, rfl⟩
      · exact (Classical.choose_spec (h_exists_forall_code hc.1 hc.2)).2
    · intro hcode
      rcases Finset.mem_image.mp hcode with ⟨X, hX, rfl⟩
      rcases Finset.mem_image.mp hX with ⟨hc, -, rfl⟩
      rw [(Classical.choose_spec (h_exists_forall_code hc.1 hc.2)).2]
      exact hc.2
  let pick (code : Fin (l + d) → FreimanRelationIndex 2 (l + d)) : Finset ℕ :=
    if hcode : code ∈ codes_finset then
      (Classical.choose (h_exists_forall_code code hcode)).1
    else ∅
  let representatives : Finset (Finset ℕ) := Finset.image pick codes_finset
  refine ⟨representatives, ?_, ?_⟩
  · intro A hA
    rcases hA with ⟨B, hB, hB_card, hA_card, hB_equiv⟩
    have hA_size : A.card = l + d := by omega
    let X : SizedNatFinset (l + d) := ⟨A, hA_size⟩
    have hX_family : X ∈ family :=
      ⟨B, hB, hB_card, hA_card, hB_equiv⟩
    have hcode : canonicalFreimanRelationCode (s := 2) hl_d_pos X ∈ codes_finset :=
      h_codes_image_finite.mem_toFinset.mpr ⟨X, hX_family, rfl⟩
    let Y := Classical.choose (h_exists_forall_code
      (canonicalFreimanRelationCode (s := 2) hl_d_pos X) hcode)
    have hY_spec : Y ∈ family ∧ canonicalFreimanRelationCode (s := 2) hl_d_pos Y =
        canonicalFreimanRelationCode (s := 2) hl_d_pos X :=
      Classical.choose_spec (h_exists_forall_code
        (canonicalFreimanRelationCode (s := 2) hl_d_pos X) hcode)
    refine ⟨Y.1, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨canonicalFreimanRelationCode (s := 2) hl_d_pos X, hcode, ?_⟩
      simp only [pick, dif_pos hcode]
      rfl
    · exact freimanEquivalent_of_canonicalCode_eq hl_d_pos X Y hY_spec.2.symm
  · exact Finset.card_image_le.trans hcodes_card_le

/-- Remainders arising from cores in one fixed `8`-class.  Translation is harmless because all
relations considered here have the same number of terms on both sides. -/
def remaindersFromCoreClass (core : Finset ℕ) (u : ℕ) : Set (Finset ℕ) :=
  {B | B.card = u ∧ ∃ C : Finset ℕ,
    C.card = core.card ∧ FreimanEquivalent 8 C core ∧ B ⊆ restrictedSumset C}

/-- Green's Lemma 36: after fixing the core's `8`-class, the possible remainders occupy at most
`choose |core ⊕ core| u` many `4`-relation classes. -/
lemma exists_remainderFreimanClassCover (core : Finset ℕ) (u : ℕ)
    (hcore : core.Nonempty) :
    ∃ representatives : Finset (Finset ℕ),
      CoversFreimanClasses 4 (remaindersFromCoreClass core u) representatives ∧
      (∀ R ∈ representatives, R.card = u) ∧
      representatives.card ≤ (restrictedSumset core).card.choose u := by
  classical
  have hl_pos : 0 < core.card := Finset.card_pos.mpr hcore
  by_cases hu : u = 0
  · subst u
    refine ⟨{∅}, ?_, ?_, ?_⟩
    · intro A hA
      rcases hA with ⟨hA_card, C, hC_card, hC_eq, hA_subset⟩
      have hA_empty : A = ∅ := Finset.card_eq_zero.mp hA_card
      subst A
      refine ⟨∅, by simp, ?_⟩
      refine ⟨fun _ ↦ 0, ?_⟩
      simpa only [Finset.coe_empty] using
        (isAddFreimanIso_empty (n := 4) (α := ℕ) (β := ℕ)
          (f := fun _ : ℕ ↦ 0))
    · simp
    · simp
  · have hu_pos : 0 < u := Nat.pos_of_ne_zero hu
    let family : Set (SizedNatFinset u) := {X | X.1 ∈ remaindersFromCoreClass core u}
    have hfamily : ∀ B ∈ family, ∃ A : SizedNatFinset core.card,
        B.1 ⊆ restrictedSumset A.1 ∧
          canonicalFreimanRelationCode (s := 8) hl_pos A =
            canonicalFreimanRelationCode (s := 8) hl_pos ⟨core, rfl⟩ := by
      intro B hB
      have hB_remainder : B.1 ∈ remaindersFromCoreClass core u := hB
      rcases hB_remainder with ⟨hB_card, C, hC_card, hC_eq, hB_subset⟩
      refine ⟨⟨C, hC_card⟩, hB_subset, ?_⟩
      have h_equiv : FreimanRelationEquivalent (s := 8)
          (⟨C, hC_card⟩ : SizedNatFinset core.card)
          (⟨core, rfl⟩ : SizedNatFinset core.card) :=
        freimanEquivalent_implies_freimanRelationEquivalent hl_pos hC_card rfl hC_eq
      exact canonicalFreimanRelationCode_eq_of_equivalent hl_pos h_equiv
    have h_ncard_bound : (canonicalFreimanRelationCode (s := 4) hu_pos '' family).ncard ≤
        (restrictedSumset core).card.choose u :=
      ncard_restrictedSumset_subset_class_image_le hl_pos hu_pos ⟨core, rfl⟩ family hfamily
    have h_image_finite : Set.Finite (canonicalFreimanRelationCode (s := 4) hu_pos '' family) :=
      Set.toFinite _
    let codes_finset : Finset (Fin u → FreimanRelationIndex 4 u) :=
      h_image_finite.toFinset
    have hcodes_card_le : codes_finset.card ≤ (restrictedSumset core).card.choose u := by
      rw [← Set.ncard_eq_toFinset_card (hs := h_image_finite)]
      exact h_ncard_bound
    have h_exists_forall_code (code : Fin u → FreimanRelationIndex 4 u)
        (hcode : code ∈ codes_finset) : ∃ X : SizedNatFinset u,
          X ∈ family ∧ canonicalFreimanRelationCode (s := 4) hu_pos X = code := by
      have hcode_img : code ∈ canonicalFreimanRelationCode (s := 4) hu_pos '' family :=
        h_image_finite.mem_toFinset.mp hcode
      rcases hcode_img with ⟨X, hX, hXcode⟩
      exact ⟨X, hX, hXcode⟩
    let chosen (code : Fin u → FreimanRelationIndex 4 u)
        (hcode : code ∈ codes_finset) : SizedNatFinset u :=
      Classical.choose (h_exists_forall_code code hcode)
    have chosen_spec (code : Fin u → FreimanRelationIndex 4 u)
        (hcode : code ∈ codes_finset) :
        chosen code hcode ∈ family ∧
          canonicalFreimanRelationCode (s := 4) hu_pos (chosen code hcode) = code := by
      simpa only [chosen] using Classical.choose_spec (h_exists_forall_code code hcode)
    let pick (code : Fin u → FreimanRelationIndex 4 u) : Finset ℕ :=
      if h : code ∈ codes_finset then
        (chosen code h).1
      else
        ∅
    let representatives : Finset (Finset ℕ) := Finset.image pick codes_finset
    refine ⟨representatives, ?_, ?_, ?_⟩
    · intro A hA_rem
      have hA_card : A.card = u := by
        rcases hA_rem with ⟨hA_card', C', hC_card', hC_eq', hA_subset'⟩
        exact hA_card'
      let X : SizedNatFinset u := ⟨A, hA_card⟩
      have hX_family : X ∈ family := hA_rem
      have hcanonical_code : canonicalFreimanRelationCode (s := 4) hu_pos X
          ∈ canonicalFreimanRelationCode (s := 4) hu_pos '' family :=
        ⟨X, hX_family, rfl⟩
      have hcode_finset : canonicalFreimanRelationCode (s := 4) hu_pos X ∈ codes_finset :=
        h_image_finite.mem_toFinset.mpr hcanonical_code
      let Y := chosen (canonicalFreimanRelationCode (s := 4) hu_pos X) hcode_finset
      have hY_spec : Y ∈ family ∧ canonicalFreimanRelationCode (s := 4) hu_pos Y =
          canonicalFreimanRelationCode (s := 4) hu_pos X :=
        chosen_spec (canonicalFreimanRelationCode (s := 4) hu_pos X) hcode_finset
      have hY_rep : Y.1 ∈ representatives := by
        apply Finset.mem_image.mpr
        refine ⟨canonicalFreimanRelationCode (s := 4) hu_pos X, hcode_finset, ?_⟩
        dsimp [pick]
        rw [dif_pos hcode_finset]
      refine ⟨Y.1, hY_rep, ?_⟩
      exact freimanEquivalent_of_canonicalCode_eq (s := 4) hu_pos X Y hY_spec.2.symm
    · intro R hR
      rcases Finset.mem_image.mp hR with ⟨code, hcode, rfl⟩
      simp only [pick, dif_pos hcode]
      exact (chosen code hcode).2
    · exact Finset.card_image_le.trans hcodes_card_le

/-- The direct finite sum produced by the core/remainder/extension decomposition. -/
def freimanClassCountBound (t m : ℕ) : ℕ :=
  ∑ d ∈ Finset.range (exceptionCardBound t m + 1),
    ∑ l ∈ Finset.Icc 1 (coreCardBound t m),
      l ^ (16 * l) * m.choose (t - d) *
        (1 + (t - d) ^ 4) ^ ((d + 1) ^ 4)

private lemma freimanEquivalent_trans {order : ℕ} {A B C : Finset ℕ}
    (hAB : FreimanEquivalent order A B) (hBC : FreimanEquivalent order B C) :
    FreimanEquivalent order A C := by
  obtain ⟨f, hf⟩ := hAB
  obtain ⟨g, hg⟩ := hBC
  exact ⟨g ∘ f, hg.comp hf⟩

private lemma freimanEquivalent_translate (order a : ℕ) (A : Finset ℕ) :
    FreimanEquivalent order A (A.image (a + ·)) := by
  refine ⟨(a + ·), ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, Finset.mem_coe.mp hx, rfl⟩)
    · intro x hx y hy hxy
      exact Nat.add_left_cancel hxy
    · intro y hy
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hy) with ⟨x, hx, rfl⟩
      exact ⟨x, Finset.mem_coe.mpr hx, rfl⟩
  · intro s u hsA huA hs hu
    have htranslate (v : Multiset ℕ) :
        (v.map (a + ·)).sum = v.card * a + v.sum := by
      induction v using Multiset.induction_on with
      | empty => simp
      | @cons x v ih =>
          simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih,
            Nat.add_mul]
          omega
    rw [htranslate s, htranslate u, hs, hu]
    exact add_left_cancel_iff

private lemma exists_exactSmallCoreFreimanClassCover (l m : ℕ) (hl : 0 < l) :
    ∃ representatives : Finset (Finset ℕ),
      CoversFreimanClasses 8
        {A | A.card = l ∧ (restrictedSumset A).card ≤ m} representatives ∧
      (∀ C ∈ representatives, C.card = l ∧ (restrictedSumset C).card ≤ m) ∧
      representatives.card ≤ l ^ (16 * l) := by
  classical
  let family : Set (SizedNatFinset l) :=
    {X | (restrictedSumset X.1).card ≤ m}
  have hcodes_finite :
      (canonicalFreimanRelationCode (s := 8) hl '' family).Finite := Set.toFinite _
  let codes := hcodes_finite.toFinset
  have h_exists (code : Fin l → FreimanRelationIndex 8 l) (hcode : code ∈ codes) :
      ∃ X : SizedNatFinset l, X ∈ family ∧
        canonicalFreimanRelationCode (s := 8) hl X = code := by
    rcases hcodes_finite.mem_toFinset.mp hcode with ⟨X, hX, rfl⟩
    exact ⟨X, hX, rfl⟩
  let pick (code : Fin l → FreimanRelationIndex 8 l) : Finset ℕ :=
    if hcode : code ∈ codes then (Classical.choose (h_exists code hcode)).1 else ∅
  let representatives := codes.image pick
  refine ⟨representatives, ?_, ?_, ?_⟩
  · intro A hA
    let X : SizedNatFinset l := ⟨A, hA.1⟩
    let code := canonicalFreimanRelationCode (s := 8) hl X
    have hcode : code ∈ codes :=
      hcodes_finite.mem_toFinset.mpr ⟨X, hA.2, rfl⟩
    let Y := Classical.choose (h_exists code hcode)
    refine ⟨Y.1, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨code, hcode, ?_⟩
      simp only [pick, dif_pos hcode]
      rfl
    · exact freimanEquivalent_of_canonicalCode_eq (s := 8) hl X Y
        (Classical.choose_spec (h_exists code hcode)).2.symm
  · intro C hC
    rcases Finset.mem_image.mp hC with ⟨code, hcode, rfl⟩
    simp only [pick, dif_pos hcode]
    exact ⟨(Classical.choose (h_exists code hcode)).2,
      (Classical.choose_spec (h_exists code hcode)).1⟩
  · calc
      representatives.card ≤ codes.card := Finset.card_image_le
      _ ≤ (Finset.univ : Finset (Fin l → FreimanRelationIndex 8 l)).card := by
        apply Finset.card_le_card
        intro code hcode
        exact Finset.mem_univ _
      _ = l ^ (16 * l) := by
        rw [Finset.card_univ, card_freimanRelationCodes]

private lemma exists_nonemptyCoreDecomposition (A : Finset ℕ) {t m : ℕ}
    (hA : A.card = t) (ht : smallSumsetClassCountThreshold ≤ t)
    (hm : (restrictedSumset A).card ≤ m) :
    ∃ a ∈ A, ∃ A₀ ⊆ A, ∃ A₁ ⊆ A,
      A₁.image (a + ·) ⊆ restrictedSumset A₀ ∧ A₀.Nonempty ∧ A₁.Nonempty ∧
      A₀.card ≤ coreCardBound t m ∧
      (A \ A₁).card ≤ exceptionCardBound t m := by
  have ht_pos : 0 < t :=
    Nat.zero_lt_of_lt (one_lt_of_smallSumsetClassCountThreshold_le ht)
  have htm : t ≤ m := by
    rw [← hA]
    exact (card_le_card_restrictedSumset_of_three_le A (by
      rw [hA]
      exact ht.trans'
        (two_pow_200_le_smallSumsetClassCountThreshold.trans' (by norm_num)))).trans hm
  by_cases hlarge : t ≤ coreCardBound t m
  · have hA_nonempty : A.Nonempty := by
      rw [← Finset.card_pos, hA]
      exact ht_pos
    have hm_pos : 0 < m := ht_pos.trans_le htm
    let a := A.min' hA_nonempty
    have ha : a ∈ A := Finset.min'_mem A hA_nonempty
    refine ⟨a, ha, A, Finset.Subset.rfl, A.erase a, Finset.erase_subset _ _, ?_,
      hA_nonempty, ?_, by rwa [hA], ?_⟩
    · intro y hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      rw [restrictedSumset, Finset.mem_image]
      refine ⟨(a, x), ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨ha, Finset.mem_of_mem_erase hx⟩, (Finset.ne_of_mem_erase hx).symm⟩
    · rw [← Finset.card_pos, Finset.card_erase_of_mem ha, hA]
      have := one_lt_of_smallSumsetClassCountThreshold_le ht
      omega
    · have hdiff : (A \ A.erase a).card = 1 := by
        simp [Finset.sdiff_erase, ha]
      rw [hdiff]
      unfold exceptionCardBound
      apply Nat.ceil_pos.mpr
      exact mul_pos (mul_pos (by norm_num)
        (Real.rpow_pos_of_pos (by exact_mod_cast ht_pos) _)) (by exact_mod_cast hm_pos)
  · obtain ⟨a, ha, A₀, hA₀, A₁, hA₁, htranslate, hcore, hexception⟩ :=
      exists_core_decomposition_with_card_bounds A hA ht hm
    have ht_real : (1 : ℝ) < t := by
      exact_mod_cast one_lt_of_smallSumsetClassCountThreshold_le ht
    have hpower : (t : ℝ) ^ (-(4 : ℝ) / 5) <
        (t : ℝ) ^ (-(1 : ℝ) / 15) := by
      exact Real.rpow_lt_rpow_of_exponent_lt ht_real (by norm_num)
    have hm_pos : 0 < m := ht_pos.trans_le htm
    have hexception_lt_core :
        4 * (t : ℝ) ^ (-(4 : ℝ) / 5) * m <
          4 * coreSamplingRate t * m := by
      unfold coreSamplingRate
      nlinarith [mul_lt_mul_of_pos_left hpower (by positivity : 0 < 4 * (m : ℝ))]
    have hcore_lt_t : 4 * coreSamplingRate t * m < t := by
      refine lt_of_le_of_lt (Nat.le_ceil (4 * coreSamplingRate t * m)) ?_
      exact_mod_cast Nat.lt_of_not_ge hlarge
    have hdiff_lt : (A \ A₁).card < t := by
      exact_mod_cast hexception.trans_lt (hexception_lt_core.trans hcore_lt_t)
    have hA₁_nonempty : A₁.Nonempty := by
      rw [← Finset.card_pos]
      have hcards := Finset.card_sdiff_add_card_eq_card hA₁
      rw [hA] at hcards
      omega
    have hA₀_nonempty : A₀.Nonempty := by
      by_contra! hA₀_empty
      have himage_nonempty : (A₁.image (a + ·)).Nonempty :=
        hA₁_nonempty.image _
      rw [hA₀_empty] at htranslate
      simp only [restrictedSumset, Finset.product_empty, Finset.filter_empty,
        Finset.image_empty] at htranslate
      rcases himage_nonempty with ⟨y, hy⟩
      exact (by simpa using htranslate hy)
    refine ⟨a, ha, A₀, hA₀, A₁, hA₁, htranslate, hA₀_nonempty,
      hA₁_nonempty, ?_, ?_⟩
    · exact_mod_cast hcore.trans (Nat.le_ceil (4 * coreSamplingRate t * m))
    · unfold exceptionCardBound
      exact_mod_cast hexception.trans
        (Nat.le_ceil (4 * (t : ℝ) ^ (-(4 : ℝ) / 5) * m))

/-- Combinatorial assembly of the three class covers, before estimating the resulting sum. -/
lemma exists_smallRestrictedSumsetFreimanClassCover_raw (t m : ℕ)
    (ht : smallSumsetClassCountThreshold ≤ t) :
    ∃ representatives : Finset (Finset ℕ),
      CoversFreimanClasses 2 (smallRestrictedSumsetSets t m) representatives ∧
      representatives.card ≤ freimanClassCountBound t m := by
  classical
  let CoreCover (l : ℕ) := { representatives : Finset (Finset ℕ) //
    CoversFreimanClasses 8
        {A | A.card = l ∧ (restrictedSumset A).card ≤ m} representatives ∧
      (∀ C ∈ representatives, C.card = l ∧ (restrictedSumset C).card ≤ m) ∧
      representatives.card ≤ l ^ (16 * l) }
  let coreCover (l : ℕ) (hl : 0 < l) : CoreCover l :=
    ⟨Classical.choose (exists_exactSmallCoreFreimanClassCover l m hl),
      Classical.choose_spec (exists_exactSmallCoreFreimanClassCover l m hl)⟩
  let coreReps (l : ℕ) : Finset (Finset ℕ) :=
    if hl : 0 < l then
      (coreCover l hl).1
    else ∅
  have hcore_cover (l : ℕ) (hl : 0 < l) :
      CoversFreimanClasses 8
        {A | A.card = l ∧ (restrictedSumset A).card ≤ m} (coreReps l) := by
    simp only [coreReps, dif_pos hl]
    exact (coreCover l hl).2.1
  have hcore_spec (l : ℕ) (hl : 0 < l) (C : Finset ℕ) (hC : C ∈ coreReps l) :
      C.card = l ∧ (restrictedSumset C).card ≤ m := by
    simp only [coreReps, dif_pos hl] at hC
    exact (coreCover l hl).2.2.1 C hC
  have hcore_card (l : ℕ) (hl : 0 < l) :
      (coreReps l).card ≤ l ^ (16 * l) := by
    simp only [coreReps, dif_pos hl]
    exact (coreCover l hl).2.2.2
  let RemainderCover (C : Finset ℕ) (u : ℕ) := { representatives : Finset (Finset ℕ) //
    CoversFreimanClasses 4 (remaindersFromCoreClass C u) representatives ∧
      (∀ R ∈ representatives, R.card = u) ∧
      representatives.card ≤ (restrictedSumset C).card.choose u }
  let remainderCover (C : Finset ℕ) (u : ℕ) (hC : C.Nonempty) :
      RemainderCover C u :=
    ⟨Classical.choose (exists_remainderFreimanClassCover C u hC),
      Classical.choose_spec (exists_remainderFreimanClassCover C u hC)⟩
  let remainderReps (C : Finset ℕ) (u : ℕ) : Finset (Finset ℕ) :=
    if hC : C.Nonempty then
      (remainderCover C u hC).1
    else ∅
  have hremainder_cover (C : Finset ℕ) (u : ℕ) (hC : C.Nonempty) :
      CoversFreimanClasses 4 (remaindersFromCoreClass C u) (remainderReps C u) := by
    simp only [remainderReps, dif_pos hC]
    exact (remainderCover C u hC).2.1
  have hremainder_spec (C : Finset ℕ) (u : ℕ) (hC : C.Nonempty)
      (R : Finset ℕ) (hR : R ∈ remainderReps C u) : R.card = u := by
    simp only [remainderReps, dif_pos hC] at hR
    exact (remainderCover C u hC).2.2.1 R hR
  have hremainder_card (C : Finset ℕ) (u : ℕ) :
      (remainderReps C u).card ≤ (restrictedSumset C).card.choose u := by
    by_cases hC : C.Nonempty
    · simp only [remainderReps, dif_pos hC]
      exact (remainderCover C u hC).2.2.2
    · simp only [remainderReps, dif_neg hC, Finset.card_empty, Nat.zero_le]
  let ExtensionCover (R : Finset ℕ) (d : ℕ) := { representatives : Finset (Finset ℕ) //
    CoversFreimanClasses 2 (extensionsOfFreimanClass R d) representatives ∧
      representatives.card ≤ (1 + R.card ^ 4) ^ ((d + 1) ^ 4) }
  let extensionCover (R : Finset ℕ) (d : ℕ) (hR : R.Nonempty) :
      ExtensionCover R d :=
    ⟨Classical.choose (exists_extensionFreimanClassCover R d hR),
      Classical.choose_spec (exists_extensionFreimanClassCover R d hR)⟩
  let extensionReps (R : Finset ℕ) (d : ℕ) : Finset (Finset ℕ) :=
    if hR : R.Nonempty then
      (extensionCover R d hR).1
    else ∅
  have hextension_cover (R : Finset ℕ) (d : ℕ) (hR : R.Nonempty) :
      CoversFreimanClasses 2 (extensionsOfFreimanClass R d) (extensionReps R d) := by
    simp only [extensionReps, dif_pos hR]
    exact (extensionCover R d hR).2.1
  have hextension_card (R : Finset ℕ) (d : ℕ) :
      (extensionReps R d).card ≤ (1 + R.card ^ 4) ^ ((d + 1) ^ 4) := by
    by_cases hR : R.Nonempty
    · simp only [extensionReps, dif_pos hR]
      exact (extensionCover R d hR).2.2
    · simp only [extensionReps, dif_neg hR, Finset.card_empty, Nat.zero_le]
  let representatives := (Finset.range (exceptionCardBound t m + 1)).biUnion fun d =>
    (Finset.Icc 1 (coreCardBound t m)).biUnion fun l =>
      (coreReps l).biUnion fun C =>
        (remainderReps C (t - d)).biUnion fun R => extensionReps R d
  refine ⟨representatives, ?_, ?_⟩
  · intro A hA
    obtain ⟨a, ha, A₀, hA₀, A₁, hA₁, htranslate, hA₀_nonempty,
      hA₁_nonempty, hcore_bound, hexception_bound⟩ :=
      exists_nonemptyCoreDecomposition A hA.1 ht hA.2
    let d := (A \ A₁).card
    let l := A₀.card
    let B := A₁.image (a + ·)
    have hd : d ∈ Finset.range (exceptionCardBound t m + 1) := by
      rw [Finset.mem_range]
      exact lt_of_le_of_lt hexception_bound (Nat.lt_succ_self _)
    have hl : l ∈ Finset.Icc 1 (coreCardBound t m) := by
      exact Finset.mem_Icc.mpr ⟨Finset.card_pos.mpr hA₀_nonempty, hcore_bound⟩
    have hl_pos : 0 < l := (Finset.mem_Icc.mp hl).1
    have hrestricted_core : (restrictedSumset A₀).card ≤ m := by
      refine (Finset.card_le_card ?_).trans hA.2
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨⟨x₁, x₂⟩, hx₁x₂, rfl⟩
      rw [restrictedSumset, Finset.mem_image]
      refine ⟨(x₁, x₂), ?_, rfl⟩
      rcases Finset.mem_filter.mp hx₁x₂ with ⟨hx₁x₂, hne⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨hA₀ (Finset.mem_product.mp hx₁x₂).1,
          hA₀ (Finset.mem_product.mp hx₁x₂).2⟩, hne⟩
    obtain ⟨C, hC, hA₀C⟩ :=
      hcore_cover l hl_pos A₀ ⟨rfl, hrestricted_core⟩
    have hC_nonempty : C.Nonempty := by
      rw [← Finset.card_pos, (hcore_spec l hl_pos C hC).1]
      exact hl_pos
    have hB_card : B.card = t - d := by
      have himage_card : B.card = A₁.card := by
        change (A₁.image (a + ·)).card = A₁.card
        rw [Finset.card_image_of_injective]
        intro x y hxy
        exact Nat.add_left_cancel hxy
      have hcards := Finset.card_sdiff_add_card_eq_card hA₁
      rw [hA.1] at hcards
      omega
    have hB_remainder : B ∈ remaindersFromCoreClass C (t - d) := by
      refine ⟨hB_card, A₀, ?_, hA₀C, htranslate⟩
      exact rfl.trans (hcore_spec l hl_pos C hC).1.symm
    obtain ⟨R, hR, hBR⟩ :=
      hremainder_cover C (t - d) hC_nonempty B hB_remainder
    have hR_card : R.card = t - d :=
      hremainder_spec C (t - d) hC_nonempty R hR
    have hR_nonempty : R.Nonempty := by
      rw [← Finset.card_pos, hR_card]
      have hB_nonempty : B.Nonempty := hA₁_nonempty.image _
      rw [← hB_card, Finset.card_pos]
      exact hB_nonempty
    have hA₁_card : A₁.card = t - d := by
      have hcards := Finset.card_sdiff_add_card_eq_card hA₁
      rw [hA.1] at hcards
      omega
    have hA_extension : A ∈ extensionsOfFreimanClass R d := by
      refine ⟨A₁, hA₁, hA₁_card.trans hR_card.symm, ?_, ?_⟩
      · have hcards := Finset.card_sdiff_add_card_eq_card hA₁
        omega
      · exact freimanEquivalent_trans (freimanEquivalent_translate 4 a A₁) hBR
    obtain ⟨Q, hQ, hAQ⟩ := hextension_cover R d hR_nonempty A hA_extension
    refine ⟨Q, ?_, hAQ⟩
    dsimp only [representatives]
    exact Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_biUnion.mpr ⟨l, hl,
      Finset.mem_biUnion.mpr ⟨C, hC, Finset.mem_biUnion.mpr ⟨R, hR, hQ⟩⟩⟩⟩
  · calc
      representatives.card ≤
          ∑ d ∈ Finset.range (exceptionCardBound t m + 1),
            ∑ l ∈ Finset.Icc 1 (coreCardBound t m),
              ∑ C ∈ coreReps l,
                ∑ R ∈ remainderReps C (t - d), (extensionReps R d).card := by
        dsimp only [representatives]
        refine Finset.card_biUnion_le.trans ?_
        refine Finset.sum_le_sum fun d hd => ?_
        refine Finset.card_biUnion_le.trans ?_
        refine Finset.sum_le_sum fun l hl => ?_
        refine Finset.card_biUnion_le.trans ?_
        refine Finset.sum_le_sum fun C hC => ?_
        exact Finset.card_biUnion_le
      _ ≤ freimanClassCountBound t m := by
        unfold freimanClassCountBound
        refine Finset.sum_le_sum fun d hd => ?_
        refine Finset.sum_le_sum fun l hl => ?_
        have hl_pos : 0 < l := by
          have := (Finset.mem_Icc.mp hl).1
          omega
        calc
          ∑ C ∈ coreReps l,
              ∑ R ∈ remainderReps C (t - d), (extensionReps R d).card ≤
              ∑ C ∈ coreReps l,
                m.choose (t - d) * (1 + (t - d) ^ 4) ^ ((d + 1) ^ 4) := by
            refine Finset.sum_le_sum fun C hC => ?_
            calc
              ∑ R ∈ remainderReps C (t - d), (extensionReps R d).card ≤
                  ∑ _ ∈ remainderReps C (t - d),
                    (1 + (t - d) ^ 4) ^ ((d + 1) ^ 4) := by
                refine Finset.sum_le_sum fun R hR => ?_
                have hR_card : R.card = t - d := by
                  exact hremainder_spec C (t - d)
                    (Finset.card_pos.mp (by
                      rw [(hcore_spec l hl_pos C hC).1]
                      exact hl_pos)) R hR
                simpa only [hR_card] using hextension_card R d
              _ = (remainderReps C (t - d)).card *
                  (1 + (t - d) ^ 4) ^ ((d + 1) ^ 4) := by simp
              _ ≤ m.choose (t - d) *
                  (1 + (t - d) ^ 4) ^ ((d + 1) ^ 4) := by
                apply Nat.mul_le_mul_right
                exact (hremainder_card C (t - d)).trans
                  (Nat.choose_le_choose (t - d) (hcore_spec l hl_pos C hC).2)
          _ = (coreReps l).card *
              (m.choose (t - d) *
                (1 + (t - d) ^ 4) ^ ((d + 1) ^ 4)) := by simp
          _ ≤ l ^ (16 * l) * m.choose (t - d) *
              (1 + (t - d) ^ 4) ^ ((d + 1) ^ 4) := by
            rw [mul_assoc]
            exact Nat.mul_le_mul_right _ (hcore_card l hl_pos)

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


end Verification
