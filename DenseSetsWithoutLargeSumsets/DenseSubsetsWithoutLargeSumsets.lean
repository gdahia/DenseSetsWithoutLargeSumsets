/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.MainTheorem
import DenseSetsWithoutLargeSumsets.CountingSumsetsOfModerateSize
import DenseSetsWithoutLargeSumsets.SimpleBoundForVeryLargeSumsets
import DenseSetsWithoutLargeSumsets.Probability
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
The construction of dense subsets without large sumsets.

The three preceding files estimate disjoint ranges of `#(A+B)`.  This file contains
the bookkeeping which combines them into the final probability estimate.
-/

namespace DenseSetsWithoutLargeSumsets

open MeasureTheory
open Filter
open scoped Pointwise

noncomputable section

private def smallSumsetEvent (n k : ℕ) (C : ℝ) : Set (Finset ℕ) :=
  {S | pairSumsetIsSubset n k 0 (C * k) S}

private def mediumSumsetEvent (n k : ℕ) (C : ℝ) : Set (Finset ℕ) :=
  {S | moderateSumsetEvent n k C S}

private def largeSumsetEvent (n k : ℕ) : Set (Finset ℕ) :=
  {S | veryLargeSumsetEvent n k S}

lemma pairEvent_subset_three_ranges {n k : ℕ} {C : ℝ} :
    {S : Finset ℕ | exactPairEvent n k S} ⊆
      smallSumsetEvent n k C ∪ mediumSumsetEvent n k C ∪ largeSumsetEvent n k := by
  intro S hS
  rcases hS with ⟨A, B, hA, hB, hAcard, hBcard, hsum⟩
  by_cases hsmall : ((A + B).card : ℝ) ≤ C * (k : ℝ)
  · left
    left
    exact ⟨A, B, hA, hB, hAcard, hBcard, by positivity, hsmall, hsum⟩
  · by_cases hmid : (A + B).card < k * (k + 1) / 2
    · left
      right
      exact ⟨A, B, hA, hB, hAcard, hBcard, not_le.mp hsmall, hmid, hsum⟩
    · right
      refine ⟨A, B, hA, hB, hAcard, hBcard, ?_, hsum⟩
      simpa [Nat.mul_comm] using Nat.le_of_not_gt hmid

lemma pairEvent_measure_le_three_ranges
    {n k : ℕ} {δ : unitInterval} {C L M G : ℝ}
    (hlower : (binomialFinsetSubset (Set.Icc 1 n) δ).real (smallSumsetEvent n k C) ≤ L)
    (hmid : (binomialFinsetSubset (Set.Icc 1 n) δ).real (mediumSumsetEvent n k C) ≤ M)
    (hlarge : (binomialFinsetSubset (Set.Icc 1 n) δ).real (largeSumsetEvent n k) ≤ G) :
    (binomialFinsetSubset (Set.Icc 1 n) δ).real {S | exactPairEvent n k S} ≤ L + M + G := by
  apply (measureReal_mono (pairEvent_subset_three_ranges)).trans
  apply (measureReal_union_le (smallSumsetEvent n k C ∪ mediumSumsetEvent n k C)
    (largeSumsetEvent n k)).trans
  apply add_le_add ?_ hlarge
  exact (measureReal_union_le (smallSumsetEvent n k C) (mediumSumsetEvent n k C)).trans
    (add_le_add hlower hmid)

lemma pairEvent_measure_le_three_ranges_of_bounds
    {γ α c : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hc_pos : 0 < c)
    {n : ℕ} (hn_low : lowerGapThreshold (moderateSumsetGapConstant γ c) γ c < n)
    {δ : unitInterval} (hδ_lower : Real.rpow (n : ℝ) (-α) < (δ : ℝ))
    (hδ_upper : (δ : ℝ) ≤ 1 - c)
    (hα_lower : α ≤ lowerDensityExponent (moderateSumsetGapConstant γ c) γ)
    (hα_mid : α ≤ moderateSumsetDensityExponent γ c)
    (hn_two : 2 ≤ n)
    (hk_two : 2 ≤ pairCardThreshold (2 + γ) n δ)
    (hlarge_bound :
      (pairCardThreshold (2 + γ) n δ : ℝ) ^ 2 *
          (pairCardThreshold (2 + γ) n δ : ℝ) ^
            (8 * pairCardThreshold (2 + γ) n δ) /
          (n : ℝ) ^ (γ * (pairCardThreshold (2 + γ) n δ : ℝ) / 2) ≤
        (pairCardThreshold (2 + γ) n δ : ℝ) ^ 2 /
          (n : ℝ) ^ (γ * (pairCardThreshold (2 + γ) n δ : ℝ) / 3)) :
    (binomialFinsetSubset (Set.Icc 1 n) δ).real
        {S | pairEvent n (pairCardThreshold (2 + γ) n δ) S} ≤
      4 * (pairCardThreshold (2 + γ) n δ : ℝ) ^ 2 /
        Real.rpow (n : ℝ) (pairEventDecayExponent γ) := by
  let k := pairCardThreshold (2 + γ) n δ
  let C := moderateSumsetGapConstant γ c
  have hC_pos : 0 < C := by
    dsimp [C]
    dsimp [moderateSumsetGapConstant]
    positivity
  have hc_lt : c < 1 := by
    have : 0 < (δ : ℝ) := (Real.rpow_pos_of_pos (by positivity) (-α)).trans hδ_lower
    linarith
  have hγ_mid_pos : 0 < γ := hγ_pos
  have hγ_mid_le : γ ≤ 2 := hγ_le.trans (by norm_num)
  have hδ_lower_low : Real.rpow (n : ℝ) (-lowerDensityExponent C γ) < (δ : ℝ) := by
    refine lt_of_le_of_lt ?_ hδ_lower
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast (by omega : 1 ≤ n)
    · exact neg_le_neg hα_lower
  have hδ_lower_mid : Real.rpow (n : ℝ) (-moderateSumsetDensityExponent γ c) < (δ : ℝ) := by
    refine lt_of_le_of_lt ?_ hδ_lower
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast (by omega : 1 ≤ n)
    · exact neg_le_neg hα_mid
  have hlarge_subset : {S : Finset ℕ | pairEvent n k S} ⊆
      {S : Finset ℕ | exactPairEvent n k S} := by
    intro S hS
    rcases hS with ⟨A, B, hA, hB, hAk, hBk, hsum⟩
    rcases Finset.exists_subset_card_eq hAk with ⟨A', hA'sub, hA'card⟩
    rcases Finset.exists_subset_card_eq hBk with ⟨B', hB'sub, hB'card⟩
    exact ⟨A', B', hA'sub.trans hA, hB'sub.trans hB, hA'card, hB'card,
      (Finset.add_subset_add hA'sub hB'sub).trans hsum⟩
  apply (measureReal_mono hlarge_subset).trans
  refine (pairEvent_measure_le_three_ranges (C := C)
    (L := 2 * (k : ℝ) / Real.rpow (n : ℝ) (ε γ / 2))
    (M := 2 * (k : ℝ) ^ 2 / Real.rpow (n : ℝ) ((γ * C) / 2))
    (G := (k : ℝ) ^ 2 / Real.rpow (n : ℝ) (γ * (k : ℝ) / 3))
    ?_ ?_ ?_).trans ?_
  · change (binomialFinsetSubset (Set.Icc 1 n) δ).real
        (pairSumsetIsSubset n k 0 (C * (k : ℝ))) ≤ _
    simpa [smallSumsetEvent, k, smallSumsetMeasure] using
      small_sumset_pair_probability_le (γ := γ) (C := C) (c := c)
        hγ_pos hγ_le hC_pos hc_pos hn_low hδ_lower_low hδ_upper
  · change (binomialFinsetSubset (Set.Icc 1 n) δ).real
        {S : Finset ℕ | moderateSumsetEvent n k C S} ≤ _
    simpa [k, C] using
      moderate_sumset_probability_le hγ_mid_pos hγ_mid_le hc_pos (by omega)
        hδ_lower_mid hδ_upper
  · change (binomialFinsetSubset (Set.Icc 1 n) δ).real
        {S : Finset ℕ | veryLargeSumsetEvent n k S} ≤ _
    have hnew := bipartite_very_large_sumset_probability_le hγ_pos (by omega : 1 < n)
      ((Real.rpow_pos_of_pos (by positivity) (-α)).trans hδ_lower)
      (lt_of_le_of_lt hδ_upper (by linarith [hc_pos] : 1 - c < 1))
    have hnew' : (binomialFinsetSubset (Set.Icc 1 n) δ).real
        {S : Finset ℕ | veryLargeSumsetEvent n k S} ≤
          (k : ℝ) ^ 2 * (k : ℝ) ^ (8 * k) /
            (n : ℝ) ^ (γ * (k : ℝ) / 2) := by
      simpa [largeSumsetEvent, k] using hnew
    exact hnew'.trans hlarge_bound
  have hn_one : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hk_two : (2 : ℝ) ≤ k := by exact_mod_cast hk_two
  apply le_trans (b :=
    (k : ℝ) ^ 2 / Real.rpow n (pairEventDecayExponent γ) +
      2 * (k : ℝ) ^ 2 / Real.rpow n (pairEventDecayExponent γ) +
      (k : ℝ) ^ 2 / Real.rpow n (pairEventDecayExponent γ))
  · apply add_le_add
    · apply add_le_add
      · apply le_trans (b :=
          2 * (k : ℝ) / Real.rpow n (pairEventDecayExponent γ))
        · apply div_le_div_of_nonneg_left (by positivity)
            (Real.rpow_pos_of_pos (by positivity : 0 < (n : ℝ)) _)
          apply Real.rpow_le_rpow_of_exponent_le hn_one
          dsimp [pairEventDecayExponent, ε]
          field_simp
          nlinarith
        · apply div_le_div_of_nonneg_right
          · nlinarith [hk_two]
          · exact (Real.rpow_pos_of_pos (by positivity : 0 < (n : ℝ)) _).le
      · apply div_le_div_of_nonneg_left (by positivity)
          (Real.rpow_pos_of_pos (by positivity : 0 < (n : ℝ)) _)
        apply Real.rpow_le_rpow_of_exponent_le hn_one
        have hC_one : (1 : ℝ) ≤ C := by
          dsimp [C, moderateSumsetGapConstant]
          conv_lhs => rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (div_nonneg (mul_nonneg (by norm_num)
            (densityCoefficient_pos (by linarith) hc_pos hc_lt).le) (by linarith))
        dsimp [pairEventDecayExponent]
        rw [div_le_iff₀ (by positivity : 0 < 8 * (γ + 3))]
        have hprod : (3 : ℝ) ≤ C * (γ + 3) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hC_one) (by linarith : 0 ≤ γ + 3)]
        have hscale : (1 : ℝ) ≤ 4 * C * (γ + 3) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hscale hγ_pos.le]
    · apply div_le_div_of_nonneg_left (by positivity)
        (Real.rpow_pos_of_pos (by positivity : 0 < (n : ℝ)) _)
      apply Real.rpow_le_rpow_of_exponent_le hn_one
      dsimp [pairEventDecayExponent]
      field_simp
      nlinarith [le_trans (by norm_num : (1 : ℝ) ≤ 2) hk_two]
  apply le_of_eq
  ring

lemma eventually_pairEvent_bound_lt {γ α c ε : ℝ}
    (hγ_pos : 0 < γ) (_hγ_le : γ ≤ 1) (hc_pos : 0 < c) (hc_lt : c < 1)
    (hε_pos : 0 < ε) :
    ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ),
      ∀ δ : unitInterval,
        Real.rpow (n : ℝ) (-α) < (δ : ℝ) → (δ : ℝ) ≤ 1 - c →
          4 * (pairCardThreshold (2 + γ) n δ : ℝ) ^ 2 /
              Real.rpow (n : ℝ) (pairEventDecayExponent γ) < ε := by
  let q := densityCoefficient (2 + γ) c
  have hq_pos : 0 < q := by
    dsimp [q, densityCoefficient]
    have hlogc : 0 < Real.log (1 / (1 - c)) := by
      apply Real.log_pos
      rw [one_lt_div] <;> linarith
    positivity
  have heps_pos : 0 < pairEventDecayExponent γ := by
    dsimp [pairEventDecayExponent]
    positivity
  have htail : Filter.Tendsto
      (fun x : ℝ => Real.rpow (Real.log x) 2 /
        Real.rpow x (pairEventDecayExponent γ)) atTop (nhds 0) := by
    exact (isLittleO_log_rpow_rpow_atTop (2 : ℝ) heps_pos).tendsto_div_nhds_zero
  have htail_nat : Filter.Tendsto
      (fun n : ℕ => Real.rpow (Real.log (n : ℝ)) 2 /
        Real.rpow (n : ℝ) (pairEventDecayExponent γ)) atTop (nhds 0) :=
    htail.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ),
      Real.rpow (Real.log (n : ℝ)) 2 /
        Real.rpow (n : ℝ) (pairEventDecayExponent γ) < ε / (4 * q ^ 2) := by
    exact htail_nat.eventually_lt_const
      (div_pos hε_pos (by positivity))
  have hlog : ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ),
      (1 : ℝ) ≤ Real.log (n : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hn_two : ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ), 2 ≤ n :=
    Filter.eventually_ge_atTop 2
  filter_upwards [hsmall, hlog, hn_two] with n hsmall hlog hn_two
  intro δ hδ_lower hδ_upper
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hk_upper := pairCardThreshold_le_densityCoefficient_mul_log (τ := 2 + γ)
    (by linarith) hc_pos hn_two
    ((Real.rpow_pos_of_pos hn_pos (-α)).trans hδ_lower) hδ_upper
  have hsq : (pairCardThreshold (2 + γ) n δ : ℝ) ^ 2 ≤
      (q * Real.log (n : ℝ)) ^ 2 := by
    have : 0 ≤ (pairCardThreshold (2 + γ) n δ : ℝ) := by positivity
    have hkq : (pairCardThreshold (2 + γ) n δ : ℝ) ≤ q * Real.log (n : ℝ) := by
      simpa [q] using hk_upper
    nlinarith [hkq, mul_nonneg hq_pos.le (zero_le_one.trans hlog),
      sq_nonneg ((pairCardThreshold (2 + γ) n δ : ℝ) - q * Real.log (n : ℝ))]
  have hden_pos : 0 < Real.rpow (n : ℝ) (pairEventDecayExponent γ) :=
    Real.rpow_pos_of_pos hn_pos _
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq (by norm_num)) hden_pos.le).trans_lt
  have hlogpow : Real.rpow (Real.log (n : ℝ)) 2 = (Real.log (n : ℝ)) ^ 2 :=
    Real.rpow_two _
  rw [hlogpow] at hsmall
  refine (le_of_eq ?_).trans_lt
    ((mul_lt_mul_of_pos_left hsmall
      (by positivity : (0 : ℝ) < 4 * q ^ 2)).trans_eq ?_)
  · ring
  · field_simp

lemma eventually_pairEvent_bound_lt_quarter {γ α c : ℝ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hc_pos : 0 < c) (hc_lt : c < 1) :
    ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ),
      ∀ δ : unitInterval,
        Real.rpow (n : ℝ) (-α) < (δ : ℝ) → (δ : ℝ) ≤ 1 - c →
          4 * (pairCardThreshold (2 + γ) n δ : ℝ) ^ 2 /
              Real.rpow (n : ℝ) (pairEventDecayExponent γ) < 1 / 4 := by
  exact eventually_pairEvent_bound_lt hγ_pos hγ_le hc_pos hc_lt (by norm_num)

lemma exists_dense_set_of_pair_probability_lt_quarter
    {n k : ℕ} {δ : unitInterval}
    (hmean : (3 : ℝ) ≤ (δ : ℝ) * (n : ℝ))
    (hprob : (binomialFinsetSubset (Set.Icc 1 n) δ).real
      {S | pairEvent n k S} < 1 / 4) :
    existsDenseSetWithoutLargeSumsets n k δ := by
  by_contra h
  refine (not_lt_of_ge ((binomialFinsetSubset_real_dense_event_ge_quarter n δ hmean).trans
    (measureReal_mono ?_))) hprob
  intro S hS
  by_contra hpair
  apply h
  exact ⟨S, hS.1, hS.2, hpair⟩

/-- The exponent used in the density range of Theorem `thm:main`. -/
def denseSubsetDensityExponent (γ c : ℝ) : ℝ :=
  min (1 / 2)
    (min (lowerDensityExponent (moderateSumsetGapConstant γ c) γ)
      (moderateSumsetDensityExponent γ c))

lemma denseSubsetDensityExponent_pos {γ c : ℝ} (hγ_pos : 0 < γ) (hc_pos : 0 < c)
    (hc_lt : c < 1) :
    0 < denseSubsetDensityExponent γ c := by
  refine lt_min (by norm_num) (lt_min ?_ (moderateSumsetDensityExponent_pos (by linarith)))
  exact lowerDensityExponent_pos_of_one_le hγ_pos
    (one_le_moderateSumsetGapConstant (by linarith) hc_pos hc_lt)

/- Formal statement of the final combination proving `stmt:randomMain`.

The remaining threshold selection is isolated in `eventuallyForDensities`; the finite
union-bound argument above is the part supplied by the three sumset-size ranges.
-/
theorem eventually_pairEvent_probability_le
    {γ c : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hc_pos : 0 < c) (hc_lt : c < 1) :
    eventuallyForDensities (denseSubsetDensityExponent γ c) c fun n δ =>
      let ℙ : Measure (Finset ℕ) := binomialFinsetSubset (Set.Icc 1 n) δ
      ℙ.real (pairEvent n (pairCardThreshold (2 + γ) n δ)) ≤
        4 * (pairCardThreshold (2 + γ) n δ : ℝ) ^ 2 /
          Real.rpow (n : ℝ) (pairEventDecayExponent γ) := by
  let C := moderateSumsetGapConstant γ c
  rw [eventuallyForDensities]
  filter_upwards [Filter.eventually_ge_atTop
      (max 2 (max (Nat.ceil (lowerGapThreshold C γ c))
        (bipartiteVeryLargeSumsetStrictThreshold γ c)) + 1)]
        with n hnN
  intro δ hδ_lower hδ_upper
  refine pairEvent_measure_le_three_ranges_of_bounds hγ_pos hγ_le hc_pos
    ?_ hδ_lower hδ_upper ?_ ?_ ?_ ?_ ?_
  · refine lt_of_le_of_lt (Nat.le_ceil _) ?_
    exact_mod_cast le_trans
      (Nat.add_le_add_right ((le_max_left _ _).trans (le_max_right _ _)) 1) hnN
  · dsimp [denseSubsetDensityExponent, C]
    exact (min_le_right _ _).trans (min_le_left _ _)
  · dsimp [denseSubsetDensityExponent, C]
    exact (min_le_right _ _).trans (min_le_right _ _)
  · omega
  · refine pairCardThreshold_ge_two_of_density_lower
      ?_ ?_ ?_ (by linarith) hδ_lower
    · linarith
    · dsimp [denseSubsetDensityExponent]
      nlinarith [min_le_left (1 / 2 : ℝ)
        (min (lowerDensityExponent (moderateSumsetGapConstant γ c) γ)
          (moderateSumsetDensityExponent γ c))]
    · omega
  · apply bipartite_very_large_sumset_factor_bound hγ_pos hγ_le hc_pos
    · exact lt_of_lt_of_le
        (Nat.lt_succ_of_le ((le_max_right _ _).trans (le_max_right _ _))) hnN
    · have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      exact (Real.rpow_pos_of_pos hn_pos
        (-denseSubsetDensityExponent γ c)).trans hδ_lower
    · exact hδ_upper

private theorem eventually_exists_dense_subset_without_large_sumsets_uniform
    {γ c : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hc_pos : 0 < c) (hc_lt : c < 1) :
    ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ),
      ∀ δ : unitInterval,
        Real.rpow (n : ℝ) (-denseSubsetDensityExponent γ c) < (δ : ℝ) →
        (δ : ℝ) ≤ 1 - c →
        ∃ S : Finset ℕ,
          S ⊆ Finset.Icc 1 n ∧
          (δ : ℝ) * (n : ℝ) ≤ (S.card : ℝ) ∧
          ¬ ∃ A B : Finset ℕ,
            A ⊆ Finset.Icc 1 n ∧
            B ⊆ Finset.Icc 1 n ∧
            Nat.ceil ((2 + γ) * Real.log (n : ℝ) / Real.log (1 / δ)) ≤ A.card ∧
            Nat.ceil ((2 + γ) * Real.log (n : ℝ) / Real.log (1 / δ)) ≤ B.card ∧
            A + B ⊆ S := by
  have hmain := eventually_pairEvent_probability_le hγ_pos hγ_le hc_pos hc_lt
  rw [eventuallyForDensities] at hmain
  filter_upwards [hmain,
    eventually_pairEvent_bound_lt_quarter (α := denseSubsetDensityExponent γ c)
      hγ_pos hγ_le hc_pos hc_lt,
    Filter.eventually_ge_atTop 9]
      with n hmain hquarter hn_nine
  intro δ hδ_lower hδ_upper
  have hn_pos : 0 < (n : ℝ) := by positivity
  change existsDenseSetWithoutLargeSumsets n (pairCardThreshold (2 + γ) n δ) δ
  apply exists_dense_set_of_pair_probability_lt_quarter
    (n := n) (k := pairCardThreshold (2 + γ) n δ)
  · refine le_trans ?_ (mul_lt_mul_of_pos_right hδ_lower hn_pos).le
    refine le_trans (b := Real.rpow (n : ℝ)
      (-denseSubsetDensityExponent γ c + 1)) ?_
      (Real.rpow_add_one hn_pos.ne' (-denseSubsetDensityExponent γ c)).le
    apply le_trans (b := Real.rpow (n : ℝ) (1 / 2))
    · have hsqrt : (3 : ℝ) ≤ Real.sqrt (n : ℝ) := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hn_nine)
      rw [Real.sqrt_eq_rpow] at hsqrt
      exact hsqrt
    · apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast (by omega : 1 ≤ n)
      · rw [denseSubsetDensityExponent]
        nlinarith [min_le_left (1 / 2 : ℝ)
          (min (lowerDensityExponent (moderateSumsetGapConstant γ c) γ)
            (moderateSumsetDensityExponent γ c))]
  · exact (hmain δ hδ_lower hδ_upper).trans_lt (hquarter δ hδ_lower hδ_upper)

/- Formal statement of the deduction of Theorem `thm:main`. -/
theorem dense_subset_without_large_sumsets
    {γ c : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hc_pos : 0 < c) (hc_lt : c < 1)
    (δ : ℕ → unitInterval)
    (hδ_lower : ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ),
      Real.rpow (n : ℝ) (-denseSubsetDensityExponent γ c) < (δ n : ℝ))
    (hδ_upper : ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ), (δ n : ℝ) ≤ 1 - c) :
    ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ),
      ∃ S : Finset ℕ,
        S ⊆ Finset.Icc 1 n ∧
        (δ n : ℝ) * (n : ℝ) ≤ (S.card : ℝ) ∧
        ¬ ∃ A B : Finset ℕ,
          A ⊆ Finset.Icc 1 n ∧
          B ⊆ Finset.Icc 1 n ∧
          Nat.ceil ((2 + γ) * Real.log (n : ℝ) / Real.log (1 / δ n)) ≤ A.card ∧
          Nat.ceil ((2 + γ) * Real.log (n : ℝ) / Real.log (1 / δ n)) ≤ B.card ∧
          A + B ⊆ S := by
  filter_upwards [eventually_exists_dense_subset_without_large_sumsets_uniform
    hγ_pos hγ_le hc_pos hc_lt,
    hδ_lower, hδ_upper] with n hmain hδ_lower hδ_upper
  exact hmain (δ n) hδ_lower hδ_upper

/-- Fixed-density form of the sharp result. Since `ε` is arbitrary, these thresholds have
leading constant `2 + o(1)`. -/
theorem fixed_density_dense_subset_without_large_sumsets
    {δ : unitInterval} (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_le : ε ≤ 1) :
    ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ),
      ∃ S : Finset ℕ,
        S ⊆ Finset.Icc 1 n ∧
        (δ : ℝ) * (n : ℝ) ≤ (S.card : ℝ) ∧
        ¬ ∃ A B : Finset ℕ,
          A ⊆ Finset.Icc 1 n ∧
          B ⊆ Finset.Icc 1 n ∧
          Nat.ceil ((2 + ε) * Real.log (n : ℝ) / Real.log (1 / δ)) ≤ A.card ∧
          Nat.ceil ((2 + ε) * Real.log (n : ℝ) / Real.log (1 / δ)) ≤ B.card ∧
          A + B ⊆ S := by
  let c : ℝ := (1 - (δ : ℝ)) / 2
  have hc_pos : 0 < c := by dsimp [c]; linarith
  have hc_lt : c < 1 := by dsimp [c]; linarith [δ.2.1]
  have hα_pos := denseSubsetDensityExponent_pos hε_pos hc_pos hc_lt
  have ht : Filter.Tendsto
      (fun n : ℕ => Real.rpow (n : ℝ) (-denseSubsetDensityExponent ε c))
      Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hα_pos).comp tendsto_natCast_atTop_atTop
  have hlower : ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ),
      Real.rpow (n : ℝ) (-denseSubsetDensityExponent ε c) < (δ : ℝ) :=
    ht.eventually_lt_const hδ_pos
  have hupper : ∀ᶠ _n : ℕ in (Filter.atTop : Filter ℕ), (δ : ℝ) ≤ 1 - c := by
    exact Filter.Eventually.of_forall fun _ => by
      dsimp [c]
      linarith [unitInterval.le_one δ]
  simpa using dense_subset_without_large_sumsets hε_pos hε_le hc_pos hc_lt
    (fun _ => δ) hlower hupper

end

end DenseSetsWithoutLargeSumsets
