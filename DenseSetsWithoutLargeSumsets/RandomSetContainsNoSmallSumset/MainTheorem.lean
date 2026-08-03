/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.EventSubset
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.FreimanDimension
import DenseSetsWithoutLargeSumsets.Probability
import DenseSetsWithoutLargeSumsets.Common
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.GeneralizedArithmeticProgression
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.LargeSumsetsFromMediumSizedSubsets.MediumSizedSubsets
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.Chang.Reduction
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.NumberTheory.Bertrand

/-!
The probability estimate for a pair with a small sumset.

Assembles the event-subset reduction, the union bound over witness pairs, and the exponent
bound into `small_sumset_pair_probability_le`, the probability estimate consumed by the rest of
the development.
-/

namespace DenseSetsWithoutLargeSumsets

open Nat hiding div_pos
open scoped Pointwise

noncomputable section

abbrev smallSumsetMeasure (n : ℕ) (δ : unitInterval) :
    MeasureTheory.Measure (Finset ℕ) :=
  binomialFinsetSubset (Set.Icc 1 n) δ

theorem small_sumset_pair_probability_le_fingerprint_sum {γ C c : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (C_pos : 0 < C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c) :
    (smallSumsetMeasure n δ).real
        (pairSumsetIsSubset n (pairCardThreshold (3 + γ) n δ) 0
          (C * pairCardThreshold (3 + γ) n δ)) ≤
      ∑ P ∈ lowerModelGAPs (γ := γ) (C := C) (n := n) δ hγ_pos C_pos hn,
        ∑ p ∈ bltDimSmallWitnessPairs
            (zmodGAPPreimageContainer n
              (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) P)
            P.dim (pairCardThreshold (3 + γ) n δ) C γ,
          (δ : ℝ) ^ (p.1 + p.2).card := by
  classical
  apply le_trans (b := (smallSumsetMeasure n δ).real
      (⋃ P ∈ lowerModelGAPs (γ := γ) (C := C) (n := n) δ hγ_pos C_pos hn,
        ⋃ p ∈ bltDimSmallWitnessPairs
            (zmodGAPPreimageContainer n
              (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) P)
            P.dim (pairCardThreshold (3 + γ) n δ) C γ,
          {S : Finset ℕ | bltWitnessPairSumsetIsSubset p S}))
  · change (smallSumsetMeasure n δ).real
      {S : Finset ℕ |
        pairSumsetIsSubset n (pairCardThreshold (3 + γ) n δ) 0
          (C * pairCardThreshold (3 + γ) n δ) S} ≤ _
    rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def]
    exact ENNReal.toReal_mono (MeasureTheory.measure_ne_top (smallSumsetMeasure n δ) _)
      (MeasureTheory.measure_mono (by
        simpa using
          pairSumsetIsSubset_event_subset_zmodGAPPreimageDimSmallWitnessPairs
            (γ := γ) (C := C) (c := c) (n := n) (δ := δ)
            hγ_pos hγ_le C_pos hc_pos hc_lt hn hn_gap hδ_lower hδ_upper hδ_upper_c))
  apply (MeasureTheory.measureReal_biUnion_finset_le
    (lowerModelGAPs (γ := γ) (C := C) (n := n) δ hγ_pos C_pos hn)
    (fun P =>
      ⋃ p ∈ bltDimSmallWitnessPairs
          (zmodGAPPreimageContainer n
            (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) P)
          P.dim (pairCardThreshold (3 + γ) n δ) C γ,
        {S : Finset ℕ | bltWitnessPairSumsetIsSubset p S})).trans
  apply Finset.sum_le_sum
  intro P _hP
  apply (MeasureTheory.measureReal_biUnion_finset_le
    (bltDimSmallWitnessPairs
      (zmodGAPPreimageContainer n
        (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) P)
      P.dim (pairCardThreshold (3 + γ) n δ) C γ)
    (fun p => {S : Finset ℕ | bltWitnessPairSumsetIsSubset p S})).trans
  apply Finset.sum_le_sum
  intro p _hp
  simpa [smallSumsetMeasure] using bltWitnessPair_probability_le n (δ := δ) p

private lemma lower_dim_fingerprint_sum_bound {γ C c : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (C_pos : 0 < C) (hC_one : 1 ≤ C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c) :
      ∑ P ∈ lowerModelGAPs (γ := γ) (C := C) (n := n) δ hγ_pos C_pos hn,
        ∑ p ∈ bltDimSmallWitnessPairs
            (zmodGAPPreimageContainer n
              (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) P)
            P.dim (pairCardThreshold (3 + γ) n δ) C γ,
          (δ : ℝ) ^ (p.1 + p.2).card ≤
      2 * (pairCardThreshold (3 + γ) n δ : ℝ) / (n : ℝ) ^ (ε γ / 2) := by
  classical
  have hC_two : 0 < 2 * C := by positivity
  have hε : 0 < ε γ := ε_pos hγ_pos
  have hδ_pos : 0 < (δ : ℝ) := unitInterval_pos_of_density_lower hn hδ_lower
  have hδ_lt : (δ : ℝ) < 1 := unitInterval_lt_one hδ_upper
  have hkpos : 0 < pairCardThreshold (3 + γ) n δ :=
    pairCardThreshold_pos_of_lower_density hγ_pos hn hδ_lower hδ_upper
  apply le_trans (b :=
    ∑ d ∈ Finset.Icc 1 (pairCardThreshold (3 + γ) n δ),
      ((properGAPsZModOfDim d
        ⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊
        (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).pos).card : ℝ) *
          ((((⌈lowerBltConstant C γ hC_two hε *
                Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ + 1) *
              (⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ + 1) ^
                ⌈lowerBltConstant C γ hC_two hε *
                  Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ : ℕ) : ℝ) *
            (((⌈lowerBltConstant C γ hC_two hε *
                Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ + 1) *
              (⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ + 1) ^
                ⌈lowerBltConstant C γ hC_two hε *
                  Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ : ℕ) : ℝ)) *
          Real.exp (-((1 - 3 * ε γ) * (d : ℝ) *
            (pairCardThreshold (3 + γ) n δ : ℝ)) * Real.log (1 / δ)))
  · simpa [lowerModelGAPs] using
      dim_fingerprint_sum_le_gap_dim_sum
        (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn)
        (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).pos
        (zmodModelEmbedding_iso (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).bijOn.injOn
        hC_two hε hδ_pos hδ_lt
  apply le_trans (b := ∑ d ∈ Finset.Icc 1 (pairCardThreshold (3 + γ) n δ),
    (n : ℝ) ^ (-(ε γ / 2)))
  · refine Finset.sum_le_sum ?_
    intro d hd
    exact lower_gap_dim_summand_le hγ_pos hγ_le C_pos hC_one hc_pos hc_lt hn hn_gap
      hδ_lower hδ_upper hδ_upper_c hC_two hε hd
  · rw [Finset.sum_const, nsmul_eq_mul]
    have hcoef : ((Finset.Icc 1 (pairCardThreshold (3 + γ) n δ)).card : ℝ) ≤
        2 * (pairCardThreshold (3 + γ) n δ : ℝ) := by
      have hcard : ((Finset.Icc 1 (pairCardThreshold (3 + γ) n δ)).card : ℝ) ≤
          (pairCardThreshold (3 + γ) n δ : ℝ) := by
        rw [Nat.card_Icc]
        exact_mod_cast (Nat.succ_sub_one
          (pairCardThreshold (3 + γ) n δ)).le
      nlinarith [hcard, ((by exact_mod_cast hkpos) :
        (0 : ℝ) < pairCardThreshold (3 + γ) n δ)]
    apply (mul_le_mul_of_nonneg_right hcoef (by positivity)).trans
    rw [Real.rpow_neg (le_of_lt (old_model_threshold_nat_pos hn))]
    ring_nf
    exact le_rfl

/-- Probability estimate for pairs with a small sumset. -/
theorem small_sumset_pair_probability_le {γ C c : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (C_pos : 0 < C) (hc_pos : 0 < c)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ))
    (hδ_upper : (δ : ℝ) ≤ 1 - c) :
    (smallSumsetMeasure n δ).real
        (pairSumsetIsSubset n (pairCardThreshold (3 + γ) n δ) 0
          (C * pairCardThreshold (3 + γ) n δ)) ≤
      2 * (pairCardThreshold (3 + γ) n δ : ℝ) / (n : ℝ) ^ (ε γ / 2) := by
  have hn : lowerSizeThreshold C γ < n := (lowerSizeThreshold_le_lowerGapThreshold C γ
    c).trans_lt hn_gap
  have hδ_pos : 0 < (δ : ℝ) := unitInterval_pos_of_density_lower hn hδ_lower
  have hc_lt : c < 1 := by linarith
  have hδ_lt : (δ : ℝ) < 1 := by linarith
  by_cases hC_one : 1 ≤ C
  · exact (small_sumset_pair_probability_le_fingerprint_sum
      hγ_pos hγ_le C_pos hc_pos hc_lt
      hn hn_gap hδ_lower hδ_lt hδ_upper).trans
      (lower_dim_fingerprint_sum_bound hγ_pos hγ_le C_pos hC_one hc_pos hc_lt hn hn_gap
        hδ_lower hδ_lt hδ_upper)
  · change (smallSumsetMeasure n δ).real
        {S : Finset ℕ |
          pairSumsetIsSubset n (pairCardThreshold (3 + γ) n δ) 0
            (C * pairCardThreshold (3 + γ) n δ) S} ≤
        2 * (pairCardThreshold (3 + γ) n δ : ℝ) / (n : ℝ) ^ (ε γ / 2)
    rw [(Set.eq_empty_iff_forall_notMem (s := {S : Finset ℕ |
        pairSumsetIsSubset n (pairCardThreshold (3 + γ) n δ) 0
          (C * pairCardThreshold (3 + γ) n δ) S})).mpr (by
      intro S hS
      rcases hS with ⟨A, B, _hAint, _hBint, hAcard, hBcard, _hAB_lower, hAB, _hAB_subset⟩
      exact hC_one
        (one_le_sumset_card_coefficient_of_threshold_pair_sumset hγ_pos hn hδ_lower hδ_lt hAcard
          hBcard
          hAB))]
    rw [MeasureTheory.measureReal_def]
    simp only [MeasureTheory.measure_empty, ENNReal.toReal_zero]
    positivity

end

end DenseSetsWithoutLargeSumsets
