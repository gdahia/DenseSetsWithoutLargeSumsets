/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.WitnessPairs
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.FreimanDimension
import DenseSetsWithoutLargeSumsets.Probability
import DenseSetsWithoutLargeSumsets.Common
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.GeneralizedArithmeticProgression
import DenseSetsWithoutLargeSumsets.LargeSumsetsFromMediumSizedSubsets.MediumSizedSubsets
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.Chang.Reduction
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.NumberTheory.Bertrand

/-!
Probability bounds for individual BLT witness pairs.

Bounds the probability that a fixed BLT witness pair has its sumset contained in the random
set, and packages the union bound over a finite family of pairs
(`bltDimSmallWitnessPairs_probability_sum_le`, `dim_fingerprint_sum_le_gap_dim_sum`).
-/

namespace DenseSetsWithoutLargeSumsets

open Nat hiding div_pos
open scoped Pointwise

noncomputable section

private lemma intToNat_injOn_of_subset_natCastImage {T : Finset ℤ} {S : Finset ℕ}
    (hT : T ⊆ natCastImage S) :
    Set.InjOn Int.toNat (T : Set ℤ) := by
  intro z hz w hw hzw
  rw [natCastImage] at hT
  rcases Finset.mem_image.mp (hT hz) with ⟨a, _ha, haz⟩
  rcases Finset.mem_image.mp (hT hw) with ⟨b, _hb, hbw⟩
  rw [← haz, ← hbw] at hzw ⊢
  simpa using hzw

private lemma bltWitnessPairSumsetIsSubset_subset_natSuperset
    (p : Finset ℤ × Finset ℤ) :
    {S : Finset ℕ | bltWitnessPairSumsetIsSubset p S} ⊆
      {S : Finset ℕ | (p.1 + p.2).image Int.toNat ⊆ S} := by
  intro S hS x hx
  rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
  change p.1 + p.2 ⊆ natCastImage S at hS
  rw [natCastImage] at hS
  rcases Finset.mem_image.mp (hS hz) with ⟨s, hs, hsz⟩
  rw [← hsz]
  simpa using hs

lemma bltWitnessPair_probability_le (n : ℕ) {δ : unitInterval}
    (p : Finset ℤ × Finset ℤ) :
    (binomialFinsetSubset (Set.Icc 1 n) δ).real
        {S : Finset ℕ | bltWitnessPairSumsetIsSubset p S} ≤
      (δ : ℝ) ^ (p.1 + p.2).card := by
  classical
  by_cases hnonempty : ∃ S : Finset ℕ, bltWitnessPairSumsetIsSubset p S
  · rcases hnonempty with ⟨S₀, hS₀⟩
    refine le_trans (b := (binomialFinsetSubset (Set.Icc 1 n) δ).real
      {S : Finset ℕ | (p.1 + p.2).image Int.toNat ⊆ S}) ?_ ?_
    · rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def]
      apply ENNReal.toReal_mono
      · exact MeasureTheory.measure_ne_top (binomialFinsetSubset (Set.Icc 1 n) δ) _
      · apply MeasureTheory.measure_mono
        simpa using bltWitnessPairSumsetIsSubset_subset_natSuperset p
    · refine (binomialFinsetSubset_real_superset_nat
        (Ω := Set.Icc 1 n) (p := δ) (Set.finite_Icc 1 n)
        (T := (p.1 + p.2).image Int.toNat)).trans_eq ?_
      rw [Finset.card_image_of_injOn (intToNat_injOn_of_subset_natCastImage hS₀)]
  · refine le_trans (b := 0) ?_ (pow_nonneg (unitInterval.nonneg δ) _)
    apply le_of_eq
    rw [MeasureTheory.measureReal_def]
    rw [ENNReal.toReal_eq_zero_iff]
    left
    rw [MeasureTheory.measure_eq_zero_iff_ae_notMem]
    filter_upwards with S hS
    exact hnonempty ⟨S, hS⟩

private lemma unitInterval_pow_le_exp_neg_mul_log_inv {δ : unitInterval} {m : ℕ} {L : ℝ}
    (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) (hL : L ≤ (m : ℝ)) :
    (δ : ℝ) ^ m ≤ Real.exp (-L * Real.log (1 / δ)) := by
  rw [← Real.exp_log (pow_pos hδ_pos m), Real.log_pow, mul_comm]
  refine (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hL ?_)).trans_eq ?_
  · rw [← Real.log_one]
    exact Real.log_le_log hδ_pos hδ_lt.le
  · rw [Real.log_div one_ne_zero (Ne.symm (ne_of_lt hδ_pos)), Real.log_one, zero_sub]
    ring_nf

private lemma bltDimSmallWitnessPairs_probability_sum_le (P : Finset ℕ) (D k : ℕ)
    (C γ : ℝ) {δ : unitInterval} (hC : 0 < 2 * C) (hε : 0 < ε γ)
    (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) :
    ∑ p ∈ bltDimSmallWitnessPairs P D k C γ, (δ : ℝ) ^ (p.1 + p.2).card ≤
      (((⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1) *
          ((natCastImage P).card + 1) ^
            ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ : ℝ) *
        ((⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1) *
          ((natCastImage P).card + 1) ^
            ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ : ℝ)) *
        Real.exp (-((1 - 3 * ε γ) * (D : ℝ) * (k : ℝ)) * Real.log (1 / δ)) := by
  classical
  refine (Finset.sum_le_sum (s := bltDimSmallWitnessPairs P D k C γ)
    (f := fun p => (δ : ℝ) ^ (p.1 + p.2).card)
    (g := fun _ => Real.exp (-((1 - 3 * ε γ) * (D : ℝ) * (k : ℝ)) *
      Real.log (1 / δ))) ?_).trans ?_
  · intro p hp
    rw [bltDimSmallWitnessPairs, Finset.mem_filter] at hp
    exact unitInterval_pow_le_exp_neg_mul_log_inv hδ_pos hδ_lt hp.2.2
  · rw [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast bltDimSmallWitnessPairs_card_le P D k C γ hC hε
    · positivity

private lemma sum_union_le_sum_add_sum {α : Type*} [DecidableEq α] (A B : Finset α)
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ A ∪ B, f x ≤ ∑ x ∈ A, f x + ∑ x ∈ B, f x := by
  classical
  refine le_trans (b := ∑ x ∈ A ∪ (B \ A), f x) ?_ ?_
  · apply le_of_eq
    congr 1
    ext x
    by_cases hxA : x ∈ A <;> simp [hxA]
  · rw [Finset.sum_union]
    · apply add_le_add_right
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        exact (Finset.mem_sdiff.mp hx).1
      · intro x _hxB _hxsdiff
        exact hf x
    · rw [Finset.disjoint_iff_inter_eq_empty]
      ext x
      simp

private lemma sum_biUnion_le_sum {α β : Type*} [DecidableEq β] (s : Finset α)
    (t : α → Finset β) (f : β → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ a ∈ s, ∑ x ∈ t a, f x := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    rw [Finset.biUnion_insert]
    refine (sum_union_le_sum_add_sum (t a) (s.biUnion t) f hf).trans ?_
    refine (add_le_add_right ih _).trans_eq ?_
    rw [Finset.sum_insert ha]

lemma dim_fingerprint_sum_le_gap_dim_sum {q n k s : ℕ} (ψ : ℕ → ZMod q)
    (hqpos : 0 < q) (hψinj : Set.InjOn ψ (interval n : Set ℕ))
    {C γ : ℝ} {δ : unitInterval} (hC : 0 < 2 * C) (hε : 0 < ε γ)
    (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) :
    ∑ P ∈ (by
        classical
        exact (Finset.Icc 1 k).biUnion (fun d => properGAPsZModOfDim d s hqpos) :
        Finset (ProperGAP (ZMod q))),
        ∑ p ∈ bltDimSmallWitnessPairs (zmodGAPPreimageContainer n ψ P) P.dim k C γ,
          (δ : ℝ) ^ (p.1 + p.2).card ≤
      ∑ d ∈ Finset.Icc 1 k,
        ((properGAPsZModOfDim d s hqpos).card : ℝ) *
          (((⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1) *
              (s + 1) ^
                ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ : ℝ) *
            ((⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1) *
              (s + 1) ^
                ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ : ℝ)) *
          Real.exp (-((1 - 3 * ε γ) * (d : ℝ) * (k : ℝ)) * Real.log (1 / δ)) := by
  classical
  refine (sum_biUnion_le_sum (Finset.Icc 1 k)
    (fun d => properGAPsZModOfDim d s hqpos)
    (fun P => ∑ p ∈ bltDimSmallWitnessPairs
      (zmodGAPPreimageContainer n ψ P) P.dim k C γ,
        (δ : ℝ) ^ (p.1 + p.2).card)
    ?_).trans ?_
  · intro P
    apply Finset.sum_nonneg'
    intro p
    exact pow_nonneg (unitInterval.nonneg δ) (p.1 + p.2).card
  refine Finset.sum_le_sum ?_
  intro d _hd
  refine (Finset.sum_le_sum (s := properGAPsZModOfDim d s hqpos)
    (f := fun P => ∑ p ∈ bltDimSmallWitnessPairs
      (zmodGAPPreimageContainer n ψ P) P.dim k C γ,
        (δ : ℝ) ^ (p.1 + p.2).card)
    (g := fun _ =>
      (((⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1) *
          (s + 1) ^
            ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ : ℝ) *
        ((⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1) *
          (s + 1) ^
            ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ : ℝ)) *
        Real.exp (-((1 - 3 * ε γ) * (d : ℝ) * (k : ℝ)) * Real.log (1 / δ))) ?_).trans_eq ?_
  · intro P hP
    refine (bltDimSmallWitnessPairs_probability_sum_le
      (zmodGAPPreimageContainer n ψ P) P.dim k C γ hC hε hδ_pos hδ_lt).trans ?_
    rw [((mem_properGAPsZModOfDim hqpos).1 hP).1]
    have hbase :
        (natCastImage (zmodGAPPreimageContainer n ψ P)).card + 1 ≤ s + 1 := by
      rw [natCastImage_card]
      exact Nat.succ_le_succ
        ((zmodGAPPreimageContainer_card_le_carrier P hψinj).trans
          ((mem_properGAPsZModOfDim hqpos).1 hP).2)
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast Nat.mul_le_mul
        (Nat.mul_le_mul_left
          (⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1)
          (Nat.pow_le_pow_left hbase
            ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊))
        (Nat.mul_le_mul_left
          (⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1)
          (Nat.pow_le_pow_left hbase
            ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊))
    · positivity
  · rw [Finset.sum_const, nsmul_eq_mul]
    ring


end

end DenseSetsWithoutLargeSumsets
