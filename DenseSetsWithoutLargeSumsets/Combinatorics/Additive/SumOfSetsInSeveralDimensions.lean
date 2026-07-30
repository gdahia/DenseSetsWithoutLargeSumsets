/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.Tactic.SetNotationForOrder
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.FreimanDimension

/-!
# Sum of sets in several dimensions

This file proves the sharp lower bound from Imre Ruzsa's *Sum of sets in several
dimensions*.  The nonemptiness assumption is the positive-cardinality assumption in the paper.
-/

namespace DenseSetsWithoutLargeSumsets

open scoped Pointwise

noncomputable section

/-- The candidate lower bound for the cardinality of a sumset of affine dimension `d`. -/
private def sumsetCardLowerBound (d m n : ℕ) : ℕ :=
  n + (Finset.Icc 1 (m - 1)).sum fun t ↦ min d (n - t)

private lemma sumsetCardLowerBound_eq (d m n : ℕ) :
    sumsetCardLowerBound d m n = n + (Finset.Icc 1 (m - 1)).sum (fun t ↦ min d (n - t)) := by
  rfl

private lemma Icc_two_eq_image_add_one (m : ℕ) :
    Finset.Icc 2 m = (Finset.Icc 1 (m - 1)).image (· + 1) := by
  ext t
  simp only [Finset.mem_Icc, Finset.mem_image]
  constructor
  · intro ht
    refine ⟨t - 1, ?_, ?_⟩
    · omega
    · omega
  · rintro ⟨u, hu, rfl⟩
    omega

private lemma sum_Icc_two_eq_sum_Icc_one (f : ℕ → ℕ) (m : ℕ) :
    (Finset.Icc 2 m).sum f = (Finset.Icc 1 (m - 1)).sum (fun t ↦ f (t + 1)) := by
  rw [Icc_two_eq_image_add_one, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.add_right_cancel hab

private lemma add_min_sub_one (d n : ℕ) :
    n + min d (n - 1) = n - 1 + min (d + 1) n := by
  omega

private lemma sumsetCardLowerBound_step {d m n : ℕ} (hm : 2 ≤ m) :
    sumsetCardLowerBound d m n = sumsetCardLowerBound d (m - 1) (n - 1) + min (d + 1) n := by
  rw [sumsetCardLowerBound_eq, sumsetCardLowerBound_eq, ← Finset.insert_Icc_add_one_left_eq_Icc]
  · rw [Finset.sum_insert]
    · norm_num only [Nat.reduceAdd]
      rw [sum_Icc_two_eq_sum_Icc_one]
      rw [← Nat.add_assoc, add_min_sub_one]
      simp only [Nat.add_assoc]
      refine congrArg (fun k => n - 1 + k) ?_
      nth_rewrite 1 [add_comm (min (d + 1) n)]
      refine congrArg (fun k => k + min (d + 1) n) ?_
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      omega
    · simp
  · omega

private lemma sumsetCardLowerBound_le_large_deletion {d m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    sumsetCardLowerBound d m n ≤ n + sumsetCardLowerBound (d - 1) (m - 1) (n - 1) := by
  have hpred : Order.pred (m - 1) = m - 2 := by
    change Nat.pred (m - 1) = m - 2
    rw [Nat.pred_eq_sub_one]
    omega
  rw [sumsetCardLowerBound_eq, sumsetCardLowerBound_eq, ← Finset.insert_Icc_pred_right_eq_Icc]
  · rw [Finset.sum_insert]
    · rw [hpred]
      apply Nat.add_le_add
      · omega
      · refine le_trans (Nat.add_le_add (min_le_right d (n - (m - 1)))
          (Finset.sum_le_sum (g := fun t ↦ min (d - 1) (n - 1 - t) + 1)
            fun t ht ↦ ?_)) ?_
        · rw [Finset.mem_Icc] at ht
          omega
        · rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc]
          simp only [smul_eq_mul, mul_one]
          simp only [Nat.sub_sub, Nat.reduceAdd]
          omega
    · rw [Finset.mem_Icc]
      rw [hpred]
      omega
  · omega

private lemma sumsetCardLowerBound_mono_right (d m : ℕ) : Monotone (sumsetCardLowerBound d m) := by
  intro a b hab
  rw [sumsetCardLowerBound_eq, sumsetCardLowerBound_eq]
  apply Nat.add_le_add hab
  apply Finset.sum_le_sum
  intro t _
  apply min_le_min_left
  omega

private lemma sumsetCardLowerBound_le_small_deletion {d m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    sumsetCardLowerBound d m n ≤ n + sumsetCardLowerBound (d - 1) (m - 1) n := by
  apply le_trans (sumsetCardLowerBound_le_large_deletion hm hmn)
  apply Nat.add_le_add_left
  apply sumsetCardLowerBound_mono_right
  omega

private lemma sumsetCardLowerBound_le_strict_right_deletion {d m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    sumsetCardLowerBound d m n ≤ m + sumsetCardLowerBound (d - 1) m (n - 1) := by
  rw [sumsetCardLowerBound_eq, sumsetCardLowerBound_eq]
  refine le_trans (b := n + (Finset.Icc 1 (m - 1)).sum
    (fun t ↦ min (d - 1) (n - 1 - t) + 1)) ?_ ?_
  · apply Nat.add_le_add_left
    apply Finset.sum_le_sum
    intro t ht
    rw [Finset.mem_Icc] at ht
    omega
  · rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc]
    simp only [smul_eq_mul, mul_one]
    omega

private lemma sumsetCardLowerBound_le_equal_right_deletion {d m : ℕ} (hm : 2 ≤ m) :
    sumsetCardLowerBound d m m ≤ m + sumsetCardLowerBound (d - 1) (m - 1) m := by
  apply le_trans (sumsetCardLowerBound_le_large_deletion hm le_rfl)
  apply Nat.add_le_add_left
  apply sumsetCardLowerBound_mono_right
  omega

private lemma two_le_card_of_nonempty_ne_one {α : Type*} (S : Finset α)
    (hS : S.Nonempty) (hcard : S.card ≠ 1) : 2 ≤ S.card := by
  rw [← Finset.card_pos] at hS
  omega

private lemma card_erase_add_card_erase_lt {α β : Type*} [DecidableEq α] [DecidableEq β]
    {S : Finset α} {T : Finset β} {s : α} {t : β} {n : ℕ}
    (hs : s ∈ S) (ht : t ∈ T) (hn : S.card + T.card = n) :
    (S.erase s).card + (T.erase t).card < n := by
  rw [Finset.card_erase_of_mem hs, Finset.card_erase_of_mem ht, ← hn]
  suffices 0 < S.card ∧ 0 < T.card by omega
  exact ⟨Finset.card_pos.mpr ⟨s, hs⟩, Finset.card_pos.mpr ⟨t, ht⟩⟩

private lemma card_erase_add_card_lt {α β : Type*} [DecidableEq α]
    {S : Finset α} {T : Finset β} {s : α} {n : ℕ}
    (hs : s ∈ S) (hn : S.card + T.card = n) : (S.erase s).card + T.card < n := by
  rw [Finset.card_erase_of_mem hs, ← hn]
  suffices 0 < S.card by omega
  exact Finset.card_pos.mpr ⟨s, hs⟩

private lemma card_erase_le_card_erase {α β : Type*} [DecidableEq α] [DecidableEq β]
    {S : Finset α} {T : Finset β} {s : α} {t : β}
    (hs : s ∈ S) (ht : t ∈ T) (hst : S.card ≤ T.card) :
    (S.erase s).card ≤ (T.erase t).card := by
  rw [Finset.card_erase_of_mem hs, Finset.card_erase_of_mem ht]
  omega

private lemma card_erase_le_card {α β : Type*} [DecidableEq α]
    {S : Finset α} {T : Finset β} {s : α} (hs : s ∈ S) (hst : S.card ≤ T.card) :
    (S.erase s).card ≤ T.card := by
  rw [Finset.card_erase_of_mem hs]
  omega

private lemma card_le_card_erase {α β : Type*} [DecidableEq β]
    {S : Finset α} {T : Finset β} {t : β} (ht : t ∈ T) (hst : S.card < T.card) :
    S.card ≤ (T.erase t).card := by
  rw [Finset.card_erase_of_mem ht]
  omega

private lemma sumsetCardLowerBound_of_full_case {d m n p s : ℕ} (hm : 2 ≤ m)
    (hrec : sumsetCardLowerBound d (m - 1) (n - 1) ≤ p) (hcard : p + d + 1 ≤ s) :
    sumsetCardLowerBound d m n ≤ s := by
  rw [sumsetCardLowerBound_step hm]
  apply le_trans (Nat.add_le_add_right hrec _)
  apply le_trans (Nat.add_le_add_left (min_le_left (d + 1) n) _)
  omega

private lemma sumsetCardLowerBound_of_large_case {d m n p s : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hrec : sumsetCardLowerBound (d - 1) (m - 1) (n - 1) ≤ p) (hcard : n + p ≤ s) :
    sumsetCardLowerBound d m n ≤ s := by
  apply le_trans (sumsetCardLowerBound_le_large_deletion hm hmn)
  exact (Nat.add_le_add_left hrec n).trans hcard

private lemma sumsetCardLowerBound_of_small_case {d m n p s : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hrec : sumsetCardLowerBound (d - 1) (m - 1) n ≤ p) (hcard : n + p ≤ s) :
    sumsetCardLowerBound d m n ≤ s := by
  apply le_trans (sumsetCardLowerBound_le_small_deletion hm hmn)
  exact (Nat.add_le_add_left hrec n).trans hcard

private lemma sumsetCardLowerBound_of_equal_right_case {d m p s : ℕ} (hm : 2 ≤ m)
    (hrec : sumsetCardLowerBound (d - 1) (m - 1) m ≤ p) (hcard : m + p ≤ s) :
    sumsetCardLowerBound d m m ≤ s := by
  apply le_trans (sumsetCardLowerBound_le_equal_right_deletion hm)
  exact (Nat.add_le_add_left hrec m).trans hcard

private lemma sumsetCardLowerBound_of_strict_right_case {d m n p s : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    (hrec : sumsetCardLowerBound (d - 1) m (n - 1) ≤ p) (hcard : m + p ≤ s) :
    sumsetCardLowerBound d m n ≤ s := by
  apply le_trans (sumsetCardLowerBound_le_strict_right_deletion hm hmn)
  exact (Nat.add_le_add_left hrec m).trans hcard

section LexicographicMinimum

variable {D : ℕ}

private def lexMin (S : Finset (Fin D → ℝ)) (hS : S.Nonempty) : Fin D → ℝ :=
  by
    refine ofLex ((S.image toLex).min' ?_)
    simpa

private lemma lexMin_mem (S : Finset (Fin D → ℝ)) (hS : S.Nonempty) : lexMin S hS ∈ S := by
  rw [lexMin]
  obtain ⟨x, hx, hxmin⟩ := Finset.mem_image.mp (Finset.min'_mem (S.image toLex) _)
  rw [← hxmin, ofLex_toLex]
  exact hx

private lemma lexMin_le (S : Finset (Fin D → ℝ)) (hS : S.Nonempty) {x : Fin D → ℝ}
    (hx : x ∈ S) : toLex (lexMin S hS) ≤ toLex x := by
  rw [lexMin, toLex_ofLex]
  apply Finset.min'_le
  exact Finset.mem_image.2 ⟨x, hx, rfl⟩

private lemma lexMin_sub_pos (S : Finset (Fin D → ℝ)) (hS : S.Nonempty)
    {x : Fin D → ℝ} (hx : x ∈ S) (hne : x ≠ lexMin S hS) :
    0 < toLex (x - lexMin S hS) := by
  rw [toLex_sub, sub_pos]
  apply (lexMin_le S hS hx).lt_of_ne
  simpa using hne.symm

end LexicographicMinimum

private lemma right_base_difference_of_eq {D : ℕ} {x y z x₀ y₀ : Fin D → ℝ}
    (hy : y = 0) (hxy : x + y = z) : y₀ = (x - x₀) - (z - y₀) + x₀ := by
  rw [hy, add_zero] at hxy
  rw [← hxy]
  abel

private lemma left_base_difference_of_eq {D : ℕ} {x y z x₀ y₀ : Fin D → ℝ}
    (hxy : x + y = z) : x₀ = (z - y₀) - (y - y₀) - (x - x₀) := by
  rw [← hxy]
  abel

section Normalize

variable {D : ℕ}

private def normalize (S : Finset (Fin D → ℝ)) (hS : S.Nonempty) : Finset (Fin D → ℝ) :=
  S.image fun x ↦ x - lexMin S hS

private lemma normalize_card (S : Finset (Fin D → ℝ)) (hS : S.Nonempty) :
    (normalize S hS).card = S.card := by
  rw [normalize, Finset.card_image_of_injective]
  intro x y hxy
  exact sub_left_injective hxy

private lemma zero_mem_normalize (S : Finset (Fin D → ℝ)) (hS : S.Nonempty) :
    0 ∈ normalize S hS := by
  rw [normalize, Finset.mem_image]
  exact ⟨lexMin S hS, lexMin_mem S hS, sub_self _⟩

private lemma normalize_nonempty (S : Finset (Fin D → ℝ)) (hS : S.Nonempty) :
    (normalize S hS).Nonempty := ⟨0, zero_mem_normalize S hS⟩

private lemma normalize_pos_of_ne_zero (S : Finset (Fin D → ℝ)) (hS : S.Nonempty)
    {x : Fin D → ℝ} (hx : x ∈ normalize S hS) (hx0 : x ≠ 0) : 0 < toLex x := by
  rw [normalize, Finset.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  apply lexMin_sub_pos S hS hy
  intro hymin
  apply hx0
  rw [hymin, sub_self]

private lemma coe_image_sub (S : Finset (Fin D → ℝ)) (c : Fin D → ℝ) :
    ((S.image fun x ↦ x - c : Finset (Fin D → ℝ)) : Set (Fin D → ℝ)) =
      (-c) +ᵥ (S : Set (Fin D → ℝ)) := by
  ext x
  simp only [Finset.coe_image, Set.mem_image, Set.mem_vadd_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    simp [sub_eq_add_neg, add_comm]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    simp [sub_eq_add_neg, add_comm]

private lemma finsetAffineDim_image_sub (S : Finset (Fin D → ℝ)) (c : Fin D → ℝ) :
    finsetAffineDim (S.image fun x ↦ x - c) = finsetAffineDim S := by
  unfold finsetAffineDim
  rw [direction_affineSpan, direction_affineSpan]
  rw [coe_image_sub]
  rw [vectorSpan_vadd]

private lemma normalize_add (A B : Finset (Fin D → ℝ)) (hA : A.Nonempty) (hB : B.Nonempty) :
    normalize A hA + normalize B hB =
      (A + B).image fun x ↦ x - (lexMin A hA + lexMin B hB) := by
  ext x
  constructor
  · intro hx
    rw [Finset.mem_add] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    rw [normalize, Finset.mem_image] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    rw [Finset.mem_image]
    refine ⟨a' + b', Finset.add_mem_add ha' hb', ?_⟩
    abel
  · intro hx
    rw [Finset.mem_image] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [Finset.mem_add] at hz ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    refine ⟨a - lexMin A hA, ?_, b - lexMin B hB, ?_, ?_⟩
    · exact Finset.mem_image.2 ⟨a, ha, rfl⟩
    · exact Finset.mem_image.2 ⟨b, hb, rfl⟩
    · abel

private lemma normalize_add_card (A B : Finset (Fin D → ℝ)) (hA : A.Nonempty)
    (hB : B.Nonempty) : (normalize A hA + normalize B hB).card = (A + B).card := by
  rw [normalize_add, Finset.card_image_of_injective]
  intro x y hxy
  exact sub_left_injective hxy

private lemma normalize_add_dim (A B : Finset (Fin D → ℝ)) (hA : A.Nonempty)
    (hB : B.Nonempty) :
    finsetAffineDim (normalize A hA + normalize B hB) = finsetAffineDim (A + B) := by
  rw [normalize_add, finsetAffineDim_image_sub]

end Normalize

section GeometricDeletion

variable {D d : ℕ}
variable (X Y : Finset (Fin D → ℝ))

private def deletedComplement : Finset (Fin D → ℝ) :=
  ((X.erase 0) ∪ (Y.erase 0)) \ ((X.erase 0) + (Y.erase 0))

private noncomputable def lowerSection (S : Finset (Fin D → ℝ))
    (x : Fin D → ℝ) : Finset (Fin D → ℝ) := by
  classical
  exact S.filter fun y ↦ toLex y < toLex x

private lemma lowerSection_card_lt {S : Finset (Fin D → ℝ)} {x y : Fin D → ℝ}
    (hx : x ∈ S) (hxy : toLex x < toLex y) :
    (lowerSection S x).card < (lowerSection S y).card := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨x, ?_, ?_⟩
    · rw [lowerSection, Finset.mem_filter]
      exact ⟨hx, hxy⟩
    · rw [lowerSection, Finset.mem_filter]
      intro h
      exact (lt_irrefl (toLex x)) h.2
  · intro z hz
    rw [lowerSection, Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, hz.2.trans hxy⟩

private lemma add_erase_zero_decomposition (h0X : 0 ∈ X) (h0Y : 0 ∈ Y) :
    X + Y = insert 0 (((X.erase 0) + (Y.erase 0)) ∪
      deletedComplement X Y) := by
  ext z
  constructor
  · intro hz
    rw [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    by_cases hx0 : x = 0
    · rw [hx0, zero_add]
      by_cases hy0 : y = 0
      · rw [Finset.mem_insert]
        exact Or.inl hy0
      · rw [Finset.mem_insert]
        right
        by_cases hyP : y ∈ X.erase 0 + Y.erase 0
        · exact Finset.mem_union_left _ hyP
        · apply Finset.mem_union_right
          rw [deletedComplement, Finset.mem_sdiff]
          exact ⟨Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hy0, hy⟩), hyP⟩
    · by_cases hy0 : y = 0
      · rw [hy0, add_zero, Finset.mem_insert]
        right
        by_cases hxP : x ∈ X.erase 0 + Y.erase 0
        · exact Finset.mem_union_left _ hxP
        · apply Finset.mem_union_right
          rw [deletedComplement, Finset.mem_sdiff]
          exact ⟨Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hx0, hx⟩), hxP⟩
      · rw [Finset.mem_insert]
        right
        apply Finset.mem_union_left
        exact Finset.add_mem_add (Finset.mem_erase.2 ⟨hx0, hx⟩)
          (Finset.mem_erase.2 ⟨hy0, hy⟩)
  · intro hz
    rw [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · simpa using Finset.add_mem_add h0X h0Y
    · rw [Finset.mem_union] at hz
      rcases hz with hz | hz
      · rw [Finset.mem_add] at hz ⊢
        obtain ⟨x, hx, y, hy, rfl⟩ := hz
        exact ⟨x, Finset.mem_of_mem_erase hx, y, Finset.mem_of_mem_erase hy, rfl⟩
      · rw [deletedComplement, Finset.mem_sdiff, Finset.mem_union] at hz
        rcases hz.1 with hz | hz
        · simpa using Finset.add_mem_add (Finset.mem_of_mem_erase hz) h0Y
        · simpa using Finset.add_mem_add h0X (Finset.mem_of_mem_erase hz)

private lemma zero_notMem_add_erase_zero
    (hposX : ∀ x ∈ X, x ≠ 0 → 0 < toLex x)
    (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y) :
    0 ∉ X.erase 0 + Y.erase 0 := by
  intro hzero
  rw [Finset.mem_add] at hzero
  obtain ⟨x, hx, y, hy, hxy⟩ := hzero
  refine (add_pos (a := toLex x) (b := toLex y) ?_ ?_).ne' ?_
  · exact hposX x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx)
  · exact hposY y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy)
  · rw [← toLex_add, hxy, toLex_zero]

private lemma span_deleted_complement
    (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hposX : ∀ x ∈ X, x ≠ 0 → 0 < toLex x)
    (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y) :
    ∀ z ∈ X + Y,
      z ∈ Submodule.span ℝ (deletedComplement X Y : Set (Fin D → ℝ)) := by
  classical
  intro z hz
  generalize hk : (lowerSection (X + Y) z).card = k
  induction k using Nat.strong_induction_on generalizing z
  rename_i k ih
  by_cases hz0 : z = 0
  · rw [hz0]
    exact Submodule.zero_mem _
  by_cases hzC : z ∈ deletedComplement X Y
  · exact Submodule.subset_span hzC
  rw [add_erase_zero_decomposition X Y h0X h0Y, Finset.mem_insert,
    Finset.mem_union] at hz
  rcases hz with hz | hz | hz
  · exact (hz0 hz).elim
  · rw [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    apply Submodule.add_mem
    · apply ih (lowerSection (X + Y) x).card
      · rw [← hk]
        apply lowerSection_card_lt
        · simpa using Finset.add_mem_add (Finset.mem_of_mem_erase hx) h0Y
        · rw [toLex_add]
          exact lt_add_of_pos_right _
            (hposY y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy))
      · simpa using Finset.add_mem_add (Finset.mem_of_mem_erase hx) h0Y
      · rfl
    · apply ih (lowerSection (X + Y) y).card
      · rw [← hk]
        apply lowerSection_card_lt
        · simpa using Finset.add_mem_add h0X (Finset.mem_of_mem_erase hy)
        · rw [toLex_add]
          exact lt_add_of_pos_left _
            (hposX x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx))
      · simpa using Finset.add_mem_add h0X (Finset.mem_of_mem_erase hy)
      · rfl
  · exact (hzC hz).elim

private lemma finsetAffineDim_le_card_of_span {S C : Finset (Fin D → ℝ)}
    (h0 : 0 ∈ S) (hspan : ∀ x ∈ S, x ∈ Submodule.span ℝ (C : Set (Fin D → ℝ))) :
    finsetAffineDim S ≤ C.card := by
  unfold finsetAffineDim
  rw [direction_affineSpan]
  refine (Submodule.finrank_mono ?_).trans (finrank_span_finset_le_card C)
  · rw [vectorSpan_eq_span_vsub_set_right ℝ (s := (S : Set (Fin D → ℝ))) (p := 0) h0]
    apply Submodule.span_le.mpr
    rintro z ⟨x, hx, rfl⟩
    simpa using hspan x hx

private lemma finsetAffineDim_le_finrank_of_mem {S : Finset (Fin D → ℝ)}
    (U : Submodule ℝ (Fin D → ℝ)) (h0 : 0 ∈ S) (hmem : ∀ x ∈ S, x ∈ U) :
    finsetAffineDim S ≤ Module.finrank ℝ U := by
  unfold finsetAffineDim
  rw [direction_affineSpan]
  apply Submodule.finrank_mono
  rw [vectorSpan_eq_span_vsub_set_right ℝ (s := (S : Set (Fin D → ℝ))) (p := 0) h0]
  apply Submodule.span_le.mpr
  rintro z ⟨x, hx, rfl⟩
  simpa using hmem x hx

private lemma left_vsub_mem_deleted_direction
    {x₀ y₀ x : Fin D → ℝ} (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (hx : x ∈ X.erase 0) :
    x - x₀ ∈ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction := by
  simpa [vsub_eq_sub] using
    (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).vsub_mem_direction
        (subset_affineSpan ℝ _ (Finset.add_mem_add hx hy₀))
        (subset_affineSpan ℝ _ (Finset.add_mem_add hx₀ hy₀))

private lemma right_vsub_mem_deleted_direction
    {x₀ y₀ y : Fin D → ℝ} (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (hy : y ∈ Y.erase 0) :
    y - y₀ ∈ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction := by
  simpa [vsub_eq_sub] using
    (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).vsub_mem_direction
        (subset_affineSpan ℝ _ (Finset.add_mem_add hx₀ hy))
        (subset_affineSpan ℝ _ (Finset.add_mem_add hx₀ hy₀))

private lemma sum_vsub_mem_deleted_direction
    {x₀ y₀ z : Fin D → ℝ} (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (hz : z ∈ X.erase 0 + Y.erase 0) :
    z - (x₀ + y₀) ∈ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction := by
  simpa [vsub_eq_sub] using
    (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).vsub_mem_direction
        (subset_affineSpan ℝ _ hz)
        (subset_affineSpan ℝ _ (Finset.add_mem_add hx₀ hy₀))

private lemma finrank_deleted_direction_eq {e : ℕ}
    (hdel : finsetAffineDim (X.erase 0 + Y.erase 0) = e) :
    Module.finrank ℝ
      (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
        Set (Fin D → ℝ))).direction = e := by
  simpa [finsetAffineDim] using hdel

private lemma add_mem_direction_sup_span_pair
    {x₀ y₀ : Fin D → ℝ} (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (z : Fin D → ℝ) (hz : z ∈ X + Y) :
    z ∈ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({x₀, y₀} : Set (Fin D → ℝ)) := by
  rw [Finset.mem_add] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  apply Submodule.add_mem
  · by_cases hx0 : x = 0
    · rw [hx0]
      exact Submodule.zero_mem _
    · rw [← sub_add_cancel x x₀]
      apply Submodule.add_mem_sup
      · apply left_vsub_mem_deleted_direction X Y hx₀ hy₀
        exact Finset.mem_erase.2 ⟨hx0, hx⟩
      · apply Submodule.subset_span
        simp
  · by_cases hy0 : y = 0
    · rw [hy0]
      exact Submodule.zero_mem _
    · rw [← sub_add_cancel y y₀]
      apply Submodule.add_mem_sup
      · apply right_vsub_mem_deleted_direction X Y hx₀ hy₀
        exact Finset.mem_erase.2 ⟨hy0, hy⟩
      · apply Submodule.subset_span
        simp

private lemma deleted_dim_add_two_ge
    {x₀ y₀ : Fin D → ℝ} (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0) :
    finsetAffineDim (X + Y) ≤ finsetAffineDim (X.erase 0 + Y.erase 0) + 2 := by
  refine le_trans (finsetAffineDim_le_finrank_of_mem
    ((affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({x₀, y₀} : Set (Fin D → ℝ)))
    ?_ ?_) ?_
  · simpa using Finset.add_mem_add h0X h0Y
  · intro z hz
    exact add_mem_direction_sup_span_pair X Y hx₀ hy₀ z hz
  · refine le_trans (Submodule.finrank_add_le_finrank_add_finrank _ _) ?_
    apply Nat.add_le_add
    · rfl
    · rw [← Finset.coe_pair]
      simpa [Set.finrank] using
        (finrank_span_finset_le_card (R := ℝ)
          ({x₀, y₀} : Finset (Fin D → ℝ))).trans (Finset.card_le_two)

private lemma finsetAffineDim_le_finrank_of_vsub {S : Finset (Fin D → ℝ)}
    (U : Submodule ℝ (Fin D → ℝ)) {p : Fin D → ℝ} (hp : p ∈ S)
    (hmem : ∀ x ∈ S, x - p ∈ U) : finsetAffineDim S ≤ Module.finrank ℝ U := by
  unfold finsetAffineDim
  rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ
    (s := (S : Set (Fin D → ℝ))) (p := p) hp]
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro z ⟨x, hx, rfl⟩
  simpa [vsub_eq_sub] using hmem x hx

private lemma add_eq_union_add_erase_right (h0Y : 0 ∈ Y) :
    X + Y = X ∪ (X + Y.erase 0) := by
  ext z
  constructor
  · intro hz
    rw [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    by_cases hy0 : y = 0
    · rw [hy0, add_zero]
      exact Finset.mem_union_left _ hx
    · apply Finset.mem_union_right
      exact Finset.add_mem_add hx (Finset.mem_erase.2 ⟨hy0, hy⟩)
  · intro hz
    rw [Finset.mem_union] at hz
    rcases hz with hz | hz
    · simpa using Finset.add_mem_add hz h0Y
    · rw [Finset.mem_add] at hz ⊢
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      exact ⟨x, hx, y, Finset.mem_of_mem_erase hy, rfl⟩

private lemma add_eq_union_erase_left_add (h0X : 0 ∈ X) :
    X + Y = Y ∪ (X.erase 0 + Y) := by
  ext z
  constructor
  · intro hz
    rw [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    by_cases hx0 : x = 0
    · rw [hx0, zero_add]
      exact Finset.mem_union_left _ hy
    · apply Finset.mem_union_right
      exact Finset.add_mem_add (Finset.mem_erase.2 ⟨hx0, hx⟩) hy
  · intro hz
    rw [Finset.mem_union] at hz
    rcases hz with hz | hz
    · simpa using Finset.add_mem_add h0X hz
    · rw [Finset.mem_add] at hz ⊢
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      exact ⟨x, Finset.mem_of_mem_erase hx, y, hy, rfl⟩

private lemma deleted_dim_eq_pred_of_left_base_mem
    {e : ℕ} {x₀ y₀ : Fin D → ℝ} (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (hdim : finsetAffineDim (X + Y) = d)
    (hdel : finsetAffineDim (X.erase 0 + Y.erase 0) = e) (hed : e < d)
    (hxU : x₀ ∈ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction) : e = d - 1 := by
  suffices d ≤ e + 1 by omega
  rw [← hdim]
  refine (finsetAffineDim_le_finrank_of_mem
    ((affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({y₀} : Set (Fin D → ℝ)))
    ?_ ?_).trans ?_
  · simpa using Finset.add_mem_add h0X h0Y
  · intro z hz
    rw [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    apply Submodule.add_mem
    · by_cases hx0 : x = 0
      · rw [hx0]
        exact Submodule.zero_mem _
      · refine (le_sup_left :
          (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
            Set (Fin D → ℝ))).direction ≤
          (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
            Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({y₀} : Set (Fin D → ℝ))) ?_
        rw [← sub_add_cancel x x₀]
        exact Submodule.add_mem _
          (left_vsub_mem_deleted_direction X Y hx₀ hy₀
            (Finset.mem_erase.2 ⟨hx0, hx⟩)) hxU
    · by_cases hy0 : y = 0
      · rw [hy0]
        exact Submodule.zero_mem _
      · rw [← sub_add_cancel y y₀]
        apply Submodule.add_mem_sup
        · exact right_vsub_mem_deleted_direction X Y hx₀ hy₀
            (Finset.mem_erase.2 ⟨hy0, hy⟩)
        · apply Submodule.subset_span
          simp
  · apply le_trans (Submodule.finrank_add_le_finrank_add_finrank _ _)
    rw [finrank_deleted_direction_eq X Y hdel]
    apply Nat.add_le_add_left
    rw [← Finset.coe_singleton]
    simpa [Set.finrank] using
      (finrank_span_finset_le_card (R := ℝ) ({y₀} : Finset (Fin D → ℝ))).trans_eq
        (Finset.card_singleton y₀)

private lemma right_base_not_mem_of_left_base_mem
    {e : ℕ} {x₀ y₀ : Fin D → ℝ} (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (hdim : finsetAffineDim (X + Y) = d)
    (hdel : finsetAffineDim (X.erase 0 + Y.erase 0) = e) (hed : e < d)
    (hxU : x₀ ∈ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction) :
    y₀ ∉ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction := by
  intro hyU
  apply Nat.not_le_of_lt hed
  rw [← hdel, ← hdim]
  apply finsetAffineDim_le_finrank_of_mem
  · simpa using Finset.add_mem_add h0X h0Y
  · intro z hz
    rw [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    apply Submodule.add_mem
    · by_cases hx0 : x = 0
      · rw [hx0]
        exact Submodule.zero_mem _
      · rw [← sub_add_cancel x x₀]
        exact Submodule.add_mem _
          (left_vsub_mem_deleted_direction X Y hx₀ hy₀
            (Finset.mem_erase.2 ⟨hx0, hx⟩)) hxU
    · by_cases hy0 : y = 0
      · rw [hy0]
        exact Submodule.zero_mem _
      · rw [← sub_add_cancel y y₀]
        exact Submodule.add_mem _
          (right_vsub_mem_deleted_direction X Y hx₀ hy₀
            (Finset.mem_erase.2 ⟨hy0, hy⟩)) hyU

private lemma left_base_mem_deletion
    {e : ℕ} {x₀ y₀ : Fin D → ℝ} (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (hdim : finsetAffineDim (X + Y) = d)
    (hdel : finsetAffineDim (X.erase 0 + Y.erase 0) = e) (hed : e < d)
    (hxU : x₀ ∈ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction) :
    finsetAffineDim (X + Y.erase 0) = d - 1 ∧
      X.card + (X + Y.erase 0).card ≤ (X + Y).card := by
  rw [← deleted_dim_eq_pred_of_left_base_mem X Y h0X h0Y hx₀ hy₀ hdim hdel hed hxU]
  constructor
  · apply Nat.le_antisymm
    · refine (finsetAffineDim_le_finrank_of_vsub
        (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
          Set (Fin D → ℝ))).direction
        (p := y₀) ?_ ?_).trans ?_
      · simpa using Finset.add_mem_add h0X hy₀
      · intro z hz
        rw [Finset.mem_add] at hz
        obtain ⟨x, hx, y, hy, rfl⟩ := hz
        rw [sub_eq_add_neg, add_assoc]
        apply Submodule.add_mem
        · by_cases hx0 : x = 0
          · rw [hx0]
            exact Submodule.zero_mem _
          · rw [← sub_add_cancel x x₀]
            exact Submodule.add_mem _
              (left_vsub_mem_deleted_direction X Y hx₀ hy₀
                (Finset.mem_erase.2 ⟨hx0, hx⟩)) hxU
        · simpa [sub_eq_add_neg] using right_vsub_mem_deleted_direction X Y hx₀ hy₀ hy
      · simpa [finsetAffineDim] using hdel.le
    · rw [← hdel]
      apply finsetAffineDim_mono
      intro z hz
      rw [Finset.mem_add] at hz ⊢
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      exact ⟨x, Finset.mem_of_mem_erase hx, y, hy, rfl⟩
  · rw [add_eq_union_add_erase_right X Y h0Y, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro z hzX hzT
    apply right_base_not_mem_of_left_base_mem X Y h0X h0Y hx₀ hy₀ hdim hdel hed hxU
    convert
      (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
        Set (Fin D → ℝ))).direction.sub_mem (x := z) (y := z - y₀) ?_ ?_ using 1
    · abel
    · by_cases hz0 : z = 0
      · rw [hz0]
        exact Submodule.zero_mem _
      · rw [← sub_add_cancel z x₀]
        exact Submodule.add_mem _
          (left_vsub_mem_deleted_direction X Y hx₀ hy₀
            (Finset.mem_erase.2 ⟨hz0, hzX⟩)) hxU
    · rw [Finset.mem_add] at hzT
      obtain ⟨x, hx, y, hy, rfl⟩ := hzT
      rw [sub_eq_add_neg, add_assoc]
      apply Submodule.add_mem
      · by_cases hx0 : x = 0
        · rw [hx0]
          exact Submodule.zero_mem _
        · rw [← sub_add_cancel x x₀]
          exact Submodule.add_mem _
            (left_vsub_mem_deleted_direction X Y hx₀ hy₀
              (Finset.mem_erase.2 ⟨hx0, hx⟩)) hxU
      · simpa [sub_eq_add_neg] using right_vsub_mem_deleted_direction X Y hx₀ hy₀ hy

private lemma left_base_not_mem_codimension_one_deletion
    {e : ℕ} {x₀ y₀ : Fin D → ℝ} (h0X : 0 ∈ X) (_h0Y : 0 ∈ Y)
    (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (hposX : ∀ x ∈ X, x ≠ 0 → 0 < toLex x)
    (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y)
    (hdel : finsetAffineDim (X.erase 0 + Y.erase 0) = e) (he : e = d - 1)
    (hxU : x₀ ∉ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction) :
    finsetAffineDim (X.erase 0 + Y.erase 0) = d - 1 ∧
      Y.card + (X.erase 0 + Y.erase 0).card ≤ (X + Y).card := by
  refine ⟨hdel.trans he, ?_⟩
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro z hz
    rw [Finset.mem_union] at hz
    rcases hz with hz | hz
    · simpa using Finset.add_mem_add h0X hz
    · rw [Finset.mem_add] at hz ⊢
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      exact ⟨x, Finset.mem_of_mem_erase hx, y, Finset.mem_of_mem_erase hy, rfl⟩
  · rw [Finset.disjoint_left]
    intro z hzY hzP
    by_cases hz0 : z = 0
    · subst z
      exact zero_notMem_add_erase_zero X Y hposX hposY hzP
    · apply hxU
      convert
        (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
          Set (Fin D → ℝ))).direction.sub_mem
            (x := z - y₀) (y := z - (x₀ + y₀)) ?_ ?_ using 1
      · abel
      · exact right_vsub_mem_deleted_direction X Y hx₀ hy₀
          (Finset.mem_erase.2 ⟨hz0, hzY⟩)
      · exact sum_vsub_mem_deleted_direction X Y hx₀ hy₀ hzP

private lemma right_base_not_mem_direction_sup_left
    {e : ℕ} {x₀ y₀ : Fin D → ℝ} (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (hdim : finsetAffineDim (X + Y) = d)
    (hdel : finsetAffineDim (X.erase 0 + Y.erase 0) = e) (_hed : e < d)
    (he : d = e + 2)
    (hxU : x₀ ∉ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction) :
    y₀ ∉ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({x₀} : Set (Fin D → ℝ)) := by
  intro hyW
  suffices d ≤ e + 1 by omega
  rw [← hdim]
  refine (finsetAffineDim_le_finrank_of_mem
    ((affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({x₀} : Set (Fin D → ℝ)))
    ?_ ?_).trans ?_
  · simpa using Finset.add_mem_add h0X h0Y
  · intro z hz
    rw [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    apply Submodule.add_mem
    · by_cases hx0 : x = 0
      · rw [hx0]
        exact Submodule.zero_mem _
      · rw [← sub_add_cancel x x₀]
        apply Submodule.add_mem_sup
        · exact left_vsub_mem_deleted_direction X Y hx₀ hy₀
            (Finset.mem_erase.2 ⟨hx0, hx⟩)
        · apply Submodule.subset_span
          simp
    · by_cases hy0 : y = 0
      · rw [hy0]
        exact Submodule.zero_mem _
      · rw [← sub_add_cancel y y₀]
        exact Submodule.add_mem _
          ((le_sup_left :
            (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
              Set (Fin D → ℝ))).direction ≤
            (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
              Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({x₀} : Set (Fin D → ℝ)))
            (right_vsub_mem_deleted_direction X Y hx₀ hy₀
              (Finset.mem_erase.2 ⟨hy0, hy⟩))) hyW
  · rw [Submodule.finrank_sup_span_singleton hxU]
    simpa [finsetAffineDim] using Nat.add_le_add_right hdel.le 1

private lemma codimension_two_deletion
    {e : ℕ} {x₀ y₀ : Fin D → ℝ} (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (hposX : ∀ x ∈ X, x ≠ 0 → 0 < toLex x)
    (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y)
    (hdim : finsetAffineDim (X + Y) = d)
    (hdel : finsetAffineDim (X.erase 0 + Y.erase 0) = e) (hed : e < d)
    (he : d = e + 2)
    (hxU : x₀ ∉ (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
      Set (Fin D → ℝ))).direction) :
    finsetAffineDim (X.erase 0 + Y) = d - 1 ∧
      Y.card + (X.erase 0 + Y).card ≤ (X + Y).card := by
  simp only [he, Nat.add_one_sub_one]
  constructor
  · apply Nat.le_antisymm
    · refine (finsetAffineDim_le_finrank_of_vsub
        ((affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
          Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({y₀} : Set (Fin D → ℝ)))
        (p := x₀) ?_ ?_).trans ?_
      · simpa using Finset.add_mem_add hx₀ h0Y
      · intro z hz
        rw [Finset.mem_add] at hz
        obtain ⟨x, hx, y, hy, rfl⟩ := hz
        rw [sub_eq_add_neg, add_assoc, add_comm y (-x₀), ← add_assoc]
        apply Submodule.add_mem
        · exact (le_sup_left :
            (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
              Set (Fin D → ℝ))).direction ≤
            (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
              Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({y₀} : Set (Fin D → ℝ)))
            (left_vsub_mem_deleted_direction X Y hx₀ hy₀ hx)
        · by_cases hy0 : y = 0
          · rw [hy0]
            exact Submodule.zero_mem _
          · rw [← sub_add_cancel y y₀]
            apply Submodule.add_mem_sup
            · exact right_vsub_mem_deleted_direction X Y hx₀ hy₀
                (Finset.mem_erase.2 ⟨hy0, hy⟩)
            · apply Submodule.subset_span
              simp
      · rw [Submodule.finrank_sup_span_singleton]
        · simpa [finsetAffineDim] using Nat.add_le_add_right hdel.le 1
        · intro hyU
          apply right_base_not_mem_direction_sup_left X Y h0X h0Y hx₀ hy₀ hdim hdel hed he hxU
          exact (le_sup_left :
            (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
              Set (Fin D → ℝ))).direction ≤
            (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
              Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({x₀} : Set (Fin D → ℝ))) hyU
    · rw [← finrank_deleted_direction_eq X Y hdel]
      rw [← Submodule.finrank_sup_span_singleton]
      · apply Submodule.finrank_mono
        refine sup_le ?_ ?_
        · apply AffineSubspace.direction_le
          apply affineSpan_mono
          intro z hz
          change z ∈ X.erase 0 + Y.erase 0 at hz
          change z ∈ X.erase 0 + Y
          rw [Finset.mem_add] at hz ⊢
          obtain ⟨x, hx, y, hy, rfl⟩ := hz
          exact ⟨x, hx, y, Finset.mem_of_mem_erase hy, rfl⟩
        · apply Submodule.span_le.mpr
          · intro z hz
            rw [Set.mem_singleton_iff] at hz
            · subst z
              simpa [vsub_eq_sub] using
                (affineSpan ℝ ((X.erase 0 + Y : Finset (Fin D → ℝ)) :
                  Set (Fin D → ℝ))).vsub_mem_direction
                    (subset_affineSpan ℝ _
                      (Finset.add_mem_add hx₀ (Finset.mem_of_mem_erase hy₀)))
                    (subset_affineSpan ℝ _ (Finset.add_mem_add hx₀ h0Y))
      · intro hyU
        apply right_base_not_mem_direction_sup_left X Y h0X h0Y hx₀ hy₀ hdim hdel hed he hxU
        exact (le_sup_left :
          (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
            Set (Fin D → ℝ))).direction ≤
          (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
            Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({x₀} : Set (Fin D → ℝ))) hyU
  · rw [add_eq_union_erase_left_add X Y h0X, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro z hzY hzT
    rw [Finset.mem_add] at hzT
    obtain ⟨x, hx, y, hy, hxy⟩ := hzT
    by_cases hz0 : z = 0
    · subst z
      by_cases hy0 : y = 0
      · apply Finset.ne_of_mem_erase hx
        rw [hy0, add_zero] at hz0
        exact hz0
      · refine (add_pos (a := toLex x) (b := toLex y) ?_ ?_).ne' ?_
        · exact hposX x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx)
        · exact hposY y hy hy0
        · rw [← toLex_add, hz0, toLex_zero]
    · by_cases hy0 : y = 0
      · apply right_base_not_mem_direction_sup_left X Y h0X h0Y hx₀ hy₀ hdim hdel hed he hxU
        rw [right_base_difference_of_eq (x₀ := x₀) (y₀ := y₀) hy0 hxy]
        apply Submodule.add_mem
        · exact (le_sup_left :
            (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
              Set (Fin D → ℝ))).direction ≤
            (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
              Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({x₀} : Set (Fin D → ℝ)))
            (Submodule.sub_mem _
              (left_vsub_mem_deleted_direction X Y hx₀ hy₀ hx)
              (right_vsub_mem_deleted_direction X Y hx₀ hy₀
                (Finset.mem_erase.2 ⟨hz0, hzY⟩)))
        · exact (le_sup_right : Submodule.span ℝ ({x₀} : Set (Fin D → ℝ)) ≤
            (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
              Set (Fin D → ℝ))).direction ⊔ Submodule.span ℝ ({x₀} : Set (Fin D → ℝ)))
            (Submodule.mem_span_singleton_self x₀)
      · apply hxU
        rw [left_base_difference_of_eq (x₀ := x₀) (y₀ := y₀) hxy]
        exact Submodule.sub_mem _
          (Submodule.sub_mem _
            (right_vsub_mem_deleted_direction X Y hx₀ hy₀
              (Finset.mem_erase.2 ⟨hz0, hzY⟩))
            (right_vsub_mem_deleted_direction X Y hx₀ hy₀
              (Finset.mem_erase.2 ⟨hy0, hy⟩)))
          (left_vsub_mem_deleted_direction X Y hx₀ hy₀ hx)

private lemma full_dim_deletion_card
    (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hposX : ∀ x ∈ X, x ≠ 0 → 0 < toLex x)
    (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y)
    (hdim : finsetAffineDim (X + Y) = d) :
    (X.erase 0 + Y.erase 0).card + d + 1 ≤ (X + Y).card := by
  classical
  rw [add_erase_zero_decomposition X Y h0X h0Y, Finset.card_insert_of_notMem]
  · rw [Finset.card_union_of_disjoint]
    · apply Nat.add_le_add_right
      apply Nat.add_le_add_left
      rw [← hdim]
      apply finsetAffineDim_le_card_of_span
      · simpa using Finset.add_mem_add h0X h0Y
      · exact span_deleted_complement X Y h0X h0Y hposX hposY
    · exact Finset.disjoint_sdiff
  · rw [Finset.mem_union]
    push Not
    refine ⟨zero_notMem_add_erase_zero X Y hposX hposY, ?_⟩
    intro hzero
    rw [deletedComplement, Finset.mem_sdiff] at hzero
    simpa using hzero.1

private lemma deleted_dim_lt_of_ne
    (hdim : finsetAffineDim (X + Y) = d)
    (hne : finsetAffineDim (X.erase 0 + Y.erase 0) ≠ d) :
    finsetAffineDim (X.erase 0 + Y.erase 0) < d := by
  refine Nat.lt_of_le_of_ne ?_ hne
  · rw [← hdim]
    apply finsetAffineDim_mono
    intro z hz
    rw [Finset.mem_add] at hz ⊢
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    exact ⟨x, Finset.mem_of_mem_erase hx, y, Finset.mem_of_mem_erase hy, rfl⟩

private lemma deleted_dim_le_add_two
    {x₀ y₀ : Fin D → ℝ} (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (hdim : finsetAffineDim (X + Y) = d) :
    d ≤ finsetAffineDim (X.erase 0 + Y.erase 0) + 2 := by
  rw [← hdim]
  exact deleted_dim_add_two_ge X Y h0X h0Y hx₀ hy₀

private lemma deleted_dim_gap_cases
    {x₀ y₀ : Fin D → ℝ} (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    (hdim : finsetAffineDim (X + Y) = d)
    (hne : finsetAffineDim (X.erase 0 + Y.erase 0) ≠ d) :
    d = finsetAffineDim (X.erase 0 + Y.erase 0) + 1 ∨
      d = finsetAffineDim (X.erase 0 + Y.erase 0) + 2 := by
  rcases Nat.eq_or_lt_of_le (deleted_dim_le_add_two X Y h0X h0Y hx₀ hy₀ hdim) with heq | hlt
  · right
    exact heq
  · left
    rcases Nat.exists_eq_add_of_lt (deleted_dim_lt_of_ne X Y hdim hne) with ⟨k, rfl⟩
    omega

private lemma geometric_deletion_cases
    (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hposX : ∀ x ∈ X, x ≠ 0 → 0 < toLex x)
    (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y)
    (hXcard : 2 ≤ X.card) (hYcard : 2 ≤ Y.card)
    (hdim : finsetAffineDim (X + Y) = d) :
    (finsetAffineDim (X.erase 0 + Y.erase 0) = d ∧
      (X.erase 0 + Y.erase 0).card + d + 1 ≤ (X + Y).card) ∨
      (finsetAffineDim (X.erase 0 + Y.erase 0) = d - 1 ∧
        Y.card + (X.erase 0 + Y.erase 0).card ≤ (X + Y).card) ∨
      (finsetAffineDim (X.erase 0 + Y) = d - 1 ∧
        Y.card + (X.erase 0 + Y).card ≤ (X + Y).card) ∨
      (finsetAffineDim (X + Y.erase 0) = d - 1 ∧
        X.card + (X + Y.erase 0).card ≤ (X + Y).card) := by
  classical
  by_cases hdimdel : finsetAffineDim (X.erase 0 + Y.erase 0) = d
  · left
    exact ⟨hdimdel, full_dim_deletion_card X Y h0X h0Y hposX hposY hdim⟩
  · right
    obtain ⟨x₀, hx₀⟩ : (X.erase 0).Nonempty := by
      apply (Finset.one_lt_card_iff_nontrivial.mp ?_).erase_nonempty
      omega
    obtain ⟨y₀, hy₀⟩ : (Y.erase 0).Nonempty := by
      apply (Finset.one_lt_card_iff_nontrivial.mp ?_).erase_nonempty
      omega
    by_cases hxU : x₀ ∈
        (affineSpan ℝ ((X.erase 0 + Y.erase 0 : Finset (Fin D → ℝ)) :
          Set (Fin D → ℝ))).direction
    · right
      right
      exact left_base_mem_deletion X Y h0X h0Y hx₀ hy₀ hdim rfl
        (deleted_dim_lt_of_ne X Y hdim hdimdel) hxU
    · rcases deleted_dim_gap_cases X Y h0X h0Y hx₀ hy₀ hdim hdimdel with hcodim | hcodim
      · left
        refine left_base_not_mem_codimension_one_deletion X Y h0X h0Y hx₀ hy₀
          hposX hposY rfl ?_ hxU
        omega
      · right
        left
        apply codimension_two_deletion X Y h0X h0Y hx₀ hy₀ hposX hposY hdim rfl
          (deleted_dim_lt_of_ne X Y hdim hdimdel) hcodim hxU

end GeometricDeletion

private theorem sumsetCardLowerBound_le_card_add :
    ∀ {D d : ℕ} (A B : Finset (Fin D → ℝ)),
      B.Nonempty → B.card ≤ A.card → finsetAffineDim (A + B) = d →
        sumsetCardLowerBound d B.card A.card ≤ (A + B).card := by
  intro D d A B hB hBA hdim
  generalize hn : A.card + B.card = n
  induction n using Nat.strong_induction_on generalizing D d A B
  rename_i n ih
  by_cases hBcard : B.card = 1
  · rw [sumsetCardLowerBound_eq, hBcard]
    simp only [tsub_self, Order.lt_one_iff, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, add_zero]
    exact Finset.card_le_card_add_right hB
  let hA : A.Nonempty := Finset.card_pos.mp ((Finset.card_pos.mpr hB).trans_le hBA)
  let X := normalize B hB
  let Y := normalize A hA
  rw [← normalize_add_card A B hA hB, ← normalize_card B hB, ← normalize_card A hA]
  rw [add_comm (normalize A hA) (normalize B hB)]
  change sumsetCardLowerBound d X.card Y.card ≤ (X + Y).card
  have h0X : 0 ∈ X := zero_mem_normalize B hB
  have h0Y : 0 ∈ Y := zero_mem_normalize A hA
  have hXtwo : 2 ≤ X.card := by
    simpa [X, normalize_card] using two_le_card_of_nonempty_ne_one B hB hBcard
  have hYtwo : 2 ≤ Y.card := by
    simpa [Y, normalize_card] using
      (two_le_card_of_nonempty_ne_one B hB hBcard).trans hBA
  have hXerase : (X.erase 0).Nonempty := by
    apply (Finset.one_lt_card_iff_nontrivial.mp ?_).erase_nonempty
    omega
  have hXYle : X.card ≤ Y.card := by
    simpa [X, Y, normalize_card] using hBA
  have hYXsum : Y.card + X.card = n := by
    simpa [X, Y, normalize_card, add_comm] using hn
  have hcases :
      (finsetAffineDim (X.erase 0 + Y.erase 0) = d ∧
        (X.erase 0 + Y.erase 0).card + d + 1 ≤ (X + Y).card) ∨
        (finsetAffineDim (X.erase 0 + Y.erase 0) = d - 1 ∧
          Y.card + (X.erase 0 + Y.erase 0).card ≤ (X + Y).card) ∨
        (finsetAffineDim (X.erase 0 + Y) = d - 1 ∧
          Y.card + (X.erase 0 + Y).card ≤ (X + Y).card) ∨
        (finsetAffineDim (X + Y.erase 0) = d - 1 ∧
          X.card + (X + Y.erase 0).card ≤ (X + Y).card) := by
    refine geometric_deletion_cases X Y h0X h0Y ?_ ?_ hXtwo hYtwo ?_
    · intro x hx hx0
      exact normalize_pos_of_ne_zero B hB hx hx0
    · intro y hy hy0
      exact normalize_pos_of_ne_zero A hA hy hy0
    · simpa [X, Y, add_comm] using (normalize_add_dim A B hA hB).trans hdim
  rcases hcases with hfull | hlarge | hsmall | hright
  · apply sumsetCardLowerBound_of_full_case hXtwo
    · have hrec :
          sumsetCardLowerBound d (X.erase 0).card (Y.erase 0).card ≤
            (Y.erase 0 + X.erase 0).card := by
        refine ih ((Y.erase 0).card + (X.erase 0).card) ?_
          (Y.erase 0) (X.erase 0) hXerase ?_ ?_ rfl
        · exact card_erase_add_card_erase_lt h0Y h0X hYXsum
        · exact card_erase_le_card_erase h0X h0Y hXYle
        · simpa [add_comm] using hfull.1
      simpa [X, Y, Finset.card_erase_of_mem h0X,
        Finset.card_erase_of_mem h0Y, add_comm] using hrec
    · exact hfull.2
  · apply sumsetCardLowerBound_of_large_case hXtwo
      hXYle
    · have hrec :
          sumsetCardLowerBound (d - 1) (X.erase 0).card (Y.erase 0).card ≤
            (Y.erase 0 + X.erase 0).card := by
        refine ih ((Y.erase 0).card + (X.erase 0).card) ?_
          (Y.erase 0) (X.erase 0) hXerase ?_ ?_ rfl
        · exact card_erase_add_card_erase_lt h0Y h0X hYXsum
        · exact card_erase_le_card_erase h0X h0Y hXYle
        · simpa [add_comm] using hlarge.1
      simpa [X, Y, Finset.card_erase_of_mem h0X,
        Finset.card_erase_of_mem h0Y, add_comm] using hrec
    · exact hlarge.2
  · apply sumsetCardLowerBound_of_small_case hXtwo
      hXYle
    · have hrec :
          sumsetCardLowerBound (d - 1) (X.erase 0).card Y.card ≤
            (Y + X.erase 0).card := by
        refine ih ((X.erase 0).card + Y.card) ?_
          Y (X.erase 0) hXerase ?_ ?_ ?_
        · apply card_erase_add_card_lt h0X
          simpa [add_comm] using hYXsum
        · exact card_erase_le_card h0X hXYle
        · simpa [add_comm] using hsmall.1
        · omega
      simpa [X, Y, Finset.card_erase_of_mem h0X, add_comm] using hrec
    · exact hsmall.2
  · by_cases hXY : X.card = Y.card
    · rw [hXY]
      apply sumsetCardLowerBound_of_equal_right_case hYtwo
      · have hrec :
            sumsetCardLowerBound (d - 1) (Y.erase 0).card X.card ≤
              (X + Y.erase 0).card := by
          refine ih ((Y.erase 0).card + X.card)
            (card_erase_add_card_lt h0Y hYXsum) X (Y.erase 0) ?_ ?_ ?_ ?_
          · apply (Finset.one_lt_card_iff_nontrivial.mp ?_).erase_nonempty
            omega
          · apply card_erase_le_card h0Y
            omega
          · simpa [add_comm] using hright.1
          · omega
        simpa [X, Y, Finset.card_erase_of_mem h0Y, hXY, add_comm] using hrec
      · simpa [hXY] using hright.2
    · have hXYlt : X.card < Y.card := lt_of_le_of_ne hXYle hXY
      refine sumsetCardLowerBound_of_strict_right_case ?_ hXYlt ?_ hright.2
      · omega
      · have hrec :
            sumsetCardLowerBound (d - 1) X.card (Y.erase 0).card ≤
              (Y.erase 0 + X).card := by
          refine ih ((Y.erase 0).card + X.card)
            (card_erase_add_card_lt h0Y hYXsum) (Y.erase 0) X
            (normalize_nonempty B hB) (card_le_card_erase h0Y hXYlt) ?_ rfl
          simpa [add_comm] using hright.1
        simpa [X, Y, Finset.card_erase_of_mem h0Y, add_comm] using hrec

/-- The sharp sumset-cardinality lower bound determined by the affine dimension of the sumset. -/
theorem card_add_lower_bound_of_affineDim {D d : ℕ} (A B : Finset (Fin D → ℝ))
    (hB : B.Nonempty) (hBA : B.card ≤ A.card) (hdim : finsetAffineDim (A + B) = d) :
    A.card + (Finset.Icc 1 (B.card - 1)).sum (fun t ↦ min d (A.card - t)) ≤
      (A + B).card := by
  rw [← sumsetCardLowerBound_eq]
  exact sumsetCardLowerBound_le_card_add A B hB hBA hdim

end

end DenseSetsWithoutLargeSumsets
