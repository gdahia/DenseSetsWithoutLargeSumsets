/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Combinatorics.Additive.FreimanHom

/-!
# A self-sumset bound for the Freiman dimension

This file derives the Freiman-dimension bound used in the small-sumset argument from the summed
lower bound for a union of two finite sets.
-/

namespace DenseSetsWithoutLargeSumsets

open scoped BigOperators Pointwise

noncomputable section
noncomputable def finsetAffineDim {d : ℕ} (S : Finset (Fin d → ℝ)) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ (S : Set (Fin d → ℝ))).direction

/-- Affine dimension is monotone under inclusion of finite sets. -/
lemma finsetAffineDim_mono {D : ℕ} {S T : Finset (Fin D → ℝ)}
    (hST : S ⊆ T) : finsetAffineDim S ≤ finsetAffineDim T := by
  unfold finsetAffineDim
  apply Submodule.finrank_mono
  apply AffineSubspace.direction_le
  apply affineSpan_mono
  simpa using hST

def rationalVectorToReal {d : ℕ} (v : Fin d → ℚ) : Fin d → ℝ :=
  fun i => (v i : ℝ)

def freimanModelDim {G : Type*} [DecidableEq G] [AddCommMonoid G] (X : Finset G) (d : ℕ) : Prop :=
  ∃ f : G → (Fin d → ℚ),
    IsAddFreimanIso 2 (X : Set G) ((X.image f : Finset (Fin d → ℚ)) : Set (Fin d → ℚ)) f ∧
      finsetAffineDim ((X.image f).image rationalVectorToReal) = d

noncomputable def freimanDim {G : Type*} [DecidableEq G] [AddCommMonoid G] (X : Finset G) : ℕ := by
    classical
    exact Nat.findGreatest (freimanModelDim X) X.card

lemma truncated_sum_eq {b r : ℕ} (hr : 1 ≤ r) (hrb : r ≤ b) :
    (Finset.Icc 1 (b - 1)).sum (fun t => min (r - 1) (b - t)) =
      Nat.choose r 2 + (b - r) * (r - 1) := by
  classical
  rw [← Finset.Ico_add_one_right_eq_Icc 1 (b - 1)]
  have hreflect :
      (Finset.Ico 1 b).sum (fun t => min (r - 1) (b - t)) =
        (Finset.Ico 1 b).sum (fun s => min (r - 1) s) := by
    convert
      (Finset.sum_Ico_reflect (fun s => min (r - 1) s) 1
        (m := b) (n := b) (Nat.le_succ b)) using 1
    congr 2
    all_goals omega
  rw [Nat.sub_add_cancel (hr.trans hrb), hreflect,
    ← Finset.sum_Ico_consecutive (fun s => min (r - 1) s) hr hrb]
  congr 1
  · trans (Finset.Ico 1 r).sum fun s => s
    · apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mem_Ico] at hs
      exact Nat.min_eq_right (by omega)
    · rw [← Nat.sub_add_cancel hr]
      rw [Finset.Ico_add_one_right_eq_Icc 1 (r - 1)]
      simpa [Nat.sub_add_cancel hr] using (Nat.sum_Icc_choose (r - 1) 1)
  · trans (Finset.Ico r b).sum fun _s => r - 1
    · apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mem_Ico] at hs
      exact Nat.min_eq_left (by omega)
    · simp [Finset.sum_const, Nat.card_Ico]

private lemma truncated_bound_contradiction {b r κ : ℚ} (hr : 0 < r) (hrb : r ≤ b)
    (hκr : 2 * κ ≤ r)
    (hbound : b + (r * (r - 1) / 2 + (b - r) * (r - 1)) ≤ κ * b) : False := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hκr) (hr.le.trans hrb),
    mul_nonneg hr.le (sub_nonneg.mpr hrb)]

lemma lt_two_mul_of_truncated_bound {b r κ : ℕ} (hr : 1 ≤ r) (hrb : r ≤ b)
    (hbound : b + (Nat.choose r 2 + (b - r) * (r - 1)) ≤ κ * b) :
    r < 2 * κ := by
  by_contra hnot
  apply truncated_bound_contradiction (b := (b : ℚ)) (r := (r : ℚ)) (κ := (κ : ℚ))
  · exact_mod_cast hr
  · exact_mod_cast hrb
  · exact_mod_cast Nat.le_of_not_gt hnot
  · rw [← Nat.cast_choose_two, ← Nat.cast_sub hrb]
    exact_mod_cast hbound
end

lemma le_freimanDim_of_model {G : Type*} [DecidableEq G] [AddCommMonoid G]
    (X : Finset G) {d : ℕ} (hd : d ≤ X.card) (hmodel : freimanModelDim X d) :
    d ≤ freimanDim X := by
  classical
  exact Nat.le_findGreatest hd hmodel

/-- A nonempty finite set of affine dimension `d` contains at least `d + 1` points. -/
lemma finsetAffineDim_add_one_le_card {d : ℕ} (S : Finset (Fin d → ℝ))
    (hS : S.Nonempty) : finsetAffineDim S + 1 ≤ S.card := by
  classical
  letI : Nonempty S := hS.to_subtype
  let p : S → (Fin d → ℝ) := Subtype.val
  have hp : Set.range p = (S : Set (Fin d → ℝ)) := by
    ext x
    simp [p]
  unfold finsetAffineDim
  rw [direction_affineSpan, ← hp]
  simpa only [Fintype.card_coe] using finrank_vectorSpan_range_add_one_le ℝ p

lemma finsetAffineDim_le_card {d : ℕ} (S : Finset (Fin d → ℝ)) :
    finsetAffineDim S ≤ S.card := by
  by_cases hS : S.Nonempty
  · exact (Nat.le_add_right _ _).trans (finsetAffineDim_add_one_le_card S hS)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS, finsetAffineDim]

end DenseSetsWithoutLargeSumsets
