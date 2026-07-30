/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! # Elementary API for Freiman dimension

The project's `freimanDim` is a bounded `Nat.findGreatest`. This file exposes its basic lower
bound API, used when Appendix A constructs an explicit full-dimensional Freiman model.
-/

namespace DenseSetsWithoutLargeSumsets

noncomputable section

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

end

end DenseSetsWithoutLargeSumsets
