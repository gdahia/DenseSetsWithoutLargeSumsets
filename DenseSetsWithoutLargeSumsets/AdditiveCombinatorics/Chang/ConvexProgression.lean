/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.Chang.GapToolkit
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.FreimanDimension
import Mathlib.Analysis.Convex.Basic

/-! # Symmetric convex progressions

This module contains the elementary interface for finite sets of lattice points in symmetric convex
bodies, used to describe the concrete box projections and slices constructed by its callers.
-/

namespace DenseSetsWithoutLargeSumsets

noncomputable section

/-- The coordinatewise inclusion of integer vectors into real vectors. -/
def intVectorToReal {d : ℕ} (v : Fin d → ℤ) : Fin d → ℝ := fun i ↦ v i

lemma intVectorToReal_injective {d : ℕ} :
    Function.Injective (intVectorToReal (d := d)) := by
  intro a b h
  funext i
  have hi := congr_fun h i
  change (a i : ℝ) = (b i : ℝ) at hi
  exact_mod_cast hi

@[simp] lemma intVectorToReal_zero {d : ℕ} :
    intVectorToReal (0 : Fin d → ℤ) = 0 := by
  ext i
  simp [intVectorToReal]

@[simp] lemma intVectorToReal_add {d : ℕ} (a b : Fin d → ℤ) :
    intVectorToReal (a + b) = intVectorToReal a + intVectorToReal b := by
  ext i
  simp [intVectorToReal, Pi.add_apply]

@[simp] lemma intVectorToReal_neg {d : ℕ} (a : Fin d → ℤ) :
    intVectorToReal (-a) = -intVectorToReal a := by
  ext i
  simp [intVectorToReal, Pi.neg_apply]

@[simp] lemma intVectorToReal_sub {d : ℕ} (a b : Fin d → ℤ) :
    intVectorToReal (a - b) = intVectorToReal a - intVectorToReal b := by
  ext i
  simp [intVectorToReal, Pi.sub_apply]

/-- The finite lattice points of a symmetric convex body of affine dimension at most `r`. -/
def IsSymmetricConvexProgression {d r : ℕ} (D : Finset (Fin d → ℤ)) : Prop :=
  ∃ K : Set (Fin d → ℝ),
    Convex ℝ K ∧ (∀ x, x ∈ K ↔ -x ∈ K) ∧
      (∀ v : Fin d → ℤ, v ∈ D ↔ intVectorToReal v ∈ K) ∧
      finsetAffineDim (D.image intVectorToReal) ≤ r

end

end DenseSetsWithoutLargeSumsets
