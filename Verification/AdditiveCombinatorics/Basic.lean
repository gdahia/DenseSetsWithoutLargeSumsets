/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Combinatorics.Additive.FreimanHom

/-!
Additive-combinatorics infrastructure
-/

open scoped BigOperators Pointwise

namespace Verification

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

end

end Verification
