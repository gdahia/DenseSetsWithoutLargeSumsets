/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.Chang.Container
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.Chang.Transport

/-! # Chang's theorem

This is the top of the Chang development and the home of its public statement,
`exists_properGAP_of_small_sumset`. The development is organized as the Ruzsa-model coarse
container (`Chang.RuzsaModel`, `Chang.Fourier`, `Chang.BohrProgression`, `Chang.Packing`,
`Chang.Container`), specialized box reboxing (`Chang.Reboxing.*`), simultaneous properization
(`Chang.Properization`), effective Freiman-coordinate reduction (`Chang.Transport`), and the final
quantitative composition below.

This file composes the coarse cyclic container with properization and the coordinate-and-lattice
transport of Appendix A. The container interface lives in `Chang.Container`; the geometric stages
are proved in `Chang.Properization` and `Chang.Transport`.

The dimension in the conclusion is the Freiman dimension of `X`, as in Green and Tao's form of the
Freiman--Bilu theorem, and that is the bound the downstream argument consumes: it separately bounds
`freimanDim X` by `2 ⌈κ⌉ - 1`. The coarse container's own dimension, `changContainerExponent κ`,
appears here only as the argument of the quartic properization and transport costs.
-/

namespace DenseSetsWithoutLargeSumsets

open scoped Pointwise

noncomputable section

/-- The public budget of the cyclic Chang theorem: the coarse container's own cost together with
the quartic properization and coordinate-transport costs at the container's dimension. -/
def changTheoremExponent (κ : ℝ) : ℝ :=
  changContainerExponent κ +
    (properizationConstant + coordinateReductionConstant) * (changContainerExponent κ + 2) ^ 4

/-- **Chang's theorem** in the cyclic form used here: a set of small doubling in `ZMod q` which is
neither too small nor too dense is contained in a proper GAP of comparable size. The dimension of
the container is bounded by the Freiman dimension of `X`, as in Green and Tao's form of the
Freiman--Bilu theorem; this is the bound the downstream counting argument consumes, since it
bounds `freimanDim X` on its own. -/
theorem exists_properGAP_of_small_sumset {q : ℕ} {κ : ℝ} (X : Finset (ZMod q))
    (hq : Nat.Prime q) (hκ : 2 ≤ κ)
    (hXX : ((X + X).card : ℝ) ≤ κ * X.card)
    (hXlower : Real.exp (changContainerExponent κ) < X.card)
    (hXupper : (X.card : ℝ) < Real.exp (-changTheoremExponent κ) * q) :
    ∃ P : ProperGAP (ZMod q), X ⊆ P ∧ P.dim ≤ freimanDim X ∧
      (P.carrier.card : ℝ) ≤ Real.exp (changTheoremExponent κ) * X.card := by
  have hC₂ : 0 < properizationConstant := properizationConstant_pos
  have hC₄ : 0 < coordinateReductionConstant := coordinateReductionConstant_pos
  have hE : 0 < changContainerExponent κ := changContainerExponent_pos hκ
  have hbox : (0 : ℝ) ≤ (changContainerExponent κ + 2) ^ 4 := by positivity
  have hXne : X.Nonempty := by
    rw [← Finset.card_pos, ← Nat.cast_pos (α := ℝ)]
    exact (Real.exp_pos _).trans hXlower
  obtain ⟨P, hXP, -, hPdim, hPcard⟩ := exists_coarseGAP_container X hq hκ hXX hXlower
  -- The container's dimension is at most the coarse budget, so its quartic costs are too.
  have hfourth : ((P.dim : ℝ) + 2) ^ 4 ≤ (changContainerExponent κ + 2) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 4
  -- Every cost of the form `exp (A (P.dim + 2)⁴) |P|` still fits inside `ZMod q`.
  have hkey : ∀ A : ℝ, 0 ≤ A →
      A * (changContainerExponent κ + 2) ^ 4 + changContainerExponent κ ≤
        changTheoremExponent κ →
      Real.exp (A * ((P.dim : ℝ) + 2) ^ 4) * P.carrier.card ≤ q := by
    intro A hA hAC
    refine le_trans (mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hfourth hA))
      hPcard (Nat.cast_nonneg _) (Real.exp_nonneg _)) ?_
    rw [← mul_assoc, ← Real.exp_add]
    refine le_trans (mul_le_mul_of_nonneg_left hXupper.le (Real.exp_nonneg _)) ?_
    rw [← mul_assoc, ← Real.exp_add]
    refine le_trans (mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (by linarith))
      (Nat.cast_nonneg q)) (le_of_eq (one_mul _))
  obtain ⟨P₂, hP₂two, hPP₂, hP₂len, hP₂dim, hP₂card⟩ :=
    exists_twoProperGAP_container P hq
      (hkey properizationConstant hC₂.le
        (by rw [changTheoremExponent]; nlinarith [mul_nonneg hC₄.le hbox]))
  -- Properization and transport together cost `exp ((C₂ + C₄) (P.dim + 2)⁴)`.
  have hexp₄ : Real.exp (coordinateReductionConstant * ((P₂.dim : ℝ) + 2) ^ 4) ≤
      Real.exp (coordinateReductionConstant * ((P.dim : ℝ) + 2) ^ 4) := by
    refine Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ 4) hC₄.le)
    have hcast := (Nat.cast_le (α := ℝ)).mpr hP₂dim
    linarith
  have hmid : Real.exp (coordinateReductionConstant * ((P₂.dim : ℝ) + 2) ^ 4) *
        P₂.carrier.card ≤
      Real.exp ((coordinateReductionConstant + properizationConstant) *
        ((P.dim : ℝ) + 2) ^ 4) * P.carrier.card := by
    refine (mul_le_mul hexp₄ hP₂card (Nat.cast_nonneg _) (Real.exp_nonneg _)).trans ?_
    rw [← mul_assoc, ← Real.exp_add, ← add_mul]
  obtain ⟨Q, hQtwo, hXQ, hQdim, hQlen, hQcard⟩ :=
    chang_coordinate_reduction X P₂ hq hXne (hXP.trans hPP₂) hP₂two
      (hmid.trans (hkey (coordinateReductionConstant + properizationConstant) (by linarith)
        (by rw [changTheoremExponent]; nlinarith)))
  refine ⟨Q.toProperGAP (GAP.twoProper_proper Q hQtwo) hQlen, hXQ, hQdim, ?_⟩
  -- The accumulated cost is `exp (changTheoremExponent κ) |X|`.
  refine ((hQcard.trans hmid).trans (mul_le_mul
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hfourth (by linarith)))
    hPcard (Nat.cast_nonneg _) (Real.exp_nonneg _))).trans ?_
  rw [← mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (Nat.cast_nonneg _)
  rw [changTheoremExponent]
  ring_nf
  exact le_refl _

end

end DenseSetsWithoutLargeSumsets
