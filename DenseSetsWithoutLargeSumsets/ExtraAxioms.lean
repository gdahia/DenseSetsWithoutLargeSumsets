/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.Basic
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.GeneralizedArithmeticProgression

/-!
The additional mathematical assumptions used by the formalization.

This file is deliberately self-contained apart from Mathlib and the project's definitions of
`freimanDim` and `ProperGAP`.
-/

namespace DenseSetsWithoutLargeSumsets

open scoped BigOperators Pointwise

noncomputable section

/-- The finset underlying a sample with replacement from `A`. -/
def bltSample {α : Type*} [DecidableEq α] (A : Finset α) {r : ℕ}
    (a : Fin r → ↑A) : Finset α :=
  Finset.univ.image fun i ↦ a i

/-- The constant in Theorem 2 of Bollobás--Leader--Tiba. -/
opaque originalBltConstant (σ ε : ℝ) (_hσ : 0 < σ) (_hε : 0 < ε) : ℝ

/--
Theorem 2 of Bollobás--Leader--Tiba, stated with finite uniform expectation.  Sampling functions
allow repetitions, exactly as the independently and uniformly selected points in the paper.
-/
axiom exists_blt_sample {G : Type*} [DecidableEq G] [AddCommGroup G] {σ ε : ℝ}
    (hσ : 0 < σ) (hε : 0 < ε) {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty)
    (c₁ c₂ : ℕ) (hc₁pos : 1 ≤ c₁) (hc₁A : c₁ ≤ A.card) (hc₂pos : 1 ≤ c₂)
    (hc₂B : c₂ ≤ B.card)
    (hcprod : originalBltConstant σ ε hσ hε * (max A.card B.card : ℝ) < c₁ * c₂) :
    ∃ A₀ B₀ : Finset G, A₀.Nonempty ∧ B₀.Nonempty ∧ A₀ ⊆ A ∧ B₀ ⊆ B ∧
      (1 - ε) * (A.card : ℝ) < (A₀.card : ℝ) ∧
      (1 - ε) * (B.card : ℝ) < (B₀.card : ℝ) ∧
      min (min ((1 - ε) * ((A₀ + B₀).card : ℝ)) (σ * (A₀.card : ℝ)))
          (σ * (B₀.card : ℝ)) <
        𝔼 ab : (Fin c₁ → ↑A₀) × (Fin c₂ → ↑B₀),
          ((bltSample A₀ ab.1 + bltSample B₀ ab.2).card : ℝ)

opaque changConstant : ℝ

axiom changConstant_pos : 0 < changConstant

axiom exists_properGAP_of_small_sumset
    {q : ℕ} {κ : ℝ} (X : Finset (ZMod q)) (hq : Nat.Prime q) (hκ : 2 ≤ κ)
    (hXX : (X + X).card ≤ κ * X.card)
    (hX_lower : changConstant * κ ^ 3 * (Real.log κ) ^ 2 < X.card)
    (hX_upper : X.card < Real.exp (-changConstant * κ ^ 4 * (Real.log κ) ^ 2) * q) :
    ∃ P : ProperGAP (ZMod q), X ⊆ P ∧ P.dim ≤ freimanDim X ∧
      P.carrier.card ≤ Real.exp (changConstant * κ ^ 4 * (Real.log κ) ^ 2) * X.card

end

end DenseSetsWithoutLargeSumsets
