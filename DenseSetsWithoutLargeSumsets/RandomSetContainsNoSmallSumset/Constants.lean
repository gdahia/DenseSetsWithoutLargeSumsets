/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.CyclicFreimanDimension
public import DenseSetsWithoutLargeSumsets.Common
public import LargeSumsetsFromSubsets.MediumSizedSubsets
import Mathlib.NumberTheory.Bertrand

/-!
# Constants for the random set argument

This file defines the constants in the proof that a random set contains no pair of sets with a
small sumset, from *Dense sets without large sumsets* (Dahia, Marciano, Souza). The proof fixes a
doubling constant `C` and an error `γ`, moves the problem from `[n]` to `ZMod q` for a prime
`2 * n ≤ q ≤ 4 * n`, and needs `n` to be large and the density to be at least `n ^ (-α)`.

## Main definitions

* `ε`: the error `ε = γ / (4 * (γ + 2))`.
* `κ`: the doubling constant `κ = 6 * C ^ 2` given to Chang's theorem.
* `lowerBltConstant`: the constant of the Bollobás–Leader–Tiba theorem for `σ = 2 * C` and `ε`.
* `lowerConstant`: the maximum of the constant of Chang's theorem and `4 * lowerBltConstant`.
* `lowerDensityExponent`: the exponent `α`.
* `lowerSizeThreshold`, `lowerGapThreshold`: the lower bounds on `n`.

## Main statements

* `exists_zmod_model`: for `n > 0` there are a prime `2 * n ≤ q ≤ 4 * n` and a Freiman
  isomorphism of order `2` from `[n]` to a subset of `ZMod q`.
-/

@[expose] public section

namespace DenseSetsWithoutLargeSumsets

open ChangFreimanRuzsa LargeSumsetsFromSubsets

noncomputable section

/-- The bound `exp (freimanDimExponent κ) * k` on the size of the proper progression that
Chang's theorem gives for a set of size at most `k` and doubling at most `κ`. -/
def changCarrierBound (k : ℕ) (κ : ℝ) : ℝ := Real.exp (freimanDimExponent κ) * k

private lemma natCast_zmod_inj {q a b : ℕ} (ha : a < q) (hb : b < q) :
    (a : ZMod q) = b ↔ a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- For `n > 0` there is a prime `q` with `2 * n ≤ q ≤ 4 * n` for which the cast `ℕ → ZMod q` is
a Freiman isomorphism of order `2` from `[n]` to its image. -/
lemma exists_zmod_model (n : ℕ) (hn : 0 < n) : ∃ q : ℕ, Nat.Prime q ∧ 2 * n ≤ q ∧ q ≤ 4 * n ∧
    ∃ ψ : ℕ → ZMod q, IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ := by
  obtain ⟨q, hq, hq_gt, hq_le⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * n) (by grind)
  refine ⟨q, hq, hq_gt.le, by grind, fun x ↦ (x : ZMod q), ?_⟩
  rw [isAddFreimanIso_two]
  simp only [interval, Finset.coe_Icc, Set.mem_Icc]
  constructor
  · apply Set.InjOn.bijOn_image
    intro a ha b hb hab
    exact (natCast_zmod_inj (by grind) (by grind)).1 hab
  · intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂
    exact_mod_cast natCast_zmod_inj (a := a₁ + b₁) (b := a₂ + b₂) (by grind) (by grind)

/-- The error `ε = γ / (4 * (γ + 2))`. -/
def ε (γ : ℝ) : ℝ := γ / (4 * (γ + 2))

/-- The doubling constant `κ = 6 * C ^ 2` given to Chang's theorem. -/
def κ (C : ℝ) : ℝ := 6 * C ^ (2 : ℕ)

/-- The exponent of Chang's theorem for doubling `κ C`. -/
def changExponent (C : ℝ) : ℝ := freimanDimExponent (κ C)

/-- The constant of the Bollobás–Leader–Tiba theorem for `σ = 2 * C` and the error `ε γ`. -/
def lowerBltConstant (C γ : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) : ℝ :=
  bltConstant (2 * C) (ε γ) hC hε

/-- The constant `lowerBltConstant C γ` as a function of `C` and `γ` alone. It is `1` when
`2 * C` or `ε γ` is not positive. -/
def lowerBltConstantDefault (C γ : ℝ) : ℝ :=
  if hC : 0 < 2 * C then
    if hε : 0 < ε γ then lowerBltConstant C γ hC hε else 1
  else 1

lemma lowerBltConstantDefault_eq (C γ : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) :
    lowerBltConstantDefault C γ = lowerBltConstant C γ hC hε := by
  simp [lowerBltConstantDefault, hC, hε]

/-- The maximum of `exp (changExponent C)` and `4 * lowerBltConstant C γ`. -/
def lowerConstant (C γ : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) : ℝ :=
  max (Real.exp (changExponent C)) (4 * lowerBltConstant C γ hC hε)

/-- The constant `lowerConstant C γ` as a function of `C` and `γ` alone. -/
def lowerConstantDefault (C γ : ℝ) : ℝ :=
  max (Real.exp (changExponent C)) (4 * lowerBltConstantDefault C γ)

lemma lowerConstantDefault_eq (C γ : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) :
    lowerConstantDefault C γ = lowerConstant C γ hC hε := by
  simp [lowerConstantDefault, lowerConstant, lowerBltConstantDefault_eq C γ hC hε]

lemma one_le_lowerBltConstant {C γ : ℝ} (hC : 0 < 2 * C) (hε : 0 < ε γ) :
    1 ≤ lowerBltConstant C γ hC hε :=
  one_le_bltConstant hC hε

lemma lowerBltConstant_le_lowerConstant {C γ : ℝ} (hC : 0 < 2 * C) (hε : 0 < ε γ) :
    lowerBltConstant C γ hC hε ≤ lowerConstant C γ hC hε := by
  refine le_trans ?_ (le_max_right _ _)
  linarith [one_le_lowerBltConstant hC hε]

lemma one_le_lowerConstant {C γ : ℝ} (hC : 0 < 2 * C) (hε : 0 < ε γ) :
    1 ≤ lowerConstant C γ hC hε :=
  (one_le_lowerBltConstant hC hε).trans (lowerBltConstant_le_lowerConstant hC hε)

lemma lowerConstant_eq (C γ : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) :
    lowerConstant C γ hC hε =
      max (Real.exp (freimanDimExponent (κ C))) (4 * lowerBltConstant C γ hC hε) :=
  rfl

lemma lowerConstant_pos (C γ : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) : 0 < lowerConstant C γ hC hε :=
  (Real.exp_pos (changExponent C)).trans_le (le_max_left _ _)

/-- The scale `8 / ε γ` of the logarithmic condition on `n`. -/
def lowerLogScale (γ : ℝ) : ℝ := 8 / ε γ

/-- The scale `8 * lowerBltConstantDefault C γ * √14 / ε γ`. -/
def lowerSqrtScaleDefault (C γ : ℝ) : ℝ :=
  8 * lowerBltConstantDefault C γ * Real.sqrt 14 / ε γ

/-- The scale `8 * lowerBltConstantDefault C γ * √K / ε γ` of the square root condition on `n`,
where `K = densityCoefficient (3 + γ) c`. -/
def lowerGapSqrtScaleDefault (C γ c : ℝ) : ℝ :=
  8 * lowerBltConstantDefault C γ *
    Real.sqrt (densityCoefficient (3 + γ) c) / ε γ

/-- The scale `8 * lowerBltConstant C γ * √K / ε γ` of the square root condition on `n`, where
`K = densityCoefficient (3 + γ) c`. -/
def lowerGapSqrtScale (C γ c : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) : ℝ :=
  8 * lowerBltConstant C γ hC hε *
    Real.sqrt (densityCoefficient (3 + γ) c) / ε γ

lemma lowerGapSqrtScaleDefault_eq (C γ c : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) :
    lowerGapSqrtScaleDefault C γ c = lowerGapSqrtScale C γ c hC hε := by
  simp [lowerGapSqrtScaleDefault, lowerGapSqrtScale, lowerBltConstantDefault_eq C γ hC hε]

lemma lowerLogScale_pos {γ : ℝ} (hε : 0 < ε γ) : 0 < lowerLogScale γ := by
  rw [lowerLogScale]
  positivity

lemma lowerGapSqrtScale_pos {C γ c : ℝ} (hC : 0 < 2 * C) (hε : 0 < ε γ)
    (hK : 0 < densityCoefficient (3 + γ) c) :
    0 < lowerGapSqrtScale C γ c hC hε := by
  have := one_le_lowerBltConstant hC hε
  rw [lowerGapSqrtScale]
  positivity

/-- A lower bound on `n` in terms of `C` and `γ`. It is the exponential of the maximum of four
quantities, so that `n` above it satisfies four conditions on `log n`. -/
def lowerAnalyticThreshold (C γ : ℝ) : ℝ :=
  Real.exp <| max (4 * Real.log (56 : ℝ) + 1) <|
    max (2 * changExponent C) <|
      max (2 * lowerLogScale γ * Real.log (42 * lowerConstantDefault C γ * lowerLogScale γ))
        ((4 * lowerSqrtScaleDefault C γ * Real.log (84 * lowerConstantDefault C γ *
          lowerSqrtScaleDefault C γ)) ^
          (2 : ℕ))

/-- The exponent `α`. The densities considered are those larger than `n ^ (-α)`. -/
def lowerDensityExponent (C γ : ℝ) : ℝ := min
    ((2 + γ) * ε γ / (12 * C ^ (2 : ℕ)))
    ((2 + γ) / (2 * Real.exp (containerExponent (κ C)))) / 2

lemma ε_pos {γ : ℝ} (hγ : 0 < γ) : 0 < ε γ := by
  unfold ε
  positivity

lemma ε_le_one_twelfth {γ : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) : ε γ ≤ 1 / 12 := by
  rw [ε, div_le_iff₀ (by positivity)]
  linarith

lemma ε_lt_one_half {γ : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) : ε γ < 1 / 2 :=
  (ε_le_one_twelfth hγ_pos hγ_le).trans_lt (by norm_num)

lemma half_le_one_sub_ε {γ : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) : (1 / 2 : ℝ) ≤ 1 - ε γ := by
  linarith [ε_le_one_twelfth hγ_pos hγ_le]

lemma one_sub_three_mul_ε_pos {γ : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) : 0 < 1 - 3 * ε γ := by
  linarith [ε_le_one_twelfth hγ_pos hγ_le]

/-- The lower bound on `n` in terms of `C` and `γ`. -/
def lowerSizeThreshold (C γ : ℝ) : ℝ := max (lowerDensityExponent C γ)
    (max 2 (max ((36 * Real.exp (changExponent C)) ^ (2 : ℕ))
      (lowerAnalyticThreshold C γ)))

/-- The lower bound on `n` in terms of `C`, `γ` and the gap `c` between the density and `1`. -/
def lowerGapThreshold (C γ c : ℝ) : ℝ :=
  max (lowerSizeThreshold C γ) <| max
    ((2 * densityCoefficient (3 + γ) c * Real.exp (changExponent C)) ^ (2 : ℕ)) <|
    Real.exp <| max
      (2 * lowerLogScale γ * Real.log
        (max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstantDefault C γ * lowerLogScale γ))
      ((4 * lowerGapSqrtScaleDefault C γ c * Real.log
        (2 * max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstantDefault C γ *
          lowerGapSqrtScaleDefault C γ c)) ^ (2 : ℕ))

lemma lowerSizeThreshold_le_lowerGapThreshold (C γ c : ℝ) :
    lowerSizeThreshold C γ ≤ lowerGapThreshold C γ c :=
  le_max_left _ _

lemma two_le_lowerSizeThreshold (C γ : ℝ) : (2 : ℝ) ≤ lowerSizeThreshold C γ :=
  le_max_of_le_right (le_max_left _ _)

lemma old_model_threshold_le_lowerSizeThreshold (C γ : ℝ) :
    ((36 * Real.exp (changExponent C)) ^ (2 : ℕ)) ≤ lowerSizeThreshold C γ :=
  le_max_of_le_right (le_max_of_le_right (le_max_left _ _))

lemma lowerAnalyticThreshold_le_lowerSizeThreshold (C γ : ℝ) :
    lowerAnalyticThreshold C γ ≤ lowerSizeThreshold C γ :=
  le_max_of_le_right (le_max_of_le_right (le_max_right _ _))

lemma lowerSizeThreshold_lt_nat_pos {C γ : ℝ} {n : ℕ} (_hγ : 0 < γ) (_hC : 0 < C)
    (hn : lowerSizeThreshold C γ < n) : 0 < n := by
  rw [← Nat.cast_pos (α := ℝ)]
  linarith [two_le_lowerSizeThreshold C γ]

end

end DenseSetsWithoutLargeSumsets
