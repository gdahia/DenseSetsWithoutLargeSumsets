/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.NumberTheory.Bertrand
import DenseSetsWithoutLargeSumsets.Probability
import DenseSetsWithoutLargeSumsets.Common
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.FreimanDimension
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.Chang.Reduction
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.GeneralizedArithmeticProgression
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.LargeSumsetsFromMediumSizedSubsets.MediumSizedSubsets

/-!
The constants of the random-set-avoids-small-sumsets argument.

For a doubling parameter `C` and error `γ` this file collects the model embedding into
`ZMod q`, the BLT and Chang constants (`lowerBltConstant`, `lowerConstant`), the various log
and sqrt scales they feed into, and the two size thresholds (`lowerSizeThreshold`,
`lowerGapThreshold`) above which the rest of the argument applies.
-/

namespace DenseSetsWithoutLargeSumsets

open Nat hiding div_pos
open scoped Pointwise

noncomputable section

def changCarrierBound (k : ℕ) (κ : ℝ) : ℝ := Real.exp (changTheoremExponent κ) * k

lemma exists_zmod_model (n : ℕ) (hn : 0 < n) : ∃ q : ℕ, Nat.Prime q ∧ 2 * n ≤ q ∧ q ≤ 4 * n ∧
    ∃ ψ : ℕ → ZMod q, IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ := by
  obtain ⟨q, hq, hq_gt, hq_le⟩ :=
    exists_prime_lt_and_le_two_mul (2 * n) (Nat.mul_ne_zero (by norm_num) (Nat.ne_of_gt hn))
  refine ⟨q, hq, hq_gt.le, ?_, ?_⟩
  · omega
  · refine ⟨fun x ↦ (x : ZMod q), ?_⟩
    rw [isAddFreimanIso_two]
    constructor
    · apply Set.InjOn.bijOn_image
      intro a ha b hb hab
      rw [ZMod.natCast_eq_natCast_iff'] at hab
      unfold interval at ha hb
      norm_cast at ha hb
      simp only [Finset.mem_Icc] at ha hb
      rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] at hab
      · exact hab
      · omega
      · omega
    · intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂
      norm_cast at ha₁ hb₁ ha₂ hb₂
      unfold interval at ha₁ hb₁ ha₂ hb₂
      simp only [Finset.mem_Icc] at ha₁ hb₁ ha₂ hb₂
      norm_cast
      constructor
      · intro h_image_sum
        rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] at h_image_sum
        · exact h_image_sum
        · omega
        · omega
      · tauto

def ε (γ : ℝ) : ℝ := γ / (4 * (γ + 2))

def κ (C : ℝ) : ℝ := 6 * C ^ (2 : ℕ)

def changExponent (C : ℝ) : ℝ := changTheoremExponent (κ C)

def lowerBltConstant (C γ : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) : ℝ :=
  bltConstant (2 * C) (ε γ) hC hε

def lowerBltConstantDefault (C γ : ℝ) : ℝ :=
  if hC : 0 < 2 * C then
    if hε : 0 < ε γ then lowerBltConstant C γ hC hε else 1
  else 1

lemma lowerBltConstantDefault_eq (C γ : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) :
    lowerBltConstantDefault C γ = lowerBltConstant C γ hC hε := by
  simp [lowerBltConstantDefault, hC, hε]

def lowerConstant (C γ : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) : ℝ :=
  max (Real.exp (changExponent C)) (4 * lowerBltConstant C γ hC hε)

def lowerConstantDefault (C γ : ℝ) : ℝ :=
  max (Real.exp (changExponent C)) (4 * lowerBltConstantDefault C γ)

lemma lowerConstantDefault_eq (C γ : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) :
    lowerConstantDefault C γ = lowerConstant C γ hC hε := by
  simp [lowerConstantDefault, lowerConstant, lowerBltConstantDefault_eq C γ hC hε]

lemma one_le_lowerBltConstant {C γ : ℝ} (hC : 0 < 2 * C)
    (hε : 0 < ε γ) :
    1 ≤ lowerBltConstant C γ hC hε := by
  simpa [lowerBltConstant] using one_le_bltConstant hC hε

lemma lowerBltConstant_le_lowerConstant {C γ : ℝ} (hC : 0 < 2 * C)
    (hε : 0 < ε γ) :
    lowerBltConstant C γ hC hε ≤ lowerConstant C γ hC hε := by
  refine le_trans (b := 4 * lowerBltConstant C γ hC hε) ?_
    (le_max_right (Real.exp (changExponent C)) (4 * lowerBltConstant C γ hC hε))
  nlinarith [one_le_lowerBltConstant hC hε]

lemma one_le_lowerConstant {C γ : ℝ} (hC : 0 < 2 * C) (hε : 0 < ε γ) :
    1 ≤ lowerConstant C γ hC hε := by
  exact (one_le_lowerBltConstant hC hε).trans
    (lowerBltConstant_le_lowerConstant hC hε)

lemma lowerConstant_eq (C γ : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) :
    lowerConstant C γ hC hε =
      max (Real.exp (changTheoremExponent (κ C)))
        (4 * lowerBltConstant C γ hC hε) := by
  simp [lowerConstant, changExponent]

lemma lowerConstant_pos (C γ : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) : 0 < lowerConstant C γ hC hε :=
  (Real.exp_pos (changExponent C)).trans_le (le_max_left _ _)

def lowerLogScale (γ : ℝ) : ℝ := 8 / ε γ

def lowerSqrtScaleDefault (C γ : ℝ) : ℝ :=
  8 * lowerBltConstantDefault C γ * Real.sqrt 14 / ε γ

def lowerGapSqrtScaleDefault (C γ c : ℝ) : ℝ :=
  8 * lowerBltConstantDefault C γ *
    Real.sqrt (densityCoefficient (3 + γ) c) / ε γ

def lowerGapSqrtScale (C γ c : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) : ℝ :=
  8 * lowerBltConstant C γ hC hε *
    Real.sqrt (densityCoefficient (3 + γ) c) / ε γ

lemma lowerGapSqrtScaleDefault_eq (C γ c : ℝ) (hC : 0 < 2 * C)
    (hε : 0 < ε γ) :
    lowerGapSqrtScaleDefault C γ c = lowerGapSqrtScale C γ c hC hε := by
  simp [lowerGapSqrtScaleDefault, lowerGapSqrtScale, lowerBltConstantDefault_eq C γ hC hε]

lemma lowerLogScale_pos {γ : ℝ} (hε : 0 < ε γ) :
    0 < lowerLogScale γ := by
  rw [lowerLogScale]
  positivity

lemma lowerGapSqrtScale_pos {C γ c : ℝ} (hC : 0 < 2 * C) (hε : 0 < ε γ)
    (hK : 0 < densityCoefficient (3 + γ) c) :
    0 < lowerGapSqrtScale C γ c hC hε := by
  rw [lowerGapSqrtScale]
  exact div_pos (mul_pos (mul_pos (by norm_num)
    (zero_lt_one.trans_le (one_le_lowerBltConstant hC hε))) (Real.sqrt_pos.2 hK)) hε

def lowerAnalyticThreshold (C γ : ℝ) : ℝ :=
  Real.exp <| max (4 * Real.log (56 : ℝ) + 1) <|
    max (2 * changExponent C) <|
      max (2 * lowerLogScale γ * Real.log (42 * lowerConstantDefault C γ * lowerLogScale γ))
        ((4 * lowerSqrtScaleDefault C γ * Real.log (84 * lowerConstantDefault C γ *
          lowerSqrtScaleDefault C γ)) ^
          (2 : ℕ))

def lowerDensityExponent (C γ : ℝ) : ℝ := min
    ((2 + γ) * ε γ / (12 * C ^ (2 : ℕ)))
    ((2 + γ) / (2 * Real.exp (changContainerExponent (κ C)))) / 2

lemma ε_pos {γ : ℝ} (hγ : 0 < γ) : 0 < ε γ := by
  unfold ε
  positivity

lemma ε_le_one_twelfth {γ : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) :
    ε γ ≤ 1 / 12 := by
  unfold ε
  refine (div_le_iff₀ ?_).mpr ?_
  · positivity
  · nlinarith

lemma ε_lt_one_half {γ : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) :
    ε γ < 1 / 2 := by
  refine (ε_le_one_twelfth hγ_pos hγ_le).trans_lt ?_
  norm_num

lemma half_le_one_sub_ε {γ : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) :
    (1 / 2 : ℝ) ≤ 1 - ε γ := by
  linarith [ε_le_one_twelfth hγ_pos hγ_le]

lemma one_sub_three_mul_ε_pos {γ : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) :
    0 < 1 - 3 * ε γ := by
  linarith [ε_le_one_twelfth hγ_pos hγ_le]

def lowerSizeThreshold (C γ : ℝ) : ℝ := max (lowerDensityExponent C γ)
    (max 2 (max ((36 * Real.exp (changExponent C)) ^ (2 : ℕ))
      (lowerAnalyticThreshold C γ)))

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

lemma two_le_lowerSizeThreshold (C γ : ℝ) : (2 : ℝ) ≤ lowerSizeThreshold C γ := by
  unfold lowerSizeThreshold
  exact (le_max_left (2 : ℝ)
      (max ((36 * Real.exp (changExponent C)) ^ (2 : ℕ)) (lowerAnalyticThreshold C γ))).trans
    (le_max_right (lowerDensityExponent C γ)
      (max 2 (max ((36 * Real.exp (changExponent C)) ^ (2 : ℕ))
        (lowerAnalyticThreshold C γ))))

lemma old_model_threshold_le_lowerSizeThreshold (C γ : ℝ) :
    ((36 * Real.exp (changExponent C)) ^ (2 : ℕ)) ≤ lowerSizeThreshold C γ := by
  unfold lowerSizeThreshold
  exact (le_max_left ((36 * Real.exp (changExponent C)) ^ (2 : ℕ))
      (lowerAnalyticThreshold C γ)).trans
    ((le_max_right (2 : ℝ)
      (max ((36 * Real.exp (changExponent C)) ^ (2 : ℕ))
        (lowerAnalyticThreshold C γ))).trans
      (le_max_right (lowerDensityExponent C γ)
        (max 2 (max ((36 * Real.exp (changExponent C)) ^ (2 : ℕ))
          (lowerAnalyticThreshold C γ)))))

lemma lowerAnalyticThreshold_le_lowerSizeThreshold (C γ : ℝ) :
    lowerAnalyticThreshold C γ ≤ lowerSizeThreshold C γ := by
  unfold lowerSizeThreshold
  exact (le_max_right ((36 * Real.exp (changExponent C)) ^ (2 : ℕ))
      (lowerAnalyticThreshold C γ)).trans
    ((le_max_right (2 : ℝ)
      (max ((36 * Real.exp (changExponent C)) ^ (2 : ℕ))
        (lowerAnalyticThreshold C γ))).trans
      (le_max_right (lowerDensityExponent C γ)
        (max 2 (max ((36 * Real.exp (changExponent C)) ^ (2 : ℕ))
          (lowerAnalyticThreshold C γ)))))

lemma lowerSizeThreshold_lt_nat_pos {C γ : ℝ} {n : ℕ} (_hγ : 0 < γ) (_hC : 0 < C)
    (hn : lowerSizeThreshold C γ < n) : 0 < n := by
  have hnpos : (0 : ℝ) < n := by
    refine lt_of_le_of_lt ?_ hn
    apply le_trans (b := 2)
    · norm_num
    · exact two_le_lowerSizeThreshold C γ
  exact_mod_cast hnpos

end

end DenseSetsWithoutLargeSumsets
