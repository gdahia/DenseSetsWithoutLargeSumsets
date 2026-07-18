/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import Mathlib.Tactic.SetNotationForOrder
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Common definitions
-/

open scoped BigOperators Pointwise

namespace DenseSetsWithoutLargeSumsets

noncomputable section

def interval (n : ℕ) : Finset ℕ := Finset.Icc 1 n

def natCastImage (A : Finset ℕ) : Finset ℤ :=
  A.image (Nat.castAddMonoidHom ℤ)

lemma natCastImage_card (A : Finset ℕ) : (natCastImage A).card = A.card := by
  exact Finset.card_image_of_injective _ Int.ofNat_injective

lemma natCastImage_add (A B : Finset ℕ) :
    natCastImage (A + B) = natCastImage A + natCastImage B := by
  exact Finset.image_add (Nat.castAddMonoidHom ℤ)

lemma natCastImage_sum_card (A B : Finset ℕ) :
    (natCastImage A + natCastImage B).card = (A + B).card := by
  rw [← natCastImage_add, natCastImage_card]

lemma log_le_half_self {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / 2 := by
  have hx2 : 0 < x / 2 := by positivity
  have hlog : Real.log x = Real.log (x / 2) + Real.log (2 : ℝ) := by
    rw [← Real.log_mul hx2.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    ring_nf
  nlinarith [hlog, Real.log_le_sub_one_of_pos hx2,
    Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

lemma log_two_gt_half : (1 / 2 : ℝ) < Real.log (2 : ℝ) := by
  norm_num
  nlinarith [Real.lt_log_one_add_of_pos (by norm_num : 0 < (1 : ℝ))]

def pairSumsetIsSubset (n k : ℕ) (lb ub : ℝ) (S : Finset ℕ) : Prop :=
  ∃ A B : Finset ℕ, A ⊆ interval n ∧ B ⊆ interval n ∧ A.card = k ∧ B.card = k ∧
      lb ≤ (A + B).card ∧ (A + B).card ≤ ub ∧ A + B ⊆ S

def exactPairEvent (n k : ℕ) (S : Finset ℕ) : Prop :=
  ∃ A B : Finset ℕ,
    A ⊆ interval n ∧ B ⊆ interval n ∧ A.card = k ∧ B.card = k ∧ A + B ⊆ S

def pairEvent (n k : ℕ) (S : Finset ℕ) : Prop :=
  ∃ A B : Finset ℕ,
    A ⊆ interval n ∧ B ⊆ interval n ∧ k ≤ A.card ∧ k ≤ B.card ∧ A + B ⊆ S

def existsDenseSetWithoutLargeSumsets (n k : ℕ) (δ : unitInterval) : Prop :=
  ∃ S : Finset ℕ,
    S ⊆ interval n ∧ (δ : ℝ) * (n : ℝ) ≤ (S.card : ℝ) ∧ ¬ pairEvent n k S

def eventuallyForDensities (α c : ℝ) (P : ℕ → unitInterval → Prop) : Prop :=
  ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ),
    ∀ δ : unitInterval,
      Real.rpow (n : ℝ) (-α) < (δ : ℝ) → (δ : ℝ) ≤ 1 - c → P n δ

def pairCardThreshold (c : ℝ) (n : ℕ) (δ : unitInterval) : ℕ :=
  Nat.ceil (c * Real.log (n : ℝ) / Real.log (1 / δ))

/-- Coefficient controlling `pairCardThreshold` when the density is bounded by `1 - c`. -/
def densityCoefficient (τ c : ℝ) : ℝ :=
  τ / Real.log (1 / (1 - c)) + 1 / Real.log 2

lemma densityCoefficient_gt_one {τ c : ℝ} (hτ_pos : 0 < τ)
    (hc_pos : 0 < c) (hc_lt : c < 1) :
    1 < densityCoefficient τ c := by
  have hgap_pos : 0 < Real.log (1 / (1 - c)) := by
    apply Real.log_pos
    rw [one_lt_div] <;> linarith
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2_lt_one : Real.log (2 : ℝ) < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have hone_lt : 1 < 1 / Real.log 2 := by
    rw [one_lt_div hlog2_pos]
    exact hlog2_lt_one
  dsimp [densityCoefficient]
  nlinarith [div_nonneg hτ_pos.le hgap_pos.le]

lemma densityCoefficient_pos {τ c : ℝ} (hτ_pos : 0 < τ)
    (hc_pos : 0 < c) (hc_lt : c < 1) :
    0 < densityCoefficient τ c :=
  zero_lt_one.trans (densityCoefficient_gt_one hτ_pos hc_pos hc_lt)

lemma pairCardThreshold_le_densityCoefficient_mul_log {τ c : ℝ} {n : ℕ}
    {δ : unitInterval} (hτ_nonneg : 0 ≤ τ) (hc_pos : 0 < c) (hn_two : 2 ≤ n)
    (hδ_pos : 0 < (δ : ℝ)) (hδ_upper : (δ : ℝ) ≤ 1 - c) :
    (pairCardThreshold τ n δ : ℝ) ≤
      densityCoefficient τ c * Real.log (n : ℝ) := by
  have h1c_pos : (0 : ℝ) < 1 - c := lt_of_lt_of_le hδ_pos hδ_upper
  have hlogn_pos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hn_two)
  unfold pairCardThreshold densityCoefficient
  refine (le_of_lt (Nat.ceil_lt_add_one ?_)).trans ?_
  · refine div_nonneg (mul_nonneg hτ_nonneg hlogn_pos.le) (Real.log_pos ?_).le
    rw [one_lt_div hδ_pos]
    linarith
  · rw [add_mul]
    refine add_le_add ?_ ?_
    · rw [div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_left (mul_nonneg hτ_nonneg hlogn_pos.le) ?_ ?_
      · refine Real.log_pos ?_
        rw [one_lt_div h1c_pos]
        linarith
      · exact Real.log_le_log (one_div_pos.mpr h1c_pos)
          (one_div_le_one_div_of_le hδ_pos hδ_upper)
    · rw [one_div_mul_eq_div, le_div_iff₀ (Real.log_pos one_lt_two), one_mul]
      exact Real.log_le_log zero_lt_two (by exact_mod_cast hn_two)

def pairEventDecayExponent (γ : ℝ) : ℝ := γ / (8 * (γ + 3))

end

end DenseSetsWithoutLargeSumsets
