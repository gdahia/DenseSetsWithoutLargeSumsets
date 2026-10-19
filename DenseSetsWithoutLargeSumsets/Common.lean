/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Common definitions

The definitions shared by the proof of Theorem 1.1 of *Dense sets without large sumsets* (Dahia,
Marciano, Souza): the interval `[n]`, the events that a set contains a sumset `A + B` with
`A, B ⊆ [n]` of given sizes, and the threshold `⌈c * log n / log (1 / δ)⌉` for these sizes.

## Main definitions

* `interval n`: the interval `[n] = {1, …, n}`.
* `pairEvent n k S`: the set `S` contains a sumset `A + B` with `A, B ⊆ [n]` and `|A|, |B| ≥ k`.
* `exactPairEvent n k S`: the same with `|A| = |B| = k`.
* `pairSumsetIsSubset n k lb ub S`: the same with `|A| = |B| = k` and `lb ≤ |A + B| ≤ ub`.
* `existsDenseSetWithoutLargeSumsets n k δ`: some `S ⊆ [n]` with `|S| ≥ δ n` contains no sumset
  `A + B` with `A, B ⊆ [n]` and `|A|, |B| ≥ k`.
* `pairCardThreshold c n δ`: the threshold `⌈c * log n / log (1 / δ)⌉`.

## Main statements

* `pairCardThreshold_le_densityCoefficient_mul_log`: if `δ ≤ 1 - c`, then
  `pairCardThreshold τ n δ ≤ densityCoefficient τ c * log n`.
-/

@[expose] public section

open scoped Pointwise

namespace DenseSetsWithoutLargeSumsets

noncomputable section

/-- The interval `[n] = {1, …, n}`. -/
def interval (n : ℕ) : Finset ℕ := Finset.Icc 1 n

/-- The image in `ℤ` of a finite set of natural numbers. -/
def natCastImage (A : Finset ℕ) : Finset ℤ :=
  A.image (Nat.castAddMonoidHom ℤ)

lemma natCastImage_card (A : Finset ℕ) : (natCastImage A).card = A.card :=
  Finset.card_image_of_injective _ Int.ofNat_injective

lemma natCastImage_add (A B : Finset ℕ) :
    natCastImage (A + B) = natCastImage A + natCastImage B :=
  Finset.image_add (Nat.castAddMonoidHom ℤ)

lemma natCastImage_sum_card (A B : Finset ℕ) :
    (natCastImage A + natCastImage B).card = (A + B).card := by
  rw [← natCastImage_add, natCastImage_card]

lemma log_le_half_self {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / 2 := by
  have h := Real.log_le_sub_one_of_pos (half_pos hx)
  rw [Real.log_div hx.ne' two_ne_zero] at h
  linarith [Real.log_le_sub_one_of_pos (zero_lt_two (α := ℝ))]

lemma log_two_gt_half : (1 / 2 : ℝ) < Real.log (2 : ℝ) := by
  have h := Real.lt_log_one_add_of_pos (one_pos (α := ℝ))
  norm_num at h
  linarith

private lemma log_two_lt_one : Real.log 2 < 1 := by
  linarith [Real.log_lt_sub_one_of_pos (zero_lt_two (α := ℝ)) (by norm_num)]

/-- The set `S` contains a sumset `A + B` with `A, B ⊆ [n]`, `|A| = |B| = k` and
`lb ≤ |A + B| ≤ ub`. -/
def pairSumsetIsSubset (n k : ℕ) (lb ub : ℝ) (S : Finset ℕ) : Prop :=
  ∃ A B : Finset ℕ, A ⊆ interval n ∧ B ⊆ interval n ∧ A.card = k ∧ B.card = k ∧
      lb ≤ (A + B).card ∧ (A + B).card ≤ ub ∧ A + B ⊆ S

/-- The set `S` contains a sumset `A + B` with `A, B ⊆ [n]` and `|A| = |B| = k`. -/
def exactPairEvent (n k : ℕ) (S : Finset ℕ) : Prop :=
  ∃ A B : Finset ℕ,
    A ⊆ interval n ∧ B ⊆ interval n ∧ A.card = k ∧ B.card = k ∧ A + B ⊆ S

/-- The set `S` contains a sumset `A + B` with `A, B ⊆ [n]` and `|A|, |B| ≥ k`. -/
def pairEvent (n k : ℕ) (S : Finset ℕ) : Prop :=
  ∃ A B : Finset ℕ,
    A ⊆ interval n ∧ B ⊆ interval n ∧ k ≤ A.card ∧ k ≤ B.card ∧ A + B ⊆ S

/-- There is `S ⊆ [n]` with `|S| ≥ δ n` that contains no sumset `A + B` with `A, B ⊆ [n]` and
`|A|, |B| ≥ k`. -/
def existsDenseSetWithoutLargeSumsets (n k : ℕ) (δ : unitInterval) : Prop :=
  ∃ S : Finset ℕ,
    S ⊆ interval n ∧ (δ : ℝ) * (n : ℝ) ≤ (S.card : ℝ) ∧ ¬ pairEvent n k S

/-- The property `P n δ` holds for all large `n` and every `δ` with `n ^ (-α) < δ ≤ 1 - c`. -/
def eventuallyForDensities (α c : ℝ) (P : ℕ → unitInterval → Prop) : Prop :=
  ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ),
    ∀ δ : unitInterval,
      Real.rpow (n : ℝ) (-α) < (δ : ℝ) → (δ : ℝ) ≤ 1 - c → P n δ

/-- The threshold `⌈c * log n / log (1 / δ)⌉`. -/
def pairCardThreshold (c : ℝ) (n : ℕ) (δ : unitInterval) : ℕ :=
  Nat.ceil (c * Real.log (n : ℝ) / Real.log (1 / δ))

/-- The constant `τ / log (1 / (1 - c)) + 1 / log 2`. If `δ ≤ 1 - c`, then
`pairCardThreshold τ n δ` is at most this constant times `log n`. -/
def densityCoefficient (τ c : ℝ) : ℝ :=
  τ / Real.log (1 / (1 - c)) + 1 / Real.log 2

private lemma log_one_div_pos {x : ℝ} (hx : 0 < x) (hx' : x < 1) : 0 < Real.log (1 / x) :=
  Real.log_pos (one_lt_one_div hx hx')

lemma densityCoefficient_gt_one {τ c : ℝ} (hτ_pos : 0 < τ)
    (hc_pos : 0 < c) (hc_lt : c < 1) :
    1 < densityCoefficient τ c := by
  rw [densityCoefficient]
  linarith [div_pos hτ_pos (log_one_div_pos (sub_pos.2 hc_lt) (sub_lt_self 1 hc_pos)),
    one_lt_one_div (Real.log_pos one_lt_two) log_two_lt_one]

lemma densityCoefficient_pos {τ c : ℝ} (hτ_pos : 0 < τ)
    (hc_pos : 0 < c) (hc_lt : c < 1) :
    0 < densityCoefficient τ c :=
  zero_lt_one.trans (densityCoefficient_gt_one hτ_pos hc_pos hc_lt)

lemma pairCardThreshold_le_densityCoefficient_mul_log {τ c : ℝ} {n : ℕ}
    {δ : unitInterval} (hτ_nonneg : 0 ≤ τ) (hc_pos : 0 < c) (hn_two : 2 ≤ n)
    (hδ_pos : 0 < (δ : ℝ)) (hδ_upper : (δ : ℝ) ≤ 1 - c) :
    (pairCardThreshold τ n δ : ℝ) ≤
      densityCoefficient τ c * Real.log (n : ℝ) := by
  have hc : (0 : ℝ) < 1 - c := hδ_pos.trans_le hδ_upper
  have hn : 0 ≤ τ * Real.log (n : ℝ) := mul_nonneg hτ_nonneg (Real.log_natCast_nonneg n)
  have hδ := log_one_div_pos hδ_pos (by linarith)
  rw [pairCardThreshold, densityCoefficient, add_mul, div_mul_eq_mul_div]
  refine (Nat.ceil_lt_add_one (div_nonneg hn hδ.le)).le.trans (add_le_add ?_ ?_)
  · exact div_le_div_of_nonneg_left hn (log_one_div_pos hc (by linarith))
      (Real.log_le_log (one_div_pos.2 hc) (one_div_le_one_div_of_le hδ_pos hδ_upper))
  · rw [one_div_mul_eq_div, le_div_iff₀ (Real.log_pos one_lt_two), one_mul]
    exact Real.log_le_log zero_lt_two (mod_cast hn_two)

/-- The exponent `γ / (8 * (γ + 3))` of `n` in the bound for the probability of `pairEvent`. -/
def pairEventDecayExponent (γ : ℝ) : ℝ := γ / (8 * (γ + 3))

end

end DenseSetsWithoutLargeSumsets
