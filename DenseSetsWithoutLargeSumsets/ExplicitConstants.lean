/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DenseSetsWithoutLargeSumsets.CountingSumsetsOfModerateSize.Probability
public import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.Constants
public import DenseSetsWithoutLargeSumsets.SimpleBoundForVeryLargeSumsets
import ChangFreimanRuzsa.ExponentBounds
import DenseSetsWithoutLargeSumsets.Combinatorics.SimpleGraph.TriangleRemovalBound
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Explicit constants for Theorems 1.1 and 1.3 and Corollary 1.2

The proofs of Theorems 1.1 and 1.3 and of Corollary 1.2 hold for densities above `n ^ (-α)` and
for `n` above a threshold, where `α` and the threshold are built from the constants of Chang's
theorem, of the theorem of Bollobás, Leader and Tiba and of the count of Green. This file bounds
them by simple expressions in `γ` and `c`:

* the exponent `α = γ / exp (exp (10 ^ 4 / c))`;
* the threshold `exp (exp (10 ^ 5 / c) / (γ * T) ^ 16)`, where `T` is the triangle removal constant
  `triangleRemovalBound (γ ^ 2 / exp (3 * 10 ^ 4 / c))` of Mathlib.

The constant of Bollobás, Leader and Tiba comes from the arithmetic removal lemma, so the threshold
has to involve the triangle removal constant, which is of tower type.

## Main definitions

* `explicitDensityExponent γ c`: the exponent `γ / exp (exp (10 ^ 4 / c))`.
* `explicitRemovalConstant γ c`: the constant `T`.
* `explicitLogThreshold γ c`: the logarithm `exp (10 ^ 5 / c) / (γ * T) ^ 16` of the threshold.

## Main statements

* `two_mul_explicitDensityExponent_le_lowerDensityExponent`,
  `two_mul_explicitDensityExponent_le_moderateSumsetDensityExponent`: twice the explicit exponent
  is below the exponents of the proofs.
* `lowerGapThreshold_lt_exp_explicitLogThreshold`,
  `veryLargeSumsetThreshold_le_exp_explicitLogThreshold`: the explicit threshold is above the
  thresholds of the proofs.
-/

@[expose] public section

namespace DenseSetsWithoutLargeSumsets

open Real

noncomputable section

/-- The exponent `γ / exp (exp (10 ^ 4 / c))` of the explicit forms of Theorems 1.1 and 1.3 and of
Corollary 1.2. -/
def explicitDensityExponent (γ c : ℝ) : ℝ := γ / exp (exp (10 ^ 4 / c))

/-- The triangle removal constant `triangleRemovalBound (γ ^ 2 / exp (3 * 10 ^ 4 / c))`, which
bounds the constant of Bollobás, Leader and Tiba. -/
def explicitRemovalConstant (γ c : ℝ) : ℝ :=
  SimpleGraph.triangleRemovalBound (γ ^ 2 / exp (3 * 10 ^ 4 / c))

/-- The logarithm `exp (10 ^ 5 / c) / (γ * T) ^ 16` of the threshold on `n`, where
`T = explicitRemovalConstant γ c`. -/
def explicitLogThreshold (γ c : ℝ) : ℝ :=
  exp (10 ^ 5 / c) / (γ * explicitRemovalConstant γ c) ^ 16

variable {γ c : ℝ}

/-! ### Elementary bounds -/

private lemma exp_le_exp_div {a : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (hc' : c < 1) :
    exp a ≤ exp (a / c) :=
  exp_le_exp.2 (le_div_self ha hc hc'.le)

private lemma two_pow_le_exp (n : ℕ) : (2 : ℝ) ^ n ≤ exp n := by
  rw [← exp_one_pow]
  exact pow_le_pow_left₀ two_pos.le (by linarith [add_one_le_exp (1 : ℝ)]) n

/-- `2 ^ n ≤ exp (n / c)` for `0 < c < 1`. -/
private lemma two_pow_le_exp_div (n : ℕ) (hc : 0 < c) (hc' : c < 1) :
    (2 : ℝ) ^ n ≤ exp (n / c) :=
  (two_pow_le_exp n).trans (exp_le_exp_div n.cast_nonneg hc hc')

private lemma le_exp_self (x : ℝ) : x ≤ exp x := by linarith [add_one_le_exp x]

private lemma two_le_exp_div {a : ℝ} (ha : 1 ≤ a) (hc : 0 < c) (hc' : c < 1) :
    2 ≤ exp (a / c) := by
  linarith [add_one_le_exp (a / c), le_div_self (by linarith : 0 ≤ a) hc hc'.le]

/-- `x ^ 2 ≤ exp (2 * a)` for `0 ≤ x ≤ exp a`. -/
private lemma sq_le_exp_two_mul {x a : ℝ} (hx : 0 ≤ x) (h : x ≤ exp a) : x ^ 2 ≤ exp (2 * a) := by
  rw [(by ring : 2 * a = (2 : ℕ) * a), exp_nat_mul]
  exact pow_le_pow_left₀ hx h 2

lemma densityCoefficient_le (hγ' : γ ≤ 1) (hc : 0 < c) (hc' : c < 1) :
    densityCoefficient (3 + γ) c ≤ 6 / c := by
  have h₁ : (3 + γ) / log (1 / (1 - c)) ≤ 4 / c :=
    div_le_div₀ (by norm_num) (by linarith) hc (le_log_one_div_one_sub hc')
  have h₂ : 1 / log 2 ≤ 2 / c := by
    rw [div_le_div_iff₀ (log_pos one_lt_two) hc]
    nlinarith [log_two_gt_d9]
  rw [densityCoefficient]
  linarith [(by ring : (6 : ℝ) / c = 4 / c + 2 / c)]

lemma moderateSumsetGapConstant_le (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c) (hc' : c < 1) :
    moderateSumsetGapConstant (1 + γ) c ≤ exp (576 / c) := by
  rw [moderateSumsetGapConstant, (by ring : 2 + (1 + γ) = 3 + γ), exp_le_exp,
    div_le_iff₀ (by linarith)]
  have h : 96 * densityCoefficient (3 + γ) c ≤ 576 / c := by
    linarith [densityCoefficient_le hγ' hc hc', (by ring : (576 : ℝ) / c = 96 * (6 / c))]
  nlinarith [mul_pos (div_pos (by norm_num : (0 : ℝ) < 576) hc) hγ]

lemma two_le_moderateSumsetGapConstant (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c) (hc' : c < 1) :
    2 ≤ moderateSumsetGapConstant (1 + γ) c := by
  rw [moderateSumsetGapConstant, (by ring : 2 + (1 + γ) = 3 + γ)]
  grw [← add_one_le_exp]
  rw [← sub_le_iff_le_add, le_div_iff₀ (by linarith)]
  nlinarith [densityCoefficient_gt_one (τ := 3 + γ) (by linarith) hc hc']

private lemma le_ε (hγ : 0 < γ) (hγ' : γ ≤ 1) : γ / 12 ≤ ε γ := by
  rw [ε]
  exact div_le_div_of_nonneg_left hγ.le (by positivity) (by linarith)

/-! ### The exponent -/

private lemma two_le_κ (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c) (hc' : c < 1) :
    2 ≤ κ (moderateSumsetGapConstant (1 + γ) c) := by
  rw [κ]
  nlinarith [two_le_moderateSumsetGapConstant hγ hγ' hc hc']

/-- The doubling constant `κ C` given to Chang's theorem is at most `6 * exp (1152 / c)`. -/
private lemma κ_le (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c) (hc' : c < 1) :
    κ (moderateSumsetGapConstant (1 + γ) c) ≤ 6 * exp (1152 / c) := by
  rw [κ, (by ring : (1152 : ℝ) / c = 2 * (576 / c))]
  grw [sq_le_exp_two_mul (by linarith [two_le_moderateSumsetGapConstant hγ hγ' hc hc'])
    (moderateSumsetGapConstant_le hγ hγ' hc hc')]

/-- The exponent of Chang's theorem in `lowerDensityExponent` is at most `exp (3500 / c)`. -/
private lemma containerExponent_κ_le (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c) (hc' : c < 1) :
    ChangFreimanRuzsa.containerExponent (κ (moderateSumsetGapConstant (1 + γ) c)) ≤
      exp (3500 / c) := by
  have hκ := two_le_κ hγ hγ' hc hc'
  grw [ChangFreimanRuzsa.containerExponent_le hκ, κ_le hγ hγ' hc hc']
  rw [mul_pow, ← mul_assoc, (by ring : (3500 : ℝ) / c = 44 / c + (3 : ℕ) * (1152 / c)), exp_add,
    exp_nat_mul]
  gcongr
  grw [(by norm_num : (2 : ℝ) * 10 ^ 8 * 6 ^ 3 ≤ 2 ^ 44)]
  exact_mod_cast two_pow_le_exp_div 44 hc hc'

/-- `150000 / c ≤ exp (3500 / c)`. -/
private lemma le_exp_div (hc : 0 < c) (hc' : c < 1) : 150000 / c ≤ exp (3500 / c) := by
  have ht := one_le_one_div hc hc'.le
  have h := quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 3500 / c)
  rw [(by ring : (3500 : ℝ) / c = 3500 * (1 / c)),
    (by ring : (150000 : ℝ) / c = 150000 * (1 / c))] at *
  nlinarith

private lemma moderateSumsetCardScale_le (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c) (hc' : c < 1) :
    moderateSumsetCardScale (1 + γ) c ≤ exp (150000 / c) := by
  refine max_le ?_ (max_le ?_ ?_)
  · rw [CountingSetsWithSmallSumset.smallSumsetClassCountThreshold_def, Nat.cast_pow,
      Nat.cast_ofNat]
    grw [two_pow_le_exp_div 9000 hc hc']
    gcongr
    norm_num
  · have h2C : 2 * moderateSumsetGapConstant (1 + γ) c ≤ exp (577 / c) := by
      rw [(by ring : (577 : ℝ) / c = 1 / c + 576 / c), exp_add]
      grw [← moderateSumsetGapConstant_le hγ hγ' hc hc']
      gcongr
      · linarith [two_le_moderateSumsetGapConstant hγ hγ' hc hc']
      · exact two_le_exp_div le_rfl hc hc'
    have hmax : max (2 * moderateSumsetGapConstant (1 + γ) c) (4 / (1 + γ)) ≤ exp (577 / c) :=
      max_le h2C ((div_le_self (by norm_num) (by linarith)).trans
        (by linarith [two_le_moderateSumsetGapConstant hγ hγ' hc hc']))
    grw [hmax]
    rw [← exp_mul, exp_le_exp, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hc]
    norm_num
  · have hbase : 49152 * densityCoefficient (2 + (1 + γ)) c / (1 + γ) ≤ exp (20 / c) := by
      have h19 : (2 : ℝ) ^ 19 ≤ exp (19 / c) := by exact_mod_cast two_pow_le_exp_div 19 hc hc'
      have hK : 49152 * densityCoefficient (3 + γ) c ≤ 2 ^ 19 * (1 / c) := by
        grw [densityCoefficient_le hγ' hc hc']
        rw [mul_one_div, mul_div_assoc', div_le_div_iff_of_pos_right hc]
        norm_num
      rw [(by ring : 2 + (1 + γ) = 3 + γ), div_le_iff₀ (by linarith),
        (by ring : (20 : ℝ) / c = 19 / c + 1 / c), exp_add]
      nlinarith [mul_le_mul h19 (le_exp_self (1 / c)) (by positivity) (exp_pos _).le,
        mul_nonneg (mul_pos (exp_pos (19 / c)) (exp_pos (1 / c))).le hγ.le]
    grw [hbase]
    · rw [← exp_mul, exp_le_exp, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hc]
      norm_num
    · exact div_nonneg (mul_nonneg (by norm_num)
        (densityCoefficient_pos (by linarith) hc hc').le) (by linarith)

private lemma div_le_lowerDensityExponent (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c) (hc' : c < 1) :
    γ / (2 * exp (exp (3500 / c))) ≤
      lowerDensityExponent (moderateSumsetGapConstant (1 + γ) c) γ := by
  set C := moderateSumsetGapConstant (1 + γ) c
  have hC₂ := two_le_moderateSumsetGapConstant hγ hγ' hc hc'
  rw [lowerDensityExponent, mul_comm, ← div_div]
  refine div_le_div_of_nonneg_right (le_min ?_ ?_) zero_le_two
  · have hε : (2 + γ) * ε γ = γ / 4 := by
      rw [ε]
      field_simp
      ring
    rw [hε, div_div]
    refine div_le_div_of_nonneg_left hγ.le (by positivity) ?_
    grw [sq_le_exp_two_mul (by linarith) (moderateSumsetGapConstant_le hγ hγ' hc hc'),
      ← le_exp_div hc hc']
    rw [(by ring : (150000 : ℝ) / c = 148848 / c + 2 * (576 / c)), exp_add, ← mul_assoc]
    gcongr
    linarith [le_exp_self (148848 / c), le_div_self (by norm_num : (0 : ℝ) ≤ 148848) hc hc'.le]
  · rw [div_le_div_iff₀ (exp_pos _) (by positivity)]
    nlinarith [exp_le_exp.2 (containerExponent_κ_le hγ hγ' hc hc'),
      exp_pos (ChangFreimanRuzsa.containerExponent (κ C))]

private lemma div_le_moderateSumsetDensityExponent (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c)
    (hc' : c < 1) :
    γ / (2 * exp (exp (3500 / c))) ≤ moderateSumsetDensityExponent (1 + γ) c := by
  rw [moderateSumsetDensityExponent]
  have hS : 0 < moderateSumsetCardScale (1 + γ) c :=
    (Nat.cast_pos.2 CountingSetsWithSmallSumset.smallSumsetClassCountThreshold_pos).trans_le
      (le_max_left _ _)
  grw [moderateSumsetCardScale_le hγ hγ' hc hc', le_exp_div hc hc']
  gcongr
  linarith

private lemma explicitDensityExponent_le_div (hγ : 0 < γ) (hc : 0 < c) (hc' : c < 1) :
    explicitDensityExponent γ c ≤ γ / (4 * exp (exp (3500 / c))) := by
  refine div_le_div_of_nonneg_left hγ.le (by positivity) ?_
  grw [(by nlinarith [quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] : (4 : ℝ) ≤ exp 2)]
  rw [← exp_add, exp_le_exp, (by ring : (10 : ℝ) ^ 4 / c = 3500 / c + 6500 / c), exp_add]
  nlinarith [two_le_exp_div (a := 3500) (by norm_num) hc hc',
    two_le_exp_div (a := 6500) (by norm_num) hc hc']

lemma explicitDensityExponent_pos (hγ : 0 < γ) : 0 < explicitDensityExponent γ c := by
  rw [explicitDensityExponent]
  positivity

lemma explicitDensityExponent_le_quarter (hγ : 0 < γ) (hc : 0 < c) (hc' : c < 1) :
    explicitDensityExponent γ c ≤ γ / 4 :=
  (explicitDensityExponent_le_div hγ hc hc').trans
    (div_le_div_of_nonneg_left hγ.le (by norm_num) (by nlinarith [one_le_exp (exp_pos
      (3500 / c)).le]))

private lemma two_mul_explicitDensityExponent_le (hγ : 0 < γ) (hc : 0 < c) (hc' : c < 1) :
    2 * explicitDensityExponent γ c ≤ γ / (2 * exp (exp (3500 / c))) := by
  linarith [explicitDensityExponent_le_div hγ hc hc',
    (by ring : γ / (4 * exp (exp (3500 / c))) = γ / (2 * exp (exp (3500 / c))) / 2)]

/-- Twice the explicit exponent is at most the exponent `lowerDensityExponent` of Lemma 2.1. -/
lemma two_mul_explicitDensityExponent_le_lowerDensityExponent (hγ : 0 < γ) (hγ' : γ ≤ 1)
    (hc : 0 < c) (hc' : c < 1) :
    2 * explicitDensityExponent γ c ≤
      lowerDensityExponent (moderateSumsetGapConstant (1 + γ) c) γ :=
  (two_mul_explicitDensityExponent_le hγ hc hc').trans (div_le_lowerDensityExponent hγ hγ' hc hc')

/-- Twice the explicit exponent is at most the exponent `moderateSumsetDensityExponent` of the
count of sumsets of moderate size. -/
lemma two_mul_explicitDensityExponent_le_moderateSumsetDensityExponent (hγ : 0 < γ) (hγ' : γ ≤ 1)
    (hc : 0 < c) (hc' : c < 1) :
    2 * explicitDensityExponent γ c ≤ moderateSumsetDensityExponent (1 + γ) c :=
  (two_mul_explicitDensityExponent_le hγ hc hc').trans
    (div_le_moderateSumsetDensityExponent hγ hγ' hc hc')

lemma two_mul_explicitDensityExponent_le_half (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c)
    (hc' : c < 1) : 2 * explicitDensityExponent γ c ≤ 1 / 2 := by
  linarith [explicitDensityExponent_le_quarter hγ hc hc']

/-! ### The constant of Bollobás, Leader and Tiba -/

lemma explicitRemovalConstant_pos (hγ : 0 < γ) : 0 < explicitRemovalConstant γ c :=
  SimpleGraph.triangleRemovalBound_pos (by positivity)

lemma explicitRemovalConstant_le_one (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c) :
    explicitRemovalConstant γ c ≤ 1 := by
  have h₀ : 0 < γ ^ 2 / exp (3 * 10 ^ 4 / c) := by positivity
  have h₁ : γ ^ 2 / exp (3 * 10 ^ 4 / c) ≤ 1 :=
    div_le_one_of_le₀ ((pow_le_one₀ hγ.le hγ').trans (one_le_exp (by positivity)))
      (exp_pos _).le
  rw [explicitRemovalConstant]
  grw [SimpleGraph.triangleRemovalBound_le_cube h₀]
  nlinarith [pow_le_one₀ h₀.le h₁ (n := 3)]

lemma mul_explicitRemovalConstant_le_one (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c) :
    γ * explicitRemovalConstant γ c ≤ 1 :=
  (mul_le_of_le_one_right hγ.le (explicitRemovalConstant_le_one hγ hγ' hc)).trans hγ'

open LargeSumsetsFromSubsets in
/-- The density parameter of Bollobás, Leader and Tiba is at least half the triangle removal
constant at `bltRho K e / bltCap K / (36 * (1 + 16 * bltCap K ^ 7) ^ 2)`. -/
private lemma triangleRemovalBound_le_two_mul_bltDelta {K e : ℝ} (hK : 1 ≤ K) (he : 0 < e)
    (he₁ : e ≤ 1) :
    SimpleGraph.triangleRemovalBound
        (bltRho K e / bltCap K / (36 * (1 + 16 * bltCap K ^ 7) ^ 2)) ≤ 2 * bltDelta K e := by
  have hcap := hundred_le_bltCap hK
  have hρ := bltRho_pos hK he
  have hρ₁ := bltRho_le hK he he₁
  have hη : 0 < bltRho K e / bltCap K / (36 * (1 + 16 * bltCap K ^ 7) ^ 2) := by positivity
  have hηρ : bltRho K e / bltCap K / (36 * (1 + 16 * bltCap K ^ 7) ^ 2) ≤ bltRho K e := by
    rw [div_div]
    refine div_le_self hρ.le (one_le_mul_of_one_le_of_one_le (by linarith) ?_)
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ bltCap K) 7]
  rw [← div_le_iff₀' two_pos, bltDelta, ArithmeticRemoval.removalConst_eq]
  push_cast
  refine le_min (le_min ?_ ?_) le_rfl <;>
    linarith [SimpleGraph.triangleRemovalBound_le_cube hη,
      pow_le_of_le_one hη.le (by linarith) (by norm_num : (3 : ℕ) ≠ 0)]

open LargeSumsetsFromSubsets in
/-- The constant `bltCap (4 * C)` of Bollobás, Leader and Tiba in Lemma 2.1 is at most
`exp (1741 / c)`, where `C = moderateSumsetGapConstant (1 + γ) c`. -/
private lemma bltCap_le (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c) (hc' : c < 1) :
    bltCap (4 * moderateSumsetGapConstant (1 + γ) c) ≤ exp (1741 / c) := by
  have hC₂ := two_le_moderateSumsetGapConstant hγ hγ' hc hc'
  rw [bltCap, (by ring : (1741 : ℝ) / c = 13 / c + (3 : ℕ) * (576 / c)), exp_add, exp_nat_mul]
  grw [← moderateSumsetGapConstant_le hγ hγ' hc hc']
  push_cast
  rw [mul_pow, ← mul_assoc]
  gcongr
  grw [(by norm_num : (100 : ℝ) * 4 ^ 3 ≤ 2 ^ 13)]
  exact_mod_cast two_pow_le_exp_div 13 hc hc'

open LargeSumsetsFromSubsets in
/-- The argument of the triangle removal constant in `bltDelta` is at least
`γ ^ 2 / exp (3 * 10 ^ 4 / c)`. -/
private lemma le_bltRho_div (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c) (hc' : c < 1) :
    γ ^ 2 / exp (3 * 10 ^ 4 / c) ≤
      bltRho (4 * moderateSumsetGapConstant (1 + γ) c) (ε γ / 2) /
        bltCap (4 * moderateSumsetGapConstant (1 + γ) c) /
          (36 * (1 + 16 * bltCap (4 * moderateSumsetGapConstant (1 + γ) c) ^ 7) ^ 2) := by
  set C := moderateSumsetGapConstant (1 + γ) c
  have hcap := hundred_le_bltCap (K := 4 * C)
    (by linarith [two_le_moderateSumsetGapConstant hγ hγ' hc hc'])
  rw [bltRho, Nat.cast_ofNat]
  set cap := bltCap (4 * C)
  have hA : cap ^ 2 * (1 + 16 * cap ^ 7) ^ 2 ≤ 289 * exp (27856 / c) := by
    rw [← mul_pow, (by ring : (27856 : ℝ) / c = (16 : ℕ) * (1741 / c)), exp_nat_mul,
      (by ring : 289 * exp (1741 / c) ^ 16 = (17 * exp (1741 / c) ^ 8) ^ 2)]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    nlinarith [one_le_pow₀ (n := 7) (by linarith : 1 ≤ cap),
      pow_le_pow_left₀ (by linarith) (bltCap_le hγ hγ' hc hc') 8]
  have hE : 36000 * 289 * 576 * exp (27856 / c) ≤ exp (3 * 10 ^ 4 / c) := by
    rw [(by ring : (3 * 10 ^ 4 : ℝ) / c = 2144 / c + 27856 / c), exp_add]
    gcongr
    grw [(by norm_num : (36000 : ℝ) * 289 * 576 ≤ 2 ^ 33),
      (by exact_mod_cast two_pow_le_exp_div 33 hc hc' : (2 : ℝ) ^ 33 ≤ exp (33 / c))]
    gcongr
    norm_num
  rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  calc _ = 36000 * γ ^ 2 * (cap ^ 2 * (1 + 16 * cap ^ 7) ^ 2) := by ring
    _ ≤ 36000 * (576 * (ε γ / 2) ^ 2) * (289 * exp (27856 / c)) := by
        gcongr
        nlinarith [le_ε hγ hγ']
    _ = (ε γ / 2) ^ 2 * (36000 * 289 * 576 * exp (27856 / c)) := by ring
    _ ≤ (ε γ / 2) ^ 2 * exp (3 * 10 ^ 4 / c) := by gcongr

open LargeSumsetsFromSubsets in
/-- The density parameter `bltDelta` of Bollobás, Leader and Tiba in Lemma 2.1 is at least
`3 / 8 * explicitRemovalConstant γ c`. -/
private lemma mul_explicitRemovalConstant_le_bltDelta (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c)
    (hc' : c < 1) :
    3 / 8 * explicitRemovalConstant γ c ≤
      bltDelta (4 * moderateSumsetGapConstant (1 + γ) c) (ε γ / 2) := by
  rw [explicitRemovalConstant]
  linarith [SimpleGraph.mul_triangleRemovalBound_le (by positivity) (le_bltRho_div hγ hγ' hc hc'),
    triangleRemovalBound_le_two_mul_bltDelta (K := 4 * moderateSumsetGapConstant (1 + γ) c)
      (by linarith [two_le_moderateSumsetGapConstant hγ hγ' hc hc']) (div_pos (ε_pos hγ) two_pos)
      (by linarith [ε_le_one_twelfth hγ hγ'])]

open LargeSumsetsFromSubsets in
/-- The sample constant of Bollobás, Leader and Tiba in Lemma 2.1 is at most
`331776 * C / (γ * T)`, where `C = moderateSumsetGapConstant (1 + γ) c` and
`T = explicitRemovalConstant γ c`. -/
private lemma mul_bltSampleConst_le (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c) (hc' : c < 1) :
    γ * explicitRemovalConstant γ c *
        bltSampleConst (4 * moderateSumsetGapConstant (1 + γ) c) (ε γ / 2) ≤
      331776 * moderateSumsetGapConstant (1 + γ) c := by
  have hK : 1 ≤ 4 * moderateSumsetGapConstant (1 + γ) c := by
    linarith [two_le_moderateSumsetGapConstant hγ hγ' hc hc']
  have he : 0 < ε γ / 2 := div_pos (ε_pos hγ) two_pos
  have hT := explicitRemovalConstant_pos (c := c) hγ
  have hS := bltSampleConst_pos hK he
  linarith [mul_bltDelta_mul_bltSampleConst hK he,
    mul_le_mul (by linarith [le_ε hγ hγ'] : γ / 24 ≤ ε γ / 2)
      (mul_le_mul_of_nonneg_right (mul_explicitRemovalConstant_le_bltDelta hγ hγ' hc hc') hS.le)
      (by positivity) he.le]

open LargeSumsetsFromSubsets in
private lemma originalBltConstant_two_mul_eq {C e : ℝ} (hC : 1 ≤ 2 * C) (he : e ≤ 1) :
    originalBltConstant (2 * C) e = bltSampleConst (4 * C) (e / 2) := by
  rw [originalBltConstant]
  push_cast
  rw [max_eq_left hC, min_eq_left he, ← mul_assoc]
  norm_num

open LargeSumsetsFromSubsets in
/-- The constant of Bollobás, Leader and Tiba in Lemma 2.1 is at most
`10 ^ 12 * C ^ 2 / (γ * T) ^ 2`, where `C = moderateSumsetGapConstant (1 + γ) c` and
`T = explicitRemovalConstant γ c`. -/
private lemma lowerBltConstant_le (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c) (hc' : c < 1) :
    lowerBltConstant (moderateSumsetGapConstant (1 + γ) c) γ ≤
      10 ^ 12 * moderateSumsetGapConstant (1 + γ) c ^ 2 /
        (γ * explicitRemovalConstant γ c) ^ 2 := by
  set C := moderateSumsetGapConstant (1 + γ) c
  set T := explicitRemovalConstant γ c
  set S := bltSampleConst (4 * C) (ε γ / 2)
  have hC₂ := two_le_moderateSumsetGapConstant hγ hγ' hc hc'
  have hT := explicitRemovalConstant_pos (c := c) hγ
  have hm : (max 1 S + 2 * C + 1) * (γ * T) ≤ 331780 * C := by
    nlinarith [mul_le_mul_of_nonneg_right
      (max_le_add_of_nonneg zero_le_one (bltSampleConst_pos (K := 4 * C) (by linarith)
        (div_pos (ε_pos hγ) two_pos)).le)
      (by positivity : (0 : ℝ) ≤ γ * T), mul_bltSampleConst_le hγ hγ' hc hc',
      mul_explicitRemovalConstant_le_one hγ hγ' hc]
  rw [lowerBltConstant, bltConstant,
    originalBltConstant_two_mul_eq (by linarith) (by linarith [ε_le_one_twelfth hγ hγ']),
    le_div_iff₀ (by positivity)]
  nlinarith [mul_self_le_mul_self (by positivity) hm]

/-! ### The exponent of Chang's theorem -/

private lemma changExponent_nonneg (C : ℝ) : 0 ≤ changExponent C := by
  have hκ : 0 ≤ κ C := by rw [κ]; positivity
  have h := (sq_nonneg (κ C)).trans (ChangFreimanRuzsa.sq_le_containerExponent hκ)
  rw [changExponent, ChangFreimanRuzsa.freimanDimExponent]
  linarith [ChangFreimanRuzsa.properizationExponent_nonneg h,
    ChangFreimanRuzsa.coordinateReductionExponent_nonneg h]

/-- The exponent `changExponent C` of Lemma 2.1 is at most `exp (8200 / c)`. -/
private lemma changExponent_le (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c) (hc' : c < 1) :
    changExponent (moderateSumsetGapConstant (1 + γ) c) ≤ exp (8200 / c) := by
  set C := moderateSumsetGapConstant (1 + γ) c
  have hκ := two_le_κ hγ hγ' hc hc'
  have h₁ := ChangFreimanRuzsa.containerExponent_add_two_pow_mul_log_le hκ
  have h₂ := ChangFreimanRuzsa.containerExponent_le hκ
  have hX : changExponent C ≤ 529 * 10 ^ 27 * κ C ^ 7 := by
    rw [changExponent, ChangFreimanRuzsa.freimanDimExponent,
      ChangFreimanRuzsa.properizationExponent, ChangFreimanRuzsa.coordinateReductionExponent]
    linarith [pow_nonneg (by linarith : (0 : ℝ) ≤ κ C) 3,
      pow_le_pow_right₀ (by linarith : 1 ≤ κ C) (by norm_num : 3 ≤ 7)]
  grw [hX, κ_le hγ hγ' hc hc']
  rw [mul_pow, ← mul_assoc, (by ring : (8200 : ℝ) / c = 136 / c + (7 : ℕ) * (1152 / c)), exp_add,
    exp_nat_mul]
  gcongr
  grw [(by norm_num : (529 : ℝ) * 10 ^ 27 * 6 ^ 7 ≤ 2 ^ 136)]
  exact_mod_cast two_pow_le_exp_div 136 hc hc'

/-! ### The threshold -/

/-- `log (x * y * z) ≤ x + log y + z` for `x, y, z ≥ 1`, and the logarithm is nonnegative. -/
private lemma log_mul_mul_le {x y z : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) :
    0 ≤ log (x * y * z) ∧ log (x * y * z) ≤ x + log y + z := by
  refine ⟨log_nonneg (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hx hy) hz),
    ?_⟩
  rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity)]
  linarith [log_le_self (by linarith : (0 : ℝ) ≤ x), log_le_self (by linarith : (0 : ℝ) ≤ z)]

/-- If `1 ≤ s ≤ a * V`, `1 ≤ m ≤ b * V` and `1 ≤ L` with `log L ≤ 5 * V`, then
`s * log (m * L * s)` is nonnegative and at most `a * (a + b + 5) * V ^ 2`. -/
private lemma mul_log_mul_mul_le {s m L V a b : ℝ} (hs : 1 ≤ s) (hm : 1 ≤ m) (hL : 1 ≤ L)
    (hsV : s ≤ a * V) (hmV : m ≤ b * V) (hLV : log L ≤ 5 * V) :
    0 ≤ s * log (m * L * s) ∧ s * log (m * L * s) ≤ a * (a + b + 5) * V ^ 2 := by
  obtain ⟨h₀, h₁⟩ := log_mul_mul_le hm hL hs
  refine ⟨mul_nonneg (by linarith) h₀, ?_⟩
  calc s * log (m * L * s) ≤ (a * V) * ((a + b + 5) * V) :=
        mul_le_mul hsV (by linarith) h₀ (by linarith)
    _ = a * (a + b + 5) * V ^ 2 := by ring

/-- The scale `(lowerBltConstant C γ + changExponent C) / (γ * c)`, which bounds the scales of the
conditions on `n` in `lowerGapThreshold C γ c`. -/
private def lowerGapScale (C γ c : ℝ) : ℝ := (lowerBltConstant C γ + changExponent C) / (γ * c)

variable {C : ℝ}

private lemma lowerBltConstant_div_le_lowerGapScale (hγ : 0 < γ) (hc : 0 < c) :
    lowerBltConstant C γ / (γ * c) ≤ lowerGapScale C γ c :=
  div_le_div_of_nonneg_right (le_add_of_nonneg_right (changExponent_nonneg C)) (by positivity)

private lemma lowerBltConstant_le_lowerGapScale (hC : 1 ≤ C) (hγ : 0 < γ) (hγ' : γ ≤ 1)
    (hc : 0 < c) (hc' : c < 1) : lowerBltConstant C γ ≤ lowerGapScale C γ c :=
  (le_div_self (by linarith [one_le_lowerBltConstant (by linarith : 0 < 2 * C) γ])
    (by positivity) ((mul_le_of_le_one_left hc.le hγ').trans hc'.le)).trans
    (lowerBltConstant_div_le_lowerGapScale hγ hc)

private lemma one_div_le_lowerGapScale (hC : 1 ≤ C) (hγ : 0 < γ) (hc : 0 < c) :
    1 / (γ * c) ≤ lowerGapScale C γ c :=
  (div_le_div_of_nonneg_right (one_le_lowerBltConstant (by linarith) γ) (by positivity)).trans
    (lowerBltConstant_div_le_lowerGapScale hγ hc)

private lemma one_le_lowerGapScale (hC : 1 ≤ C) (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c)
    (hc' : c < 1) : 1 ≤ lowerGapScale C γ c :=
  (one_le_one_div (by positivity) ((mul_le_of_le_one_left hc.le hγ').trans hc'.le)).trans
    (one_div_le_lowerGapScale hC hγ hc)

private lemma changExponent_le_lowerGapScale (hC : 1 ≤ C) (hγ : 0 < γ) (hγ' : γ ≤ 1)
    (hc : 0 < c) (hc' : c < 1) : changExponent C ≤ lowerGapScale C γ c := by
  have hB := one_le_lowerBltConstant (by linarith : 0 < 2 * C) γ
  exact (le_div_self (changExponent_nonneg C) (by positivity)
    ((mul_le_of_le_one_left hc.le hγ').trans hc'.le)).trans
    (div_le_div_of_nonneg_right (le_add_of_nonneg_left (by linarith)) (by positivity))

private lemma densityCoefficient_le_lowerGapScale (hC : 1 ≤ C) (hγ : 0 < γ) (hγ' : γ ≤ 1)
    (hc : 0 < c) (hc' : c < 1) : densityCoefficient (3 + γ) c ≤ 6 * lowerGapScale C γ c := by
  calc densityCoefficient (3 + γ) c ≤ 6 * (1 / c) := by
        linarith [densityCoefficient_le hγ' hc hc', (by ring : (6 : ℝ) / c = 6 * (1 / c))]
    _ ≤ 6 * (1 / (γ * c)) := by grw [mul_le_of_le_one_left hc.le hγ']
    _ ≤ 6 * lowerGapScale C γ c := by grw [one_div_le_lowerGapScale hC hγ hc]

private lemma lowerLogScale_le_lowerGapScale (hC : 1 ≤ C) (hγ : 0 < γ) (hγ' : γ ≤ 1)
    (hc : 0 < c) (hc' : c < 1) : lowerLogScale γ ≤ 96 * lowerGapScale C γ c := by
  calc lowerLogScale γ ≤ 8 / (γ / 12) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (le_ε hγ hγ')
    _ = 96 * (1 / γ) := by ring
    _ ≤ 96 * (1 / (γ * c)) := by grw [mul_le_of_le_one_right hγ.le hc'.le]
    _ ≤ 96 * lowerGapScale C γ c := by grw [one_div_le_lowerGapScale hC hγ hc]

private lemma lowerSqrtScale_le_lowerGapScale (hC : 1 ≤ C) (hγ : 0 < γ) (hγ' : γ ≤ 1)
    (hc : 0 < c) (hc' : c < 1) : lowerSqrtScale C γ ≤ 384 * lowerGapScale C γ c := by
  have hB := one_le_lowerBltConstant (by linarith : 0 < 2 * C) γ
  calc lowerSqrtScale C γ ≤ 8 * lowerBltConstant C γ * 4 / (γ / 12) := by
        refine div_le_div₀ (by positivity) ?_ (by positivity) (le_ε hγ hγ')
        gcongr
        exact (sqrt_le_left (by norm_num)).2 (by norm_num)
    _ = 384 * (lowerBltConstant C γ / γ) := by ring
    _ ≤ 384 * (lowerBltConstant C γ / (γ * c)) := by grw [mul_le_of_le_one_right hγ.le hc'.le]
    _ ≤ 384 * lowerGapScale C γ c := by grw [lowerBltConstant_div_le_lowerGapScale hγ hc]

private lemma lowerGapSqrtScale_le_lowerGapScale (hC : 1 ≤ C) (hγ : 0 < γ) (hγ' : γ ≤ 1)
    (hc : 0 < c) (hc' : c < 1) : lowerGapSqrtScale C γ c ≤ 288 * lowerGapScale C γ c := by
  have hB := one_le_lowerBltConstant (by linarith : 0 < 2 * C) γ
  have hK := densityCoefficient_le hγ' hc hc'
  calc lowerGapSqrtScale C γ c ≤ 8 * lowerBltConstant C γ * (3 / c) / (γ / 12) := by
        refine div_le_div₀ (by positivity) ?_ (by positivity) (le_ε hγ hγ')
        gcongr
        refine (sqrt_le_left (by positivity)).2 (hK.trans ?_)
        rw [div_pow, div_le_div_iff₀ hc (by positivity)]
        nlinarith [mul_pos hc (sub_pos.2 hc')]
    _ = 288 * (lowerBltConstant C γ / (γ * c)) := by ring
    _ ≤ 288 * lowerGapScale C γ c := by grw [lowerBltConstant_div_le_lowerGapScale hγ hc]

private lemma one_le_lowerSqrtScale (hC : 1 ≤ C) (hγ : 0 < γ) (hγ' : γ ≤ 1) :
    1 ≤ lowerSqrtScale C γ := by
  have hB := one_le_lowerBltConstant (by linarith : 0 < 2 * C) γ
  rw [lowerSqrtScale, le_div_iff₀ (ε_pos hγ)]
  nlinarith [ε_le_one_twelfth hγ hγ', mul_le_mul hB (one_le_sqrt.2 (by norm_num : (1 : ℝ) ≤ 14))
    zero_le_one (by linarith)]

private lemma one_le_lowerGapSqrtScale (hC : 1 ≤ C) (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c)
    (hc' : c < 1) : 1 ≤ lowerGapSqrtScale C γ c := by
  have hB := one_le_lowerBltConstant (by linarith : 0 < 2 * C) γ
  rw [lowerGapSqrtScale, le_div_iff₀ (ε_pos hγ)]
  nlinarith [ε_le_one_twelfth hγ hγ', mul_le_mul hB
    (one_le_sqrt.2 (densityCoefficient_gt_one (τ := 3 + γ) (by linarith) hc hc').le) zero_le_one
    (by linarith)]

private lemma log_lowerConstant_le_lowerGapScale (hC : 1 ≤ C) (hγ : 0 < γ) (hγ' : γ ≤ 1)
    (hc : 0 < c) (hc' : c < 1) : log (lowerConstant C γ) ≤ 5 * lowerGapScale C γ c := by
  have hB := one_le_lowerBltConstant (by linarith : 0 < 2 * C) γ
  have hle : lowerConstant C γ ≤ exp (changExponent C) * (4 * lowerBltConstant C γ) := by
    rw [lowerConstant]
    exact max_le (le_mul_of_one_le_right (exp_pos _).le (by linarith))
      (le_mul_of_one_le_left (by linarith) (one_le_exp (changExponent_nonneg C)))
  grw [hle]
  · rw [log_mul (exp_pos _).ne' (by positivity), log_exp]
    linarith [log_le_self (by positivity : (0 : ℝ) ≤ 4 * lowerBltConstant C γ),
      changExponent_le_lowerGapScale hC hγ hγ' hc hc',
      lowerBltConstant_le_lowerGapScale hC hγ hγ' hc hc']
  · exact lowerConstant_pos C γ

/-- The quantities `2 * lowerLogScale γ * log (m * lowerConstant C γ * lowerLogScale γ)` in
`lowerGapThreshold C γ c` are at most `10 ^ 12 * V ^ 4`, where `V = lowerGapScale C γ c`. -/
private lemma two_mul_lowerLogScale_mul_log_le (hC : 1 ≤ C) (hγ : 0 < γ) (hγ' : γ ≤ 1)
    (hc : 0 < c) (hc' : c < 1) {m : ℝ} (hm : 1 ≤ m) (hmV : m ≤ 60 * lowerGapScale C γ c) :
    2 * lowerLogScale γ * log (m * lowerConstant C γ * lowerLogScale γ) ≤
      10 ^ 12 * lowerGapScale C γ c ^ 4 := by
  have hV := one_le_lowerGapScale hC hγ hγ' hc hc'
  have hLs : 1 ≤ lowerLogScale γ := by
    rw [lowerLogScale, le_div_iff₀ (ε_pos hγ)]
    linarith [ε_le_one_twelfth hγ hγ']
  obtain ⟨-, h⟩ := mul_log_mul_mul_le hLs hm (one_le_lowerConstant (by linarith) γ)
    (lowerLogScale_le_lowerGapScale hC hγ hγ' hc hc') hmV
    (log_lowerConstant_le_lowerGapScale hC hγ hγ' hc hc')
  nlinarith [pow_le_pow_right₀ hV (by norm_num : 2 ≤ 4)]

/-- The quantities `(4 * s * log (m * lowerConstant C γ * s)) ^ 2` in `lowerGapThreshold C γ c`
are at most `10 ^ 12 * V ^ 4`, where `V = lowerGapScale C γ c`. -/
private lemma four_mul_mul_log_sq_le (hC : 1 ≤ C) (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c)
    (hc' : c < 1) {s m : ℝ} (hs : 1 ≤ s) (hsV : s ≤ 384 * lowerGapScale C γ c) (hm : 1 ≤ m)
    (hmV : m ≤ 120 * lowerGapScale C γ c) :
    (4 * s * log (m * lowerConstant C γ * s)) ^ 2 ≤ 10 ^ 12 * lowerGapScale C γ c ^ 4 := by
  have hV := one_le_lowerGapScale hC hγ hγ' hc hc'
  obtain ⟨h₀, h⟩ := mul_log_mul_mul_le hs hm (one_le_lowerConstant (by linarith) γ) hsV hmV
    (log_lowerConstant_le_lowerGapScale hC hγ hγ' hc hc')
  calc (4 * s * log (m * lowerConstant C γ * s)) ^ 2 =
        16 * (s * log (m * lowerConstant C γ * s)) ^ 2 := by ring
    _ ≤ 16 * (384 * (384 + 120 + 5) * lowerGapScale C γ c ^ 2) ^ 2 := by gcongr
    _ ≤ 10 ^ 12 * lowerGapScale C γ c ^ 4 := by
        nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ lowerGapScale C γ c) 4]

/-- The quantities `(a * exp (changExponent C)) ^ 2` in `lowerGapThreshold C γ c` are at most
`exp (10 ^ 12 * V ^ 4)` for `0 ≤ a ≤ 36 * V`, where `V = lowerGapScale C γ c`. -/
private lemma sq_mul_exp_changExponent_le (hC : 1 ≤ C) (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c)
    (hc' : c < 1) {a : ℝ} (ha : 0 ≤ a) (haV : a ≤ 36 * lowerGapScale C γ c) :
    (a * exp (changExponent C)) ^ 2 ≤ exp (10 ^ 12 * lowerGapScale C γ c ^ 4) := by
  have hV := one_le_lowerGapScale hC hγ hγ' hc hc'
  grw [haV, le_exp_self (36 * lowerGapScale C γ c)]
  rw [← exp_add, ← exp_nat_mul, exp_le_exp]
  push_cast
  linarith [changExponent_le_lowerGapScale hC hγ hγ' hc hc', le_self_pow₀ hV (by norm_num : 4 ≠ 0)]

/-- The threshold `lowerAnalyticThreshold C γ` is at most `exp (10 ^ 12 * V ^ 4)`, where
`V = lowerGapScale C γ c`. -/
private lemma lowerAnalyticThreshold_le (hC : 1 ≤ C) (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c)
    (hc' : c < 1) : lowerAnalyticThreshold C γ ≤ exp (10 ^ 12 * lowerGapScale C γ c ^ 4) := by
  have hV := one_le_lowerGapScale hC hγ hγ' hc hc'
  have hV₄ : lowerGapScale C γ c ≤ lowerGapScale C γ c ^ 4 := le_self_pow₀ hV (by norm_num)
  rw [lowerAnalyticThreshold, exp_le_exp]
  refine max_le ?_ (max_le ?_ (max_le ?_ ?_))
  · linarith [log_le_self (by norm_num : (0 : ℝ) ≤ 56)]
  · linarith [changExponent_le_lowerGapScale hC hγ hγ' hc hc']
  · exact two_mul_lowerLogScale_mul_log_le hC hγ hγ' hc hc' (by norm_num) (by linarith)
  · exact four_mul_mul_log_sq_le hC hγ hγ' hc hc' (one_le_lowerSqrtScale hC hγ hγ')
      (lowerSqrtScale_le_lowerGapScale hC hγ hγ' hc hc') (by norm_num) (by linarith)

/-- The threshold `lowerSizeThreshold C γ` is at most `exp (10 ^ 12 * V ^ 4)`, where
`V = lowerGapScale C γ c`. -/
private lemma lowerSizeThreshold_le (hC : 1 ≤ C) (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c)
    (hc' : c < 1) : lowerSizeThreshold C γ ≤ exp (10 ^ 12 * lowerGapScale C γ c ^ 4) := by
  have hV := one_le_lowerGapScale hC hγ hγ' hc hc'
  rw [lowerSizeThreshold]
  refine max_le ?_ (max_le ?_ (max_le ?_ (lowerAnalyticThreshold_le hC hγ hγ' hc hc')))
  · grw [← one_le_exp (by positivity : (0 : ℝ) ≤ 10 ^ 12 * lowerGapScale C γ c ^ 4),
      lowerDensityExponent, min_le_left]
    rw [div_div, div_le_one (by positivity)]
    nlinarith [ε_le_one_twelfth hγ hγ', ε_pos hγ, one_le_pow₀ (n := 2) hC]
  · linarith [add_one_le_exp (10 ^ 12 * lowerGapScale C γ c ^ 4), one_le_pow₀ (n := 4) hV]
  · exact sq_mul_exp_changExponent_le hC hγ hγ' hc hc' (by norm_num) (by linarith)

/-- The threshold `lowerGapThreshold C γ c` of Lemma 2.1 is at most `exp (10 ^ 12 * V ^ 4)`, where
`V = lowerGapScale C γ c`. -/
private lemma lowerGapThreshold_le (hC : 1 ≤ C) (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c)
    (hc' : c < 1) : lowerGapThreshold C γ c ≤ exp (10 ^ 12 * lowerGapScale C γ c ^ 4) := by
  have hV := one_le_lowerGapScale hC hγ hγ' hc hc'
  have hK := densityCoefficient_le_lowerGapScale hC hγ hγ' hc hc'
  have hM : max 42 (3 * densityCoefficient (3 + γ) c) ≤ 60 * lowerGapScale C γ c :=
    max_le (by linarith) (by linarith)
  have hM₁ : (1 : ℝ) ≤ max 42 (3 * densityCoefficient (3 + γ) c) := le_max_of_le_left (by norm_num)
  rw [lowerGapThreshold]
  refine max_le (lowerSizeThreshold_le hC hγ hγ' hc hc') (max_le ?_ (exp_le_exp.2 (max_le ?_ ?_)))
  · exact sq_mul_exp_changExponent_le hC hγ hγ' hc hc'
      (by linarith [densityCoefficient_gt_one (τ := 3 + γ) (by linarith) hc hc']) (by linarith)
  · exact two_mul_lowerLogScale_mul_log_le hC hγ hγ' hc hc' hM₁ hM
  · exact four_mul_mul_log_sq_le hC hγ hγ' hc hc' (one_le_lowerGapSqrtScale hC hγ hγ' hc hc')
      (by linarith [lowerGapSqrtScale_le_lowerGapScale hC hγ hγ' hc hc']) (by linarith)
      (by linarith)

/-- The scale `lowerGapScale C γ c` for `C = moderateSumsetGapConstant (1 + γ) c` is at most
`2 * 10 ^ 12 * exp (8201 / c) / (γ * T) ^ 3`, where `T = explicitRemovalConstant γ c`. -/
private lemma lowerGapScale_le (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c) (hc' : c < 1) :
    lowerGapScale (moderateSumsetGapConstant (1 + γ) c) γ c ≤
      2 * 10 ^ 12 * exp (8201 / c) / (γ * explicitRemovalConstant γ c) ^ 3 := by
  have hT := explicitRemovalConstant_pos (c := c) hγ
  have hD₁ := mul_explicitRemovalConstant_le_one hγ hγ' hc
  have hC : moderateSumsetGapConstant (1 + γ) c ^ 2 ≤ exp (8200 / c) := by
    grw [sq_le_exp_two_mul (by linarith [two_le_moderateSumsetGapConstant hγ hγ' hc hc'])
      (moderateSumsetGapConstant_le hγ hγ' hc hc'), mul_div_assoc']
    gcongr
    norm_num
  have hBX : lowerBltConstant (moderateSumsetGapConstant (1 + γ) c) γ +
      changExponent (moderateSumsetGapConstant (1 + γ) c) ≤
        2 * 10 ^ 12 * exp (8200 / c) / (γ * explicitRemovalConstant γ c) ^ 2 := by
    have hB := lowerBltConstant_le hγ hγ' hc hc'
    rw [le_div_iff₀ (by positivity)] at hB ⊢
    linarith [changExponent_le hγ hγ' hc hc', exp_pos (8200 / c),
      mul_le_of_le_one_right (changExponent_nonneg (moderateSumsetGapConstant (1 + γ) c))
        (pow_le_one₀ (by positivity) hD₁ (n := 2))]
  calc lowerGapScale (moderateSumsetGapConstant (1 + γ) c) γ c =
        (lowerBltConstant (moderateSumsetGapConstant (1 + γ) c) γ +
          changExponent (moderateSumsetGapConstant (1 + γ) c)) * (1 / γ) * (1 / c) := by
        rw [lowerGapScale]
        ring
    _ ≤ 2 * 10 ^ 12 * exp (8200 / c) / (γ * explicitRemovalConstant γ c) ^ 2 *
        (1 / (γ * explicitRemovalConstant γ c)) * exp (1 / c) :=
        mul_le_mul (mul_le_mul hBX (one_div_le_one_div_of_le (by positivity)
          (mul_le_of_le_one_right hγ.le (explicitRemovalConstant_le_one hγ hγ' hc)))
          (by positivity) (by positivity)) (le_exp_self _) (by positivity) (by positivity)
    _ = 2 * 10 ^ 12 * exp (8201 / c) / (γ * explicitRemovalConstant γ c) ^ 3 := by
        rw [(by ring : (8201 : ℝ) / c = 8200 / c + 1 / c), exp_add]
        ring

/-- `16 * 10 ^ 60 * exp (8201 / c) ^ 4 < exp (10 ^ 5 / c)` for `0 < c < 1`. -/
private lemma mul_exp_pow_lt (hc : 0 < c) (hc' : c < 1) :
    16 * 10 ^ 60 * exp (8201 / c) ^ 4 < exp (10 ^ 5 / c) := by
  calc 16 * 10 ^ 60 * exp (8201 / c) ^ 4 ≤ 2 ^ 204 * exp (8201 / c) ^ 4 := by
        gcongr
        norm_num
    _ ≤ exp ((204 : ℕ) / c) * exp (8201 / c) ^ 4 := by grw [two_pow_le_exp_div 204 hc hc']
    _ = exp (33008 / c) := by
        rw [← exp_nat_mul, ← exp_add]
        congr 1
        push_cast
        ring
    _ < exp (10 ^ 5 / c) := exp_lt_exp.2 ((div_lt_div_iff_of_pos_right hc).2 (by norm_num))

/-- `10 ^ 9 / (γ ^ 3 * c ^ 2)` is at most the logarithm of the explicit threshold. -/
lemma div_le_explicitLogThreshold (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c) (hc' : c < 1) :
    10 ^ 9 / (γ ^ 3 * c ^ 2) ≤ explicitLogThreshold γ c := by
  have hT := explicitRemovalConstant_pos (c := c) hγ
  have hT₁ := explicitRemovalConstant_le_one hγ hγ' hc
  have hD : (γ * explicitRemovalConstant γ c) ^ 16 ≤ γ ^ 3 :=
    (pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_right hγ.le hT₁) 16).trans
      (pow_le_pow_of_le_one hγ.le hγ' (by norm_num))
  rw [explicitLogThreshold, (by ring : 10 ^ 9 / (γ ^ 3 * c ^ 2) = 10 ^ 9 / c ^ 2 / γ ^ 3)]
  refine div_le_div₀ (exp_pos _).le ?_ (by positivity) hD
  calc 10 ^ 9 / c ^ 2 ≤ (10 ^ 5 / c) ^ 2 / 2 := by
        rw [div_pow, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg c]
    _ ≤ exp (10 ^ 5 / c) := by
        linarith [quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 10 ^ 5 / c),
          (by positivity : (0 : ℝ) ≤ 10 ^ 5 / c)]

/-- The threshold `lowerGapThreshold` of Lemma 2.1 is below the explicit threshold. -/
lemma lowerGapThreshold_lt_exp_explicitLogThreshold (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c)
    (hc' : c < 1) :
    lowerGapThreshold (moderateSumsetGapConstant (1 + γ) c) γ c <
      exp (explicitLogThreshold γ c) := by
  have hC := two_le_moderateSumsetGapConstant hγ hγ' hc hc'
  have hD : 0 < γ * explicitRemovalConstant γ c := mul_pos hγ (explicitRemovalConstant_pos hγ)
  grw [lowerGapThreshold_le (by linarith) hγ hγ' hc hc', exp_lt_exp]
  calc 10 ^ 12 * lowerGapScale (moderateSumsetGapConstant (1 + γ) c) γ c ^ 4
      ≤ 10 ^ 12 * (2 * 10 ^ 12 * exp (8201 / c) / (γ * explicitRemovalConstant γ c) ^ 3) ^ 4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans
          (one_le_lowerGapScale (by linarith) hγ hγ' hc hc')) (lowerGapScale_le hγ hγ' hc hc') 4)
          (by norm_num)
    _ = 16 * 10 ^ 60 * exp (8201 / c) ^ 4 / (γ * explicitRemovalConstant γ c) ^ 12 := by ring
    _ < exp (10 ^ 5 / c) / (γ * explicitRemovalConstant γ c) ^ 12 := by
        gcongr
        exact mul_exp_pow_lt hc hc'
    _ ≤ explicitLogThreshold γ c :=
        div_le_div_of_nonneg_left (exp_pos _).le (by positivity)
          (pow_le_pow_of_le_one hD.le (mul_explicitRemovalConstant_le_one hγ hγ' hc) (by norm_num))

/-- The threshold `veryLargeSumsetThreshold` of the count of very large sumsets is below the
explicit threshold. -/
lemma veryLargeSumsetThreshold_le_exp_explicitLogThreshold (hγ : 0 < γ) (hγ' : γ ≤ 1)
    (hc : 0 < c) (hc' : c < 1) :
    veryLargeSumsetThreshold γ c ≤ exp (explicitLogThreshold γ c) := by
  have hK₁ := densityCoefficient_gt_one (τ := 3 + γ) (by linarith) hc hc'
  have hγc₁ : γ * c ≤ 1 := (mul_le_of_le_one_left hc.le hγ').trans hc'.le
  have hx : (18 * densityCoefficient (3 + γ) c / γ) ^ (36 / γ) ≤ exp (3888 / (γ ^ 2 * c)) := by
    rw [rpow_def_of_pos (by positivity), exp_le_exp]
    have h₁ : log (18 * densityCoefficient (3 + γ) c / γ) ≤ 108 / (γ * c) := by
      refine (log_le_self (by positivity)).trans ?_
      rw [div_le_div_iff₀ hγ (by positivity)]
      linarith [mul_le_mul_of_nonneg_left ((le_div_iff₀ hc).1 (densityCoefficient_le hγ' hc hc'))
        (by positivity : (0 : ℝ) ≤ 18 * γ)]
    grw [h₁]
    apply le_of_eq
    field_simp
    ring
  have hy : 1 + 3888 / (γ ^ 2 * c) ≤ 10 ^ 9 / (γ ^ 3 * c ^ 2) := by
    have h₁ : γ ^ 3 * c ^ 2 ≤ γ ^ 2 * c := by
      rw [(by ring : γ ^ 3 * c ^ 2 = γ ^ 2 * c * (γ * c))]
      exact mul_le_of_le_one_right (by positivity) hγc₁
    have h₂ : 1 ≤ 1 / (γ ^ 3 * c ^ 2) :=
      one_le_one_div (by positivity) ((mul_le_of_le_one_left (by positivity)
        (pow_le_one₀ hγ.le hγ')).trans (pow_le_one₀ hc.le hc'.le))
    calc 1 + 3888 / (γ ^ 2 * c) ≤ 1 / (γ ^ 3 * c ^ 2) + 3888 / (γ ^ 3 * c ^ 2) :=
          add_le_add h₂ (div_le_div_of_nonneg_left (by norm_num) (by positivity) h₁)
      _ ≤ 10 ^ 9 / (γ ^ 3 * c ^ 2) := by
          rw [← add_div]
          gcongr
          norm_num
  rw [veryLargeSumsetThreshold]
  calc (⌈(18 * densityCoefficient (3 + γ) c / γ) ^ (36 / γ)⌉₊ : ℝ) ≤
        (18 * densityCoefficient (3 + γ) c / γ) ^ (36 / γ) + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
    _ ≤ exp (3888 / (γ ^ 2 * c)) + 1 := by grw [hx]
    _ ≤ exp (1 + 3888 / (γ ^ 2 * c)) := by
        rw [exp_add]
        nlinarith [add_one_le_exp (1 : ℝ),
          one_le_exp (by positivity : (0 : ℝ) ≤ 3888 / (γ ^ 2 * c))]
    _ ≤ exp (explicitLogThreshold γ c) :=
        exp_le_exp.2 (hy.trans (div_le_explicitLogThreshold hγ hγ' hc hc'))

/-! ### Consequences for `n` above the threshold -/

variable {n : ℕ}

lemma div_le_log_of_exp_explicitLogThreshold_le (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c)
    (hc' : c < 1) (hn : exp (explicitLogThreshold γ c) ≤ n) :
    10 ^ 9 / (γ ^ 3 * c ^ 2) ≤ log n :=
  (div_le_explicitLogThreshold hγ hγ' hc hc').trans
    ((le_log_iff_exp_le ((exp_pos _).trans_le hn)).2 hn)

lemma nine_le_of_exp_explicitLogThreshold_le (hγ : 0 < γ) (hγ' : γ ≤ 1) (hc : 0 < c)
    (hc' : c < 1) (hn : exp (explicitLogThreshold γ c) ≤ n) : 9 ≤ n := by
  have h : (10 : ℝ) ^ 9 ≤ 10 ^ 9 / (γ ^ 3 * c ^ 2) :=
    le_div_self (by norm_num) (by positivity) ((mul_le_of_le_one_left (by positivity)
      (pow_le_one₀ hγ.le hγ')).trans (pow_le_one₀ hc.le hc'.le))
  exact_mod_cast (by linarith [add_one_le_exp (explicitLogThreshold γ c),
    div_le_explicitLogThreshold hγ hγ' hc hc'] : (9 : ℝ) ≤ n)

end

end DenseSetsWithoutLargeSumsets
