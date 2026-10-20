/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.Constants
import SumOfSetsInSeveralDimensions.FreimanDimensionSumsetBounds

/-!
# Estimates for the thresholds and the density exponent

Let `n` be larger than `lowerSizeThreshold C γ` or `lowerGapThreshold C γ c`, let
`α = lowerDensityExponent C γ` and let `n ^ (-α) < δ < 1`. This file turns these assumptions into
the inequalities between `log n`, the size `k = pairCardThreshold (3 + γ) n δ` and the constants
that the counting argument uses.

## Main statements

* `fifteen_lt_log_of_lowerAnalyticThreshold`: `15 < log n`.
* `two_mul_chang_size_threshold_lt_pairCardThreshold`:
  `2 * exp (containerExponent (κ C)) < k`.
* `fourteen_mul_sq_lt_ε_mul_pairCardThreshold`: `14 * C ^ 2 < ε γ * k`.
* `density_coeff_log_lt_exp_neg_mul_q`: `2 * K * log n < exp (-changExponent C) * q` for
  `K = densityCoefficient (3 + γ) c` and `q ≥ 2 * n`.
* `lowerLogScale_log_bound_of_gap`: `lowerLogScale γ * log (M * L * log n) ≤ log n` for
  `M = max 42 (3 * K)` and `L = lowerConstant C γ`.
* `lowerGapSqrtScale_log_bound`: `lowerGapSqrtScale C γ c * log (M * L * log n) ≤ √(log n)`.
* `freiman_image_sum_card`: a Freiman isomorphism of order `2` on `X` preserves the size of
  `A + B` for `A, B ⊆ X`.
-/

@[expose] public section

namespace DenseSetsWithoutLargeSumsets

open Finset Real ChangFreimanRuzsa SumOfSetsInSeveralDimensions
open scoped Pointwise

noncomputable section

private lemma mul_log_mul_le_self {A T x : ℝ} (hA : 0 < A) (hT : 0 < T) (hx : 0 < x)
    (h : 2 * T * log (A * T) ≤ x) : T * log (A * x) ≤ x := by
  have hlog : log (A * x) = log (A * T) + log (x / T) := by
    rw [← log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  rw [hlog]
  nlinarith [log_le_half_self (div_pos hx hT), div_mul_cancel₀ x hT.ne']

private lemma log_le_sqrt {x : ℝ} (hx : 0 < x) : log x ≤ √x := by
  have h := log_le_half_self (sqrt_pos.2 hx)
  rw [log_sqrt hx.le] at h
  linarith

private lemma log_le_quarter_self {x : ℝ} (hx : 16 ≤ x) : log x ≤ x / 4 := by
  have h : 4 ≤ √x := le_sqrt_of_sq_le (by linarith)
  nlinarith [log_le_sqrt (by linarith : 0 < x), sq_sqrt (by linarith : 0 ≤ x)]

private lemma seven_halves_lt_log_fiftysix : (7 / 2 : ℝ) < log 56 := by
  have h₂ := lt_log_one_add_of_pos (zero_lt_one' ℝ)
  have h₇ := lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 6)
  rw [(by norm_num : (56 : ℝ) = 2 ^ 3 * 7), log_mul (by norm_num) (by norm_num), log_pow]
  norm_num at h₂ h₇ ⊢
  linarith

private lemma four_lt_log_eightyfour : (4 : ℝ) < log 84 := by
  have h₂ := lt_log_one_add_of_pos (zero_lt_one' ℝ)
  have h := log_lt_log (by norm_num) (by norm_num : (2 : ℝ) ^ 6 < 84)
  rw [log_pow] at h
  norm_num at h₂ h
  linarith

private lemma mul_log_mul_le_sqrt {A T x : ℝ} (hA : 42 ≤ A) (hT : 1 ≤ T) (hx : 0 < x)
    (h : 4 * T * log (2 * A * T) ≤ √x) : T * log (A * x) ≤ √x := by
  have hT₀ : 0 < T := by linarith
  have hA₀ : 0 < A := by linarith
  have h₈₄ : log 84 ≤ log (2 * A * T) := log_le_log (by norm_num) (by nlinarith)
  have hAT : log (2 * A * T) = log 2 + log A + log T := by
    rw [log_mul (by positivity) hT₀.ne', log_mul two_ne_zero hA₀.ne']
  have hlog : log (A * x) = log A + 2 * (log (√x / T) + log T) := by
    rw [log_mul hA₀.ne' hx.ne', log_div (sqrt_pos.2 hx).ne' hT₀.ne', log_sqrt hx.le]
    ring
  have h' : 4 * log (2 * A * T) ≤ √x / T := by
    rw [le_div_iff₀ hT₀]
    linarith
  rw [← le_div_iff₀' hT₀]
  linarith [log_le_quarter_self (by linarith [four_lt_log_eightyfour] : 16 ≤ √x / T),
    log_nonneg (by linarith : 1 ≤ A), log_nonneg hT, log_nonneg one_le_two]

/-- If `n` is larger than `lowerSizeThreshold C γ`, then `15 < log n`. -/
lemma fifteen_lt_log_of_lowerAnalyticThreshold {C γ : ℝ} {n : ℕ}
    (hn : lowerSizeThreshold C γ < n) :
    (15 : ℝ) < log (n : ℝ) := by
  have h : exp (4 * log 56 + 1) < n := (exp_le_exp.2 (le_max_left _ _)).trans_lt
    ((lowerAnalyticThreshold_le_lowerSizeThreshold C γ).trans_lt hn)
  linarith [(lt_log_iff_exp_lt ((exp_pos _).trans h)).2 h, seven_halves_lt_log_fiftysix]

lemma pairCardThreshold_pos_of_density {τ : ℝ} {n : ℕ} {δ : unitInterval}
    (hτ : 0 < τ) (hδ : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) (hn : 1 < n) :
    0 < pairCardThreshold τ n δ := by
  rw [pairCardThreshold, Nat.ceil_pos]
  exact div_pos (mul_pos hτ (log_pos (mod_cast hn))) (log_pos ((one_lt_div hδ).2 hδ_lt))

lemma one_lt_densityCoefficient {γ c : ℝ} (hγ_pos : 0 < γ)
    (hc_pos : 0 < c) (hc_lt : c < 1) :
    1 < densityCoefficient (3 + γ) c :=
  densityCoefficient_gt_one (by linarith) hc_pos hc_lt

private lemma one_le_lowerGapSqrtScale {C γ c : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1)
    (hC : 0 < 2 * C) (hε : 0 < ε γ) (hc_pos : 0 < c) (hc_lt : c < 1) :
    1 ≤ lowerGapSqrtScale C γ c hC hε := by
  rw [lowerGapSqrtScale, le_div_iff₀ hε]
  linarith [ε_le_one_twelfth hγ_pos hγ_le, one_le_mul_of_one_le_of_one_le
    (one_le_lowerBltConstant hC hε)
    (one_le_sqrt.2 (one_lt_densityCoefficient hγ_pos hc_pos hc_lt).le)]

lemma κ_ge_six_of_one_le {C : ℝ} (hC : 1 ≤ C) : 6 ≤ κ C := by
  rw [κ]
  linarith [one_le_pow₀ hC (n := 2)]

lemma two_le_κ_of_one_le {C : ℝ} (hC : 1 ≤ C) : 2 ≤ κ C := by
  linarith [κ_ge_six_of_one_le hC]

lemma lowerDensityExponent_pos_of_one_le {C γ : ℝ} (hγ : 0 < γ) (hC : 1 ≤ C) :
    0 < lowerDensityExponent C γ := by
  have := ε_pos hγ
  unfold lowerDensityExponent
  positivity

private lemma two_add_mul_ε {γ : ℝ} (hγ : 0 < γ) : (2 + γ) * ε γ = γ / 4 := by
  unfold ε
  field_simp
  ring

private lemma sq_mul_lowerDensityExponent_le {C : ℝ} (γ : ℝ) (hC : 1 ≤ C) :
    C ^ 2 * lowerDensityExponent C γ ≤ (2 + γ) * ε γ / 24 := by
  have h : lowerDensityExponent C γ ≤ (2 + γ) * ε γ / (12 * C ^ 2) / 2 :=
    div_le_div_of_nonneg_right (min_le_left _ _) zero_le_two
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq ?_
  field_simp
  ring

private lemma exp_mul_lowerDensityExponent_le (C γ : ℝ) :
    exp (containerExponent (κ C)) * lowerDensityExponent C γ ≤ (2 + γ) / 4 := by
  have h : lowerDensityExponent C γ ≤ (2 + γ) / (2 * exp (containerExponent (κ C))) / 2 :=
    div_le_div_of_nonneg_right (min_le_right _ _) zero_le_two
  refine (mul_le_mul_of_nonneg_left h (exp_pos _).le).trans_eq ?_
  field_simp
  ring

/-- If `k ≤ |A + B| ≤ C * k` for sets `A` and `B` of size `k > 0`, then `C ≥ 1`. -/
lemma one_le_sumset_card_coefficient_of_small_pair_sumset
    {G : Type*} [DecidableEq G] [Add G]
    [IsRightCancelAdd G]
    {A B : Finset G} {k : ℕ} {C : ℝ}
    (hk : 0 < k) (hAcard : #A = k) (hBcard : #B = k)
    (hAB : #(A + B) ≤ C * k) : 1 ≤ C := by
  subst hAcard
  have hA : (0 : ℝ) < #A := mod_cast hk
  have h : (#A : ℝ) ≤ #(A + B) :=
    mod_cast card_le_card_add_right (card_pos.1 (hBcard ▸ hk))
  exact le_of_mul_le_mul_right (by linarith) hA

/-- A Freiman isomorphism of order `2` on `X` preserves the size of `A + B` for `A, B ⊆ X`. -/
lemma freiman_image_sum_card {G H : Type*} [DecidableEq G] [DecidableEq H]
    [AddCommMonoid G] [AddCommMonoid H]
    {X A B : Finset G} {Y : Set H} {f : G → H}
    (hiso : IsAddFreimanIso 2 (X : Set G) Y f)
    (hAX : A ⊆ X) (hBX : B ⊆ X) :
    #(A.image f + B.image f) = #(A + B) := by
  rw [add_def, add_def, ← prodMap_image_product, image_image]
  apply card_image_eq_of_kernel_iff
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab'
  obtain ⟨ha, hb⟩ := mem_product.1 hab
  obtain ⟨ha', hb'⟩ := mem_product.1 hab'
  exact hiso.add_eq_add (hAX ha) (hBX hb) (hAX ha') (hBX hb')

private lemma log_one_div_lt_lowerDensityExponent_mul_log {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hn_pos : 0 < n) (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) :
    log (1 / δ) < lowerDensityExponent C γ * log n := by
  have hn : (0 : ℝ) < n := mod_cast hn_pos
  have h := log_lt_log (rpow_pos_of_pos hn _) hδ_lower
  rw [log_rpow hn] at h
  rw [one_div, log_inv]
  linarith

lemma log_one_div_unitInterval_pos {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hn_pos : 0 < n) (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ))
    (hδ_upper : (δ : ℝ) < 1) :
    0 < log (1 / δ) :=
  log_pos ((one_lt_div ((rpow_pos_of_pos (Nat.cast_pos.2 hn_pos) _).trans hδ_lower)).2 hδ_upper)

lemma pairCardThreshold_arg_le {γ : ℝ} {n : ℕ} {δ : unitInterval} :
    (3 + γ) * log (n : ℝ) / log (1 / δ) ≤
      (pairCardThreshold (3 + γ) n δ : ℝ) :=
  Nat.le_ceil _

private lemma two_mul_ceil_κ_sub_one_le_fourteen_sq {C : ℝ} (hC : 1 ≤ C) :
    ((2 * ⌈κ C⌉₊ - 1 : ℕ) : ℝ) ≤ 14 * C ^ 2 := by
  have h : ((2 * ⌈κ C⌉₊ - 1 : ℕ) : ℝ) ≤ 2 * ⌈κ C⌉₊ := mod_cast Nat.sub_le _ _
  have hκ : κ C = 6 * C ^ 2 := rfl
  linarith [Nat.ceil_lt_add_one (by linarith [κ_ge_six_of_one_le hC] : 0 ≤ κ C),
    one_le_pow₀ hC (n := 2)]

private lemma lt_pairCardThreshold_of_mul_lowerDensityExponent_lt {γ C R : ℝ} {n : ℕ}
    {δ : unitInterval} (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn_one : 1 < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hR : R * lowerDensityExponent C γ < 3 + γ) :
    R < (pairCardThreshold (3 + γ) n δ : ℝ) := by
  have hn_pos := zero_lt_one.trans hn_one
  have hlog : 0 < log n := log_pos (mod_cast hn_one)
  refine lt_of_lt_of_le ?_ pairCardThreshold_arg_le
  refine lt_trans ?_ (div_lt_div_of_pos_left (mul_pos (by linarith) hlog)
    (log_one_div_unitInterval_pos hn_pos hδ_lower hδ_upper)
    (log_one_div_lt_lowerDensityExponent_mul_log hn_pos hδ_lower))
  rw [lt_div_iff₀ (mul_pos (lowerDensityExponent_pos_of_one_le hγ_pos hC_one) hlog)]
  linarith [mul_lt_mul_of_pos_right hR hlog]

/-- The size `k` is larger than `2 * exp (containerExponent (κ C))`. -/
lemma two_mul_chang_size_threshold_lt_pairCardThreshold {γ C : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn_one : 1 < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    2 * (exp (containerExponent (κ C))) <
      (pairCardThreshold (3 + γ) n δ : ℝ) :=
  lt_pairCardThreshold_of_mul_lowerDensityExponent_lt hγ_pos hC_one hn_one hδ_lower hδ_upper
    (by linarith [exp_mul_lowerDensityExponent_le C γ])

/-- The size `k` satisfies `14 * C ^ 2 < ε γ * k`. -/
lemma fourteen_mul_sq_lt_ε_mul_pairCardThreshold {γ C : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn_one : 1 < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    14 * C ^ (2 : ℕ) < ε γ * (pairCardThreshold (3 + γ) n δ : ℝ) := by
  have hε := ε_pos hγ_pos
  rw [← div_lt_iff₀' hε]
  apply lt_pairCardThreshold_of_mul_lowerDensityExponent_lt hγ_pos hC_one hn_one hδ_lower hδ_upper
  rw [div_mul_eq_mul_div, div_lt_iff₀ hε]
  linarith [sq_mul_lowerDensityExponent_le γ hC_one, mul_pos hγ_pos hε]

lemma two_mul_ceil_κ_sub_one_le_ε_mul_pairCardThreshold {γ C : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn_one : 1 < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    ((2 * ⌈κ C⌉₊ - 1 : ℕ) : ℝ) ≤
      ε γ * (pairCardThreshold (3 + γ) n δ : ℝ) :=
  (two_mul_ceil_κ_sub_one_le_fourteen_sq hC_one).trans
    (fourteen_mul_sq_lt_ε_mul_pairCardThreshold hγ_pos hC_one hn_one hδ_lower hδ_upper).le

lemma two_mul_ceil_κ_sub_one_le_pairCardThreshold {γ C : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn_one : 1 < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    2 * ⌈κ C⌉₊ - 1 ≤ pairCardThreshold (3 + γ) n δ := by
  refine (Nat.cast_lt (α := ℝ).1 (lt_pairCardThreshold_of_mul_lowerDensityExponent_lt hγ_pos
    hC_one hn_one hδ_lower hδ_upper ?_)).le
  linarith [mul_le_mul_of_nonneg_right (two_mul_ceil_κ_sub_one_le_fourteen_sq hC_one)
    (lowerDensityExponent_pos_of_one_le hγ_pos hC_one).le,
    sq_mul_lowerDensityExponent_le γ hC_one, two_add_mul_ε hγ_pos]

lemma old_model_threshold_nat_pos {C γ : ℝ} {n : ℕ} (hn : lowerSizeThreshold C γ < n) :
    0 < (n : ℝ) := by
  linarith [two_le_lowerSizeThreshold C γ]

/-- If `n` is larger than `lowerGapThreshold C γ c` and `q ≥ 2 * n`, then
`2 * K * log n < exp (-changExponent C) * q` for `K = densityCoefficient (3 + γ) c`. -/
lemma density_coeff_log_lt_exp_neg_mul_q {C γ c : ℝ} {n q : ℕ}
    (hγ_pos : 0 < γ) (hc_pos : 0 < c) (hc_lt : c < 1)
    (hn : lowerGapThreshold C γ c < n) (hq_lower : 2 * n ≤ q) :
    2 * densityCoefficient (3 + γ) c * log (n : ℝ) <
      exp (-(changExponent C)) * q := by
  have hK := densityCoefficient_pos (by linarith : 0 < 3 + γ) hc_pos hc_lt
  have hn₀ := old_model_threshold_nat_pos
    ((lowerSizeThreshold_le_lowerGapThreshold C γ c).trans_lt hn)
  have hsq : (2 * densityCoefficient (3 + γ) c * exp (changExponent C)) ^ 2 < n :=
    (le_max_of_le_right (le_max_left _ _)).trans_lt hn
  have hq : (2 * n : ℝ) ≤ q := mod_cast hq_lower
  rw [exp_neg, inv_mul_eq_div, lt_div_iff₀ (exp_pos _)]
  linarith [mul_le_mul_of_nonneg_left (log_le_sqrt hn₀)
      (by positivity : 0 ≤ 2 * densityCoefficient (3 + γ) c * exp (changExponent C)),
    mul_lt_mul_of_pos_right (lt_sqrt_of_sq_lt hsq) (sqrt_pos.2 hn₀), mul_self_sqrt hn₀.le]

private lemma max_lt_log_of_lowerGapThreshold_lt {C γ c : ℝ} {n : ℕ}
    (hn : lowerGapThreshold C γ c < n) :
    max
      (2 * lowerLogScale γ * log
        (max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstantDefault C γ * lowerLogScale γ))
      ((4 * lowerGapSqrtScaleDefault C γ c * log
        (2 * max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstantDefault C γ *
          lowerGapSqrtScaleDefault C γ c)) ^ 2) < log n := by
  have h : exp _ < (n : ℝ) := (le_max_of_le_right (le_max_right _ _)).trans_lt hn
  exact (lt_log_iff_exp_lt ((exp_pos _).trans h)).2 h

/-- If `n` is larger than `lowerGapThreshold C γ c`, then
`lowerLogScale γ * log (M * L * log n) ≤ log n` for `M = max 42 (3 * K)`,
`K = densityCoefficient (3 + γ) c` and `L = lowerConstant C γ`. -/
lemma lowerLogScale_log_bound_of_gap {C γ c : ℝ} {n : ℕ}
    (hC : 0 < 2 * C) (hε : 0 < ε γ)
    (hn : lowerGapThreshold C γ c < n) :
    lowerLogScale γ * log
        (max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstant C γ hC hε *
          log (n : ℝ)) ≤
      log (n : ℝ) := by
  have hn_old := (lowerSizeThreshold_le_lowerGapThreshold C γ c).trans_lt hn
  apply mul_log_mul_le_self
    (mul_pos (lt_max_of_lt_left (by norm_num)) (lowerConstant_pos C γ hC hε))
    (lowerLogScale_pos hε) (by linarith [fifteen_lt_log_of_lowerAnalyticThreshold hn_old])
  rw [← lowerConstantDefault_eq C γ hC hε]
  exact ((le_max_left _ _).trans_lt (max_lt_log_of_lowerGapThreshold_lt hn)).le

/-- If `n` is larger than `lowerGapThreshold C γ c`, then
`lowerGapSqrtScale C γ c * log (M * L * log n) ≤ √(log n)` for `M = max 42 (3 * K)`,
`K = densityCoefficient (3 + γ) c` and `L = lowerConstant C γ`. -/
lemma lowerGapSqrtScale_log_bound {C γ c : ℝ} {n : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC : 0 < 2 * C) (hε : 0 < ε γ)
    (hc_pos : 0 < c) (hc_lt : c < 1)
    (hn : lowerGapThreshold C γ c < n) :
    lowerGapSqrtScale C γ c hC hε * log
        (max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstant C γ hC hε *
          log (n : ℝ)) ≤
      √(log (n : ℝ)) := by
  have hn_old := (lowerSizeThreshold_le_lowerGapThreshold C γ c).trans_lt hn
  refine mul_log_mul_le_sqrt ?_ (one_le_lowerGapSqrtScale hγ_pos hγ_le hC hε hc_pos hc_lt)
    (by linarith [fifteen_lt_log_of_lowerAnalyticThreshold hn_old]) ?_
  · nlinarith [le_max_left 42 (3 * densityCoefficient (3 + γ) c), one_le_lowerConstant hC hε]
  · apply le_sqrt_of_sq_le
    rw [← mul_assoc 2, ← lowerConstantDefault_eq C γ hC hε,
      ← lowerGapSqrtScaleDefault_eq C γ c hC hε]
    exact ((le_max_right _ _).trans_lt (max_lt_log_of_lowerGapThreshold_lt hn)).le

end

end DenseSetsWithoutLargeSumsets
