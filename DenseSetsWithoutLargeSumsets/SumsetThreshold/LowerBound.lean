/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DenseSetsWithoutLargeSumsets.SumsetThreshold.Basic
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.SumsetLowerBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The lower bound for `φ(δ, N)`

Hernández and Hetzel proved that `liminf φ(δ, N) / log N ≥ 1 / log (1 / δ)` for every fixed
`0 < δ < 1` (*On growth rates of infinite and finite sumsets*, arXiv:2606.07310, Corollary C).
Corollary 1.2 of *Dense sets without large sumsets* quotes it in the uniform form
`φ(δ, n) ≥ (1 - γ) * log n / log (1 / δ)` for all large `n` and all `n ^ (-α) ≤ δ ≤ 1 - c`.

This file proves the uniform form. The proof is not the one of Hernández and Hetzel: it applies
`pairEvent_of_mul_log_le`, a consequence of the Kővári–Sós–Turán theorem, to
`k = ⌈(1 - γ) * log n / log (1 / δ)⌉`.

## Main statements

* `eventually_forall_log_div_log_le_phi`: for `γ > 0` and `0 < c < 1`, for all large `n` and every
  `δ` with `n ^ (-(γ / 4)) ≤ δ ≤ 1 - c`, `(1 - γ) * log n / log (1 / δ) ≤ φ(δ, n)`.
* `eventually_div_log_le_phi_div_log`: for fixed `0 < δ < 1`, `γ > 0` and all large `N`,
  `(1 - γ) / log (1 / δ) ≤ φ(δ, N) / log N`.
-/

public section

namespace DenseSetsWithoutLargeSumsets

open Filter Real

private lemma mul_add_two_mul_log_add_two_le {K L ℓ ℓ₀ θ γ : ℝ} (hK : 1 ≤ K) (hL : 0 ≤ L)
    (hθ : 0 < θ) (hθ₁ : θ ≤ 1) (hθγ : θ / ℓ₀ ≤ γ / 12) (hℓ : ℓ ≤ γ / 4 * L)
    (hKℓ : K * ℓ ≤ (1 - γ) * L + ℓ) (hKL : K ≤ L / ℓ₀ + 1) (hθL : 3 - 2 * log θ ≤ γ / 2 * L) :
    K * (ℓ + θ) + 2 * log K + 2 ≤ L := by
  have hlog := log_le_sub_one_of_pos (mul_pos hθ (by linarith : 0 < K))
  rw [log_mul hθ.ne' (by linarith)] at hlog
  linarith [mul_le_mul_of_nonneg_left hKL hθ.le, mul_le_mul_of_nonneg_right hθγ hL,
    (by ring : θ * (L / ℓ₀ + 1) = θ / ℓ₀ * L + θ)]

private lemma mul_one_add_lt_mul_exp {K L ℓ ℓ₀ θ γ : ℝ} (hK : 0 ≤ K) (hL : 1 ≤ L) (hθ : 0 < θ)
    (hθ₁ : θ ≤ 1) (hγ : γ ≤ 1) (hℓ : ℓ ≤ γ / 4 * L) (hKL : K ≤ L / ℓ₀ + 1)
    (hLθ : (2 / ℓ₀ + 2) * 32 / (9 * θ) < L) :
    K * (1 + θ) < θ * exp (L - ℓ) := by
  rw [div_lt_iff₀ (by positivity)] at hLθ
  have h₁ : K * (1 + θ) ≤ (L / ℓ₀ + 1) * 2 := mul_le_mul hKL (by linarith) (by linarith)
    (hK.trans hKL)
  have h₂ := mul_le_mul_of_nonneg_left
    ((quadratic_le_exp_of_nonneg (x := 3 / 4 * L) (by linarith)).trans
      (exp_le_exp.2 (by nlinarith : 3 / 4 * L ≤ L - ℓ))) hθ.le
  nlinarith [mul_lt_mul_of_pos_right hLθ (by linarith : 0 < L), mul_pos hθ (by linarith : 0 < L),
    (by ring : (L / ℓ₀ + 1) * 2 = 2 / ℓ₀ * L + 2)]

private lemma le_phi_of_le_log_div_log_add_one {γ c θ : ℝ} {n k : ℕ} {δ : unitInterval}
    (hc₀ : 0 < c) (hc : c < 1) (hθ : 0 < θ) (hθ₁ : θ ≤ 1)
    (hθγ : θ / log (1 / (1 - c)) ≤ γ / 12) (hL₁ : 1 ≤ log n)
    (hL₂ : 3 - 2 * log θ ≤ γ / 2 * log n)
    (hL₃ : (2 / log (1 / (1 - c)) + 2) * 32 / (9 * θ) < log n)
    (hδ : (n : ℝ) ^ (-(γ / 4)) ≤ δ) (hδ' : (δ : ℝ) ≤ 1 - c) (hk : 1 ≤ k)
    (hkx : (k : ℝ) ≤ (1 - γ) * log n / log (1 / δ) + 1) :
    k ≤ phi δ n := by
  have hK : (1 : ℝ) ≤ k := mod_cast hk
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h ↦ by norm_num [h] at hL₁)
  have hδ₀ : 0 < (δ : ℝ) := (rpow_pos_of_pos hn _).trans_le hδ
  have hℓ₀ := log_one_div_pos (sub_pos.2 hc) (sub_lt_self 1 hc₀)
  have hℓ₀ℓ : log (1 / (1 - c)) ≤ log (1 / δ) :=
    log_le_log (one_div_pos.2 (sub_pos.2 hc)) (one_div_le_one_div_of_le hδ₀ hδ')
  have hℓ : log (1 / δ) ≤ γ / 4 * log n := by
    have h := log_le_log (rpow_pos_of_pos hn _) hδ
    rw [log_rpow hn] at h
    rw [one_div, log_inv]
    linarith
  have hγ : γ ≤ 1 := by
    by_contra h
    linarith [div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith : 1 - γ < 0)
      (by linarith : 0 < log n)) (hℓ₀.trans_le hℓ₀ℓ)]
  have hKℓ : k * log (1 / δ) ≤ (1 - γ) * log n + log (1 / δ) := by
    have h := mul_le_mul_of_nonneg_right hkx (hℓ₀.trans_le hℓ₀ℓ).le
    rwa [add_mul, one_mul, div_mul_cancel₀ _ (hℓ₀.trans_le hℓ₀ℓ).ne'] at h
  have hKL : (k : ℝ) ≤ log n / log (1 / (1 - c)) + 1 :=
    hkx.trans (add_le_add_left (div_le_div₀ (by linarith) (by nlinarith) hℓ₀ hℓ₀ℓ) 1)
  have h₁ := mul_add_two_mul_log_add_two_le hK (by linarith) hθ hθ₁ hθγ hℓ hKℓ hKL hL₂
  have h₂ := mul_one_add_lt_mul_exp (by linarith) hL₁ hθ hθ₁ hγ hℓ hKL hL₃
  rw [exp_sub, exp_log hn, exp_log (one_div_pos.2 hδ₀), div_div_eq_mul_div, div_one, ← mul_assoc,
    mul_right_comm] at h₂
  have hkn : (k : ℝ) ≤ n := by
    nlinarith [mul_le_mul_of_nonneg_right
      (mul_le_mul hθ₁ (unitInterval.le_one δ) hδ₀.le zero_le_one) hn.le]
  exact le_phi fun S hS hcard ↦
    pairEvent_of_mul_log_le hk (mod_cast hkn) hδ₀ hθ.le h₁ h₂ hS hcard

/-- For `γ > 0` and `0 < c < 1`, for all large `n` and every `δ` with
`n ^ (-(γ / 4)) ≤ δ ≤ 1 - c`, we have `⌈(1 - γ) * log n / log (1 / δ)⌉ ≤ φ(δ, n)`. -/
lemma eventually_forall_ceil_le_phi {γ c : ℝ} (hγ : 0 < γ) (hc₀ : 0 < c) (hc : c < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ δ : unitInterval, (n : ℝ) ^ (-(γ / 4)) ≤ δ → (δ : ℝ) ≤ 1 - c →
      ⌈(1 - γ) * log n / log (1 / δ)⌉₊ ≤ phi δ n := by
  have hℓ₀ := log_one_div_pos (sub_pos.2 hc) (sub_lt_self 1 hc₀)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (tendsto_log_atTop.eventually_ge_atTop 1),
    tendsto_natCast_atTop_atTop.eventually (tendsto_log_atTop.eventually_ge_atTop
      ((3 - 2 * log (min 1 (γ * log (1 / (1 - c)) / 12))) / (γ / 2))),
    tendsto_natCast_atTop_atTop.eventually (tendsto_log_atTop.eventually_gt_atTop
      ((2 / log (1 / (1 - c)) + 2) * 32 / (9 * min 1 (γ * log (1 / (1 - c)) / 12))))]
    with n h₁ h₂ h₃ δ hδ hδ'
  rcases Nat.eq_zero_or_pos ⌈(1 - γ) * log n / log (1 / (δ : ℝ))⌉₊ with h₀ | hk
  · exact h₀ ▸ Nat.zero_le _
  · exact le_phi_of_le_log_div_log_add_one hc₀ hc (lt_min one_pos (by positivity)) (min_le_left _ _)
      ((div_le_iff₀ hℓ₀).2 ((min_le_right _ _).trans_eq (by ring)))
      h₁ ((div_le_iff₀' (half_pos hγ)).1 h₂) h₃ hδ hδ' hk
      (Nat.ceil_lt_add_one (Nat.ceil_pos.1 hk).le).le

/-- The lower bound of Hernández and Hetzel in the uniform form of Corollary 1.2 of *Dense sets
without large sumsets*: for `γ > 0` and `0 < c < 1`, for all large `n` and every `δ` with
`n ^ (-(γ / 4)) ≤ δ ≤ 1 - c`, we have `(1 - γ) * log n / log (1 / δ) ≤ φ(δ, n)`. -/
lemma eventually_forall_log_div_log_le_phi {γ c : ℝ} (hγ : 0 < γ) (hc₀ : 0 < c) (hc : c < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ δ : unitInterval, (n : ℝ) ^ (-(γ / 4)) ≤ δ → (δ : ℝ) ≤ 1 - c →
      (1 - γ) * log n / log (1 / δ) ≤ phi δ n := by
  filter_upwards [eventually_forall_ceil_le_phi hγ hc₀ hc] with n hn δ hδ hδ'
    using (Nat.le_ceil _).trans (Nat.cast_le.2 (hn δ hδ hδ'))

variable {γ : ℝ} {δ : unitInterval}

/-- For fixed `0 < δ < 1`, `γ > 0` and all large `N`,
`(1 - γ) / log (1 / δ) ≤ φ(δ, N) / log N`. -/
lemma eventually_div_log_le_phi_div_log (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1)
    (hγ : 0 < γ) :
    ∀ᶠ N : ℕ in atTop, (1 - γ) / log (1 / δ) ≤ (phi δ N : ℝ) / log N := by
  filter_upwards [eventually_forall_log_div_log_le_phi hγ (sub_pos.2 hδ_lt) (sub_lt_self 1 hδ_pos),
    tendsto_natCast_atTop_atTop.eventually
      ((tendsto_rpow_neg_atTop (by positivity : 0 < γ / 4)).eventually_le_const hδ_pos),
    eventually_ge_atTop 2] with N hN hδN hN₂
  rw [div_le_div_iff₀ (log_one_div_pos hδ_pos hδ_lt) (log_pos (mod_cast hN₂))]
  exact (div_le_iff₀ (log_one_div_pos hδ_pos hδ_lt)).1 (hN δ hδN (sub_sub_cancel 1 _).ge)

/-- For fixed `0 < δ < 1`, `γ > 0` and all large `N`,
`1 - γ ≤ φ(δ, N) * log (1 / δ) / log N`. -/
lemma eventually_le_phi_mul_log_div_log (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1)
    (hγ : 0 < γ) :
    ∀ᶠ N : ℕ in atTop, 1 - γ ≤ (phi δ N : ℝ) * log (1 / δ) / log N := by
  filter_upwards [eventually_div_log_le_phi_div_log hδ_pos hδ_lt hγ, eventually_ge_atTop 2]
    with N hN hN₂
  rw [div_le_div_iff₀ (log_one_div_pos hδ_pos hδ_lt) (log_pos (mod_cast hN₂))] at hN
  rwa [le_div_iff₀ (log_pos (mod_cast hN₂))]

end DenseSetsWithoutLargeSumsets
