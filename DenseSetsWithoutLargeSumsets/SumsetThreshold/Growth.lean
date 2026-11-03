/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DenseSetsWithoutLargeSumsets.ExplicitConstants
public import DenseSetsWithoutLargeSumsets.SumsetThreshold.Basic
import DenseSetsWithoutLargeSumsets.SumsetThreshold.LowerBound
import DenseSetsWithoutLargeSumsets.SumsetThreshold.UpperBound

/-!
# `φ(δ, N)` grows like `log N`

The upper bound of `SumsetThreshold.UpperBound` and the lower bound of
`SumsetThreshold.LowerBound` give Corollary 1.2 of *Dense sets without large sumsets*: for all
`n ≥ exp (explicitLogThreshold γ c)` and all `n ^ (-explicitDensityExponent γ c) ≤ δ ≤ 1 - c`,

`(1 - γ) / log (1 / δ) ≤ φ(δ, n) / log n ≤ (3 + γ) / log (1 / δ)`.

For fixed `0 < δ < 1` this proves Conjecture 4.10 of Kra, Moreira, Richter and Robertson
(*Problems on infinite sumset configurations in the integers and beyond*, arXiv:2311.06197):
`liminf φ(δ, N) / log N > 0` and `limsup φ(δ, N) / log N < ∞`.

## Main statements

* `phi_div_log_mem_Icc`: Corollary 1.2.
* `one_div_log_one_div_le_liminf_phi_div_log`: `1 / log (1 / δ) ≤ liminf φ(δ, N) / log N`, the
  statement of Corollary C of Hernández and Hetzel (*On growth rates of infinite and finite
  sumsets*, arXiv:2606.07310). The proof here goes through the Kővári–Sós–Turán theorem and is not
  theirs.
* `one_le_liminf_phi_mul_log_div_log`: `1 ≤ liminf φ(δ, N) * log (1 / δ) / log N`.
* `limsup_phi_div_log_lt_top_and_liminf_phi_div_log_pos`: Conjecture 4.10, with the limits taken
  in the extended reals.
* `liminf_phi_div_log_pos` and `limsup_phi_div_log_le_three_div_log_one_div`: the two halves with
  real limits.
* `exists_mul_log_le_phi_le_mul_log`: Conjecture 4.10 with explicit constants, for all large `N`.
-/

public section

namespace DenseSetsWithoutLargeSumsets

open Filter Real

variable {γ c : ℝ} {δ : unitInterval}

/-- `200 / (γ ^ 2 * c ^ 2) ≤ log n` for `n ≥ exp (explicitLogThreshold γ c)`. -/
private lemma div_le_log (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hc_pos : 0 < c) (hc_lt : c < 1)
    {n : ℕ} (hn : exp (explicitLogThreshold γ c) ≤ n) : 200 / (γ ^ 2 * c ^ 2) ≤ log n := by
  refine le_trans ?_ (div_le_log_of_exp_explicitLogThreshold_le hγ_pos hγ_le hc_pos hc_lt hn)
  refine div_le_div₀ (by norm_num) (by norm_num) (by positivity) ?_
  rw [(by ring : γ ^ 3 * c ^ 2 = γ ^ 2 * c ^ 2 * γ)]
  exact mul_le_of_le_one_right (by positivity) hγ_le

/-- **Corollary 1.2** of *Dense sets without large sumsets*. Let `0 < γ ≤ 1` and `0 < c < 1`. For
every `n ≥ exp (explicitLogThreshold γ c)` and every `δ` with
`n ^ (-explicitDensityExponent γ c) ≤ δ ≤ 1 - c`,
`(1 - γ) / log (1 / δ) ≤ φ(δ, n) / log n ≤ (3 + γ) / log (1 / δ)`. -/
theorem phi_div_log_mem_Icc (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hc_pos : 0 < c) (hc_lt : c < 1)
    {n : ℕ} (hn : exp (explicitLogThreshold γ c) ≤ n)
    (hδ : (n : ℝ) ^ (-explicitDensityExponent γ c) ≤ δ) (hδ' : (δ : ℝ) ≤ 1 - c) :
    (φ δ n : ℝ) / log n ∈ Set.Icc ((1 - γ) / log (1 / δ)) ((3 + γ) / log (1 / δ)) := by
  have hn₁ : (1 : ℝ) < n := by
    exact_mod_cast (nine_le_of_exp_explicitLogThreshold_le hγ_pos hγ_le hc_pos hc_lt hn).trans_lt'
      (by norm_num)
  have hlog := log_pos hn₁
  have hα := explicitDensityExponent_pos (c := c) hγ_pos
  have h₁ := log_div_log_le_phi hγ_pos hγ_le hc_pos hc_lt (div_le_log hγ_pos hγ_le hc_pos hc_lt hn)
    ((rpow_le_rpow_of_exponent_le hn₁.le
      (neg_le_neg (explicitDensityExponent_le_quarter hγ_pos hc_pos hc_lt))).trans hδ) hδ'
  have h₂ := phi_lt_log_div_log hγ_pos hγ_le hc_pos hc_lt hn
    ((rpow_lt_rpow_of_exponent_lt hn₁ (by linarith)).trans_le hδ) hδ'
  refine ⟨?_, ?_⟩
  · rwa [le_div_iff₀ hlog, div_mul_eq_mul_div]
  · rw [div_le_iff₀ hlog, div_mul_eq_mul_div]
    exact h₂.le

/-- For fixed `0 < δ < 1`, `1 / log (1 / δ) ≤ liminf φ(δ, N) / log N`. This is the statement of
Corollary C of Hernández and Hetzel. -/
theorem one_div_log_one_div_le_liminf_phi_div_log (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) :
    1 / log (1 / δ) ≤ liminf (fun N : ℕ ↦ (φ δ N : ℝ) / log N) atTop := by
  have hℓ := log_one_div_pos hδ_pos hδ_lt
  refine le_of_forall_lt_imp_le_of_dense ?_
  intro a ha
  rw [lt_div_iff₀ hℓ] at ha
  refine le_liminf_of_le (isBoundedUnder_le_phi_div_log hδ_pos hδ_lt).isCoboundedUnder_ge ?_
  filter_upwards [eventually_div_log_le_phi_div_log hδ_pos hδ_lt (γ := 1 - a * log (1 / δ))
    (by linarith)] with N hN
  rwa [sub_sub_cancel, mul_div_cancel_right₀ _ hℓ.ne'] at hN

/-- For fixed `0 < δ < 1`, `1 ≤ liminf φ(δ, N) * log (1 / δ) / log N`. -/
lemma one_le_liminf_phi_mul_log_div_log (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) :
    1 ≤ liminf (fun N : ℕ ↦ (φ δ N : ℝ) * log (1 / δ) / log N) atTop := by
  refine le_of_forall_lt_imp_le_of_dense ?_
  intro a ha
  refine le_liminf_of_le (isCoboundedUnder_ge_of_eventually_le _
    (eventually_phi_mul_log_div_log_le hδ_pos hδ_lt one_pos le_rfl)) ?_
  filter_upwards [eventually_le_phi_mul_log_div_log hδ_pos hδ_lt (γ := 1 - a) (by linarith)]
    with N hN
  rwa [sub_sub_cancel] at hN

/-- The lower half of Conjecture 4.10 of Kra, Moreira, Richter and Robertson: for fixed
`0 < δ < 1`, `liminf φ(δ, N) / log N > 0`. The upper half is
`limsup_phi_div_log_le_three_div_log_one_div`. -/
lemma liminf_phi_div_log_pos (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) :
    0 < liminf (fun N : ℕ ↦ (φ δ N : ℝ) / log N) atTop :=
  (one_div_pos.2 (log_one_div_pos hδ_pos hδ_lt)).trans_le
    (one_div_log_one_div_le_liminf_phi_div_log hδ_pos hδ_lt)

/-- Conjecture 4.10 of Kra, Moreira, Richter and Robertson with explicit constants: for fixed
`0 < δ < 1` there are `c > 0` and `C` such that `c * log N ≤ φ(δ, N) ≤ C * log N` for all large
`N`. -/
lemma exists_mul_log_le_phi_le_mul_log (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) :
    ∃ c C : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * log N ≤ φ δ N ∧ (φ δ N : ℝ) ≤ C * log N := by
  refine ⟨(1 - 1 / 2) / log (1 / δ), (3 + 1) / log (1 / δ),
    div_pos (by norm_num) (log_one_div_pos hδ_pos hδ_lt), ?_⟩
  filter_upwards [eventually_div_log_le_phi_div_log hδ_pos hδ_lt one_half_pos,
    eventually_phi_div_log_le hδ_pos hδ_lt one_pos le_rfl, eventually_ge_atTop 2]
    with N h₁ h₂ hN
  have hlog : 0 < log N := log_pos (mod_cast hN)
  exact ⟨(le_div_iff₀ hlog).1 h₁, (div_le_iff₀ hlog).1 h₂⟩

/-- Conjecture 4.10 of Kra, Moreira, Richter and Robertson as they state it, with both limits
taken in the extended reals: for fixed `0 < δ < 1`, `limsup φ(δ, N) / log N < ∞` and
`liminf φ(δ, N) / log N > 0`. -/
theorem limsup_phi_div_log_lt_top_and_liminf_phi_div_log_pos (hδ_pos : 0 < (δ : ℝ))
    (hδ_lt : (δ : ℝ) < 1) :
    limsup (fun N : ℕ ↦ ((φ δ N / log N : ℝ) : EReal)) atTop < ⊤ ∧
      0 < liminf (fun N : ℕ ↦ ((φ δ N / log N : ℝ) : EReal)) atTop := by
  refine ⟨(limsup_le_of_le (h := ?_)).trans_lt (EReal.coe_lt_top ((3 + 1) / log (1 / δ))),
    (EReal.coe_pos.2 (div_pos one_half_pos (log_one_div_pos hδ_pos hδ_lt))).trans_le
      (le_liminf_of_le (h := ?_))⟩
  · filter_upwards [eventually_phi_div_log_le hδ_pos hδ_lt one_pos le_rfl] with N hN
    exact EReal.coe_le_coe_iff.2 hN
  · filter_upwards [eventually_div_log_le_phi_div_log hδ_pos hδ_lt one_half_pos] with N hN
    exact EReal.coe_le_coe_iff.2 (by linarith)

end DenseSetsWithoutLargeSumsets
