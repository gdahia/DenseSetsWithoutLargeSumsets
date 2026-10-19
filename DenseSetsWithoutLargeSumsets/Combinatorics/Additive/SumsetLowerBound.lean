/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DenseSetsWithoutLargeSumsets.Common
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.SumsetFromZarankiewicz
import DenseSetsWithoutLargeSumsets.Mathlib.Combinatorics.SimpleGraph.Extremal.KovariSosTuran
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Dense subsets of `[n]` contain large sumsets

Let `S ⊆ [n]` with `|S| ≥ δ n`. For `m ≤ n`, the reduction of `SumsetFromZarankiewicz` and the
Kővári–Sós–Turán bound

`zarankiewicz (n + m) m k k ≤ (k - 1) ^ (1 / k) * (n + m) * m ^ (1 - 1 / k) + (k - 1) * m`

show that `S` contains a sumset `A + B` with `A, B ⊆ [n]` and `|A|, |B| ≥ k` as soon as

`(k - 1) ^ (1 / k) * (1 + m / n) * m ^ (-1 / k) + k / n < δ`.

With `m = ⌈n / k⌉` the left side is at most `exp (-(log n - 2 * log k - 2) / k) + k / n`, which
gives a condition on `k` with no rational powers.

## Main statements

* `pairEvent_of_lt_density`: the condition above, for every `0 < m ≤ n`.
* `pairEvent_of_mul_log_le`: if `k * (log (1 / δ) + t) + 2 * log k + 2 ≤ log n` and
  `k * (1 + t) < t * δ * n` for some `t ≥ 0`, then `S` contains such a sumset.
* `eventually_pairEvent_of_rpow_le_card`: for fixed `k ≥ 1` and `α < 1 / k`, every `S ⊆ [n]` with
  `|S| ≥ n ^ (1 - α)` contains such a sumset when `n` is large.
-/

public section

namespace DenseSetsWithoutLargeSumsets

open Filter Finset SimpleGraph Real

/-- The reduction to the Zarankiewicz function, with the Kővári–Sós–Turán bound in place of the
Zarankiewicz function. -/
lemma exists_pairEvent_of_kovariSosTuran {n m k : ℕ} (hk : 1 ≤ k) (hmn : m ≤ n) {S : Finset ℕ}
    (hS : S ⊆ interval n)
    (hz : ((k : ℝ) - 1) ^ (k : ℝ)⁻¹ * (n + m) * (m : ℝ) ^ (1 - (k : ℝ)⁻¹) + ((k : ℝ) - 1) * m + m
      < m * #S) :
    pairEvent n k S := by
  apply exists_pairEvent_of_zarankiewicz_add_lt hmn hS
  have hkst := zarankiewicz_le (n + m) m hk le_rfl
  rw [Nat.cast_add] at hkst
  rw [← Nat.cast_lt (α := ℝ)]
  push_cast
  linarith

/-- Let `S ⊆ [n]` with `|S| ≥ δ n` and let `0 < m ≤ n`. If
`(k - 1) ^ (1 / k) * (1 + m / n) * m ^ (-1 / k) + k / n < δ`, then `S` contains a sumset `A + B`
with `A, B ⊆ [n]` and `|A|, |B| ≥ k`. -/
theorem pairEvent_of_lt_density {n m k : ℕ} {δ : ℝ} {S : Finset ℕ} (hk : 1 ≤ k) (hm : 0 < m)
    (hmn : m ≤ n) (hS : S ⊆ interval n) (hcard : δ * n ≤ #S)
    (hδ : ((k : ℝ) - 1) ^ (k : ℝ)⁻¹ * (1 + (m : ℝ) / n) * (m : ℝ) ^ (-(k : ℝ)⁻¹) + (k : ℝ) / n
      < δ) :
    pairEvent n k S := by
  have hm0 : (0 : ℝ) < m := mod_cast hm
  have hn0 : (0 : ℝ) < n := mod_cast hm.trans_le hmn
  apply exists_pairEvent_of_kovariSosTuran hk hmn hS
  rw [sub_eq_neg_add (1 : ℝ), rpow_add_one hm0.ne']
  have h : ((k : ℝ) - 1) ^ (k : ℝ)⁻¹ * (n + m) * (m : ℝ) ^ (-(k : ℝ)⁻¹) + k < δ * n := by
    rw [← div_lt_iff₀ hn0]
    convert hδ using 1
    field_simp
  linarith [mul_lt_mul_of_pos_left h hm0, mul_le_mul_of_nonneg_left hcard hm0.le]

private lemma sub_one_rpow_inv_le_exp {K : ℝ} (hK : 1 ≤ K) :
    (K - 1) ^ K⁻¹ ≤ exp (log K / K) := by
  rw [div_eq_mul_inv, ← rpow_def_of_pos (by linarith)]
  exact rpow_le_rpow (by linarith) (by linarith) (by positivity)

private lemma one_add_div_le_exp {K N M : ℝ} (hK : 1 ≤ K) (hKN : K ≤ N) (hM : M ≤ N / K + 1) :
    1 + M / N ≤ exp (2 / K) := by
  have hN : 0 < N := by linarith
  have h : M / N ≤ 1 / K + 1 / N := by
    rw [div_le_iff₀ hN]
    convert hM using 1
    field_simp
  linarith [add_one_le_exp (2 / K), one_div_le_one_div_of_le (by linarith) hKN, one_div K,
    div_eq_mul_inv 2 K]

private lemma rpow_neg_inv_le_exp {K N M : ℝ} (hK : 0 < K) (hN : 0 < N) (hM : N / K ≤ M) :
    M ^ (-K⁻¹) ≤ exp (-(log N - log K) / K) := by
  have h : -(log N - log K) / K = log (N / K) * -K⁻¹ := by
    rw [log_div hN.ne' hK.ne']
    ring
  rw [h, ← rpow_def_of_pos (div_pos hN hK)]
  exact rpow_le_rpow_of_nonpos (div_pos hN hK) hM (by simpa using hK.le)

private lemma exp_mul_exp_mul_exp_add_div_lt {K N δ t : ℝ} (hK : 1 ≤ K) (hN : 0 < N) (hδ : 0 < δ)
    (ht : 0 ≤ t) (hlog : K * (log (1 / δ) + t) + 2 * log K + 2 ≤ log N)
    (hKδ : K * (1 + t) < t * δ * N) :
    exp (log K / K) * exp (2 / K) * exp (-(log N - log K) / K) + K / N < δ := by
  have hK0 : 0 < K := by linarith
  rw [one_div, log_inv] at hlog
  have h₁ : exp (log K / K) * exp (2 / K) * exp (-(log N - log K) / K) ≤ δ / (1 + t) := by
    rw [← exp_add, ← exp_add, ← add_div, ← add_div, ← exp_log hδ]
    refine le_trans ?_ (div_le_div_of_nonneg_left (exp_pos _).le (by positivity)
      (add_comm 1 t ▸ add_one_le_exp t))
    rw [← exp_sub, exp_le_exp, div_le_iff₀ hK0]
    linarith
  have h₂ : K / N < δ * t / (1 + t) := by
    rw [div_lt_div_iff₀ hN (by positivity)]
    linarith
  have h₃ : δ / (1 + t) + δ * t / (1 + t) = δ := by
    field_simp
  linarith

/-- Let `S ⊆ [n]` with `|S| ≥ δ n`, let `1 ≤ k ≤ n` and let `t ≥ 0`. If
`k * (log (1 / δ) + t) + 2 * log k + 2 ≤ log n` and `k * (1 + t) < t * δ * n`, then `S` contains a
sumset `A + B` with `A, B ⊆ [n]` and `|A|, |B| ≥ k`. -/
theorem pairEvent_of_mul_log_le {n k : ℕ} {δ t : ℝ} {S : Finset ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hδ : 0 < δ) (ht : 0 ≤ t)
    (hlog : k * (log (1 / δ) + t) + 2 * log k + 2 ≤ log n) (hkδ : k * (1 + t) < t * δ * n)
    (hS : S ⊆ interval n) (hcard : δ * n ≤ #S) :
    pairEvent n k S := by
  have hK : (1 : ℝ) ≤ k := mod_cast hk
  have hKN : (k : ℝ) ≤ n := mod_cast hkn
  have hN : (0 : ℝ) < n := by linarith
  have hK0 : (0 : ℝ) < k := by linarith
  refine pairEvent_of_lt_density (m := ⌈(n : ℝ) / k⌉₊) hk (Nat.ceil_pos.2 (div_pos hN hK0))
    (Nat.ceil_le.2 (div_le_self hN.le hK)) hS hcard
    (lt_of_le_of_lt ?_ (exp_mul_exp_mul_exp_add_div_lt hK hN hδ ht hlog hkδ))
  gcongr
  · exact sub_one_rpow_inv_le_exp hK
  · exact one_add_div_le_exp hK hKN (Nat.ceil_lt_add_one (div_pos hN hK0).le).le
  · exact rpow_neg_inv_le_exp hK0 hN (Nat.le_ceil _)

/-- For fixed `k ≥ 1` and `α < 1 / k`, if `n` is large then every `S ⊆ [n]` with
`|S| ≥ n ^ (1 - α)` contains a sumset `A + B` with `A, B ⊆ [n]` and `|A|, |B| ≥ k`. -/
theorem eventually_pairEvent_of_rpow_le_card {k : ℕ} {α : ℝ} (hk : 1 ≤ k) (hα : α < (k : ℝ)⁻¹) :
    ∀ᶠ n : ℕ in atTop, ∀ S : Finset ℕ, S ⊆ interval n → (n : ℝ) ^ (1 - α) ≤ #S →
      pairEvent n k S := by
  have hK : (1 : ℝ) ≤ k := mod_cast hk
  have hkα : 0 < 1 - k * α := by
    linarith [mul_lt_mul_of_pos_left hα (by linarith : (0 : ℝ) < k),
      mul_inv_cancel₀ (by linarith : (k : ℝ) ≠ 0)]
  have hα₁ : 0 < 1 - α := by linarith [inv_le_one_of_one_le₀ hK]
  filter_upwards [eventually_ge_atTop k,
    tendsto_natCast_atTop_atTop.eventually
      (tendsto_log_atTop.eventually_ge_atTop ((k + 2 * log k + 2) / (1 - k * α))),
    tendsto_natCast_atTop_atTop.eventually ((tendsto_rpow_atTop hα₁).eventually_gt_atTop (2 * k))]
    with n hkn hL hpow S hS hcard
  have hn : (0 : ℝ) < n := mod_cast hk.trans hkn
  rw [div_le_iff₀ hkα] at hL
  apply pairEvent_of_mul_log_le (δ := (n : ℝ) ^ (-α)) (t := 1) hk hkn (rpow_pos_of_pos hn _)
    zero_le_one ?_ ?_ hS ?_
  · rw [one_div, log_inv, log_rpow hn]
    linarith
  · rw [one_mul, ← rpow_add_one hn.ne', neg_add_eq_sub]
    linarith [hpow]
  · rwa [← rpow_add_one hn.ne', neg_add_eq_sub]

end DenseSetsWithoutLargeSumsets
