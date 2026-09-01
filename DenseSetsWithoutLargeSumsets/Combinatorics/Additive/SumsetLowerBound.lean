/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.SumsetFromZarankiewicz
import DenseSetsWithoutLargeSumsets.Combinatorics.SimpleGraph.KovariSosTuran

/-!
# The lower bound for the main question

For any `m ≤ n`, the difference reduction in `exists_pairEvent_of_zarankiewicz_lt` gives a
relation on `Fin (n + m) × Fin m` with at least `m * (#S - 1)` edges.  Kővári–Sós–Turán
bounds its Zarankiewicz number by

`(k - 1) ^ (1 / k) * (n + m) * m ^ (1 - 1 / k) + (k - 1) * m`.

After division by `m * n`, the sufficient density is exactly

`(k - 1) ^ (1 / k) * (1 + m / n) * m ^ (-1 / k) + k / n`.

Taking `m = ⌊n / k⌋` makes every factor outside `n ^ (-1 / k)` equal to `1 + o(1)` and only
changes its logarithm by `O(log k)`.  Thus the guaranteed size is

`k = (1 - o(1)) * log n / log (1 / δ)`.

The construction has leading constant `3`, so the two directions match up to a factor of `3`.
-/

namespace DenseSetsWithoutLargeSumsets

open Finset SimpleGraph

/-- **The lower bound with the Kővári–Sós–Turán estimate substituted.** -/
theorem exists_pairEvent_of_kovariSosTuran {n m k : ℕ} (hk : 1 ≤ k) (hm : 0 < m)
    (hmn : m ≤ n) {S : Finset ℕ} (hS : S ⊆ interval n)
    (hz : ((k : ℝ) - 1) ^ ((k : ℝ)⁻¹) * (n + m) * m ^ (1 - (k : ℝ)⁻¹)
        + ((k : ℝ) - 1) * m + m < m * #S) :
    pairEvent n k S := by
  apply exists_pairEvent_of_zarankiewicz_add_lt hm hmn hS
  have hkst := zarankiewicz_le (n + m) m hk le_rfl
  have hlt : (zarankiewicz (n + m) m k k : ℝ) + m < (m : ℝ) * #S := by
    norm_num only [Nat.cast_add] at hkst ⊢
    linarith
  exact_mod_cast hlt

/-- **The constant-sharp density bound.** The free window parameter `m` may be optimized for
the desired `n`, `k`, and `δ`.  Choosing `m = ⌊n / k⌋` makes the coefficient of the main
term `1 + o(1)`, rather than losing a fixed constant. -/
theorem pairEvent_of_lt_density {n m k : ℕ} {δ : ℝ} {S : Finset ℕ} (hk : 1 ≤ k)
    (hm : 0 < m) (hmn : m ≤ n) (hS : S ⊆ interval n) (hcard : δ * n ≤ #S)
    (hδ : ((k : ℝ) - 1) ^ ((k : ℝ)⁻¹) * (1 + (m : ℝ) / n) *
          (m : ℝ) ^ (-(k : ℝ)⁻¹) + (k : ℝ) / n < δ) :
    pairEvent n k S := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le hm hmn
  apply exists_pairEvent_of_kovariSosTuran hk hm hmn hS
  have hpow : (m : ℝ) ^ (1 - (k : ℝ)⁻¹) =
      (m : ℝ) ^ (-(k : ℝ)⁻¹) * m := by
    rw [show 1 - (k : ℝ)⁻¹ = -(k : ℝ)⁻¹ + 1 by ring,
      Real.rpow_add hm0, Real.rpow_one]
  have hmul := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hδ hm0) hn0
  rw [hpow]
  calc
    ((k : ℝ) - 1) ^ ((k : ℝ)⁻¹) * ((n : ℝ) + m) *
          ((m : ℝ) ^ (-(k : ℝ)⁻¹) * m) + ((k : ℝ) - 1) * m + m
        < δ * m * n := by
          field_simp [hn0.ne'] at hmul ⊢
          nlinarith
    _ ≤ (m : ℝ) * #S := by nlinarith

/-- `(k - 1) ^ (1 / k) ≤ k`, used only for the convenient fixed-`k` corollary below. -/
private lemma rpow_inv_sub_one_le {k : ℕ} (hk : 1 ≤ k) :
    ((k : ℝ) - 1) ^ ((k : ℝ)⁻¹) ≤ (k : ℝ) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  rcases le_or_gt ((k : ℝ) - 1) 1 with h | h
  · calc
      ((k : ℝ) - 1) ^ ((k : ℝ)⁻¹) ≤ (1 : ℝ) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by linarith) h (by positivity)
      _ = 1 := Real.one_rpow _
      _ ≤ (k : ℝ) := hk1
  · calc
      ((k : ℝ) - 1) ^ ((k : ℝ)⁻¹) ≤ ((k : ℝ) - 1) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h.le (Nat.cast_inv_le_one k)
      _ = (k : ℝ) - 1 := Real.rpow_one _
      _ ≤ (k : ℝ) := by linarith

/-- A convenient consequence obtained by taking `m = n`. -/
private theorem pairEvent_of_crude_lt_density {n k : ℕ} {δ : ℝ} {S : Finset ℕ}
    (hk : 1 ≤ k) (hn : 1 ≤ n) (hS : S ⊆ interval n) (hcard : δ * n ≤ #S)
    (hδ : 3 * k * (n : ℝ) ^ (-(k : ℝ)⁻¹) < δ) :
    pairEvent n k S := by
  apply pairEvent_of_lt_density (m := n) hk (Nat.zero_lt_of_lt hn) le_rfl hS hcard
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkinv : (k : ℝ)⁻¹ ≤ 1 := Nat.cast_inv_le_one k
  have hpow_le : (n : ℝ)⁻¹ ≤ (n : ℝ) ^ (-(k : ℝ)⁻¹) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hpref := rpow_inv_sub_one_le hk
  have hpref0 : 0 ≤ ((k : ℝ) - 1) ^ ((k : ℝ)⁻¹) :=
    Real.rpow_nonneg (by linarith) _
  have hpow0 : 0 ≤ (n : ℝ) ^ (-(k : ℝ)⁻¹) := by positivity
  have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
  have hterm1 := mul_le_mul_of_nonneg_right hpref hpow0
  have hterm2 := mul_le_mul_of_nonneg_left hpow_le (zero_le_one.trans hk1)
  rw [div_self hn0.ne']
  norm_num
  calc
    ((k : ℝ) - 1) ^ ((k : ℝ)⁻¹) * 2 * (n : ℝ) ^ (-(k : ℝ)⁻¹) +
          (k : ℝ) / n
        ≤ 2 * ((k : ℝ) * (n : ℝ) ^ (-(k : ℝ)⁻¹)) +
          (k : ℝ) * (n : ℝ) ^ (-(k : ℝ)⁻¹) := by
            apply add_le_add
            · nlinarith
            · simpa only [div_eq_mul_inv] using hterm2
    _ = 3 * (k : ℝ) * (n : ℝ) ^ (-(k : ℝ)⁻¹) := by ring
    _ < δ := hδ

/-- **The lower bound in the power regime.** For fixed `k ≥ 1` and `α < 1 / k`, every
sufficiently large `S ⊆ [n]` with `#S ≥ n ^ (1 - α)` contains a sumset of size `k`.

The construction avoids size `(3 + o(1)) / α`; this guarantee reaches every fixed size below
`1 / α`, giving the claimed factor-three comparison. -/
theorem eventually_pairEvent_of_rpow_le_card {k : ℕ} {α : ℝ} (hk : 1 ≤ k)
    (hα : α < (k : ℝ)⁻¹) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ S : Finset ℕ, S ⊆ interval n →
      (n : ℝ) ^ (1 - α) ≤ #S → pairEvent n k S := by
  have hβ : 0 < (k : ℝ)⁻¹ - α := by linarith
  have htend : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((k : ℝ)⁻¹ - α))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually_gt_atTop (3 * k), Filter.eventually_ge_atTop 1]
    with n hgt hn S hS hcard
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  apply pairEvent_of_crude_lt_density (n := n) (k := k) (δ := (n : ℝ) ^ (-α)) hk hn hS
  · calc
      ((n : ℝ) ^ (-α)) * n = (n : ℝ) ^ (1 - α) := by
        rw [show 1 - α = -α + 1 by ring, Real.rpow_add hn0, Real.rpow_one]
      _ ≤ #S := hcard
  · have hsplit : (n : ℝ) ^ ((k : ℝ)⁻¹ - α) =
        (n : ℝ) ^ (-α) / (n : ℝ) ^ (-(k : ℝ)⁻¹) := by
      rw [← Real.rpow_sub hn0]
      congr 1
      ring
    rw [hsplit, lt_div_iff₀ (Real.rpow_pos_of_pos hn0 _)] at hgt
    exact hgt

end DenseSetsWithoutLargeSumsets
