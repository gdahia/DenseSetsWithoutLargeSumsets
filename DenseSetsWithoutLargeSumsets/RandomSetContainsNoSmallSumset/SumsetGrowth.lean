/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.Constants
import SumOfSetsInSeveralDimensions.FreimanDimensionSumsetBounds
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Data.Nat.Choose.Cast

/-!
# Sumsets of two sets with a small sumset

Let `A` and `B` be sets of size `k` in an abelian group with `|A + B| ≤ C * k`. By the
Plünnecke–Ruzsa inequality, `|A + A|` and `|B + B|` are at most `C ^ 2 * k`. So `A ∪ B`, and every
`A₀ ∪ B₀` with `A₀ ⊆ A`, `B₀ ⊆ B` and `|A₀ ∪ B₀| ≥ k / 2`, has doubling at most
`κ C = 6 * C ^ 2`. We also bound `|A + B|` from below in terms of `freimanDim (A ∪ B)`.

## Main statements

* `card_union_add_union_le_κ_mul`: `|(A ∪ B) + (A ∪ B)| ≤ κ C * k`.
* `card_large_subset_union_add_union_le_κ_mul_card`:
  `|(A₀ ∪ B₀) + (A₀ ∪ B₀)| ≤ κ C * |A₀ ∪ B₀|`.
* `asym_large_subsets_sum_lower`: if `freimanDim (A ∪ B) = r` with `1 ≤ r ≤ ε * k` and
  `|A| ≥ |B| ≥ (1 - ε) * k`, then `|A + B| ≥ (1 - 2 * ε) * r * k`.
-/

@[expose] public section

namespace DenseSetsWithoutLargeSumsets

open Finset SumOfSetsInSeveralDimensions
open scoped Pointwise

noncomputable section

private lemma card_add_self_le_sq_mul {G : Type*} [DecidableEq G] [AddCommGroup G]
    {A B : Finset G} {k : ℕ} {C : ℝ} (hAcard : #A = k) (hBcard : #B = k)
    (hAB : #(A + B) ≤ C * k) :
    #(A + A) ≤ C ^ 2 * k := by
  obtain rfl | hk := eq_or_ne k 0
  · simp [card_eq_zero.1 hAcard]
  have h := pluennecke_ruzsa_inequality_nsmul_add (card_pos.1 (hBcard ▸ hk.bot_lt)) A 2
  rw [add_comm, hBcard, two_nsmul] at h
  refine le_trans (b := (#(A + B) / k : ℝ) ^ 2 * k) ?_ ?_
  · simpa using (NNRat.cast_le (K := ℝ)).2 h
  · gcongr
    exact (div_le_iff₀ (mod_cast hk.bot_lt)).2 hAB

private lemma card_union_add_union_le_three_mul {G : Type*} [DecidableEq G] [AddCommGroup G]
    {A B : Finset G} {k : ℕ} {C : ℝ} (hAcard : #A = k) (hBcard : #B = k)
    (hAB : #(A + B) ≤ C * k) (hC : 1 ≤ C) :
    #((A ∪ B) + (A ∪ B)) ≤ 3 * C ^ 2 * k := by
  have h : (#((A + A) ∪ ((A + B) ∪ (B + B))) : ℝ) ≤ #(A + A) + (#(A + B) + #(B + B)) :=
    mod_cast (card_union_le _ _).trans (Nat.add_le_add_left (card_union_le _ _) _)
  rw [union_add, add_union, add_union, add_comm B A, union_assoc, union_left_idem]
  linarith [card_add_self_le_sq_mul hAcard hBcard hAB,
    card_add_self_le_sq_mul hBcard hAcard (add_comm A B ▸ hAB),
    mul_le_mul_of_nonneg_right (le_self_pow₀ hC two_ne_zero) (Nat.cast_nonneg (α := ℝ) k)]

/-- If `|A| = |B| = k` and `|A + B| ≤ C * k`, then `|(A ∪ B) + (A ∪ B)| ≤ κ C * k`. -/
lemma card_union_add_union_le_κ_mul {G : Type*} [DecidableEq G] [AddCommGroup G]
    {A B : Finset G} {k : ℕ} {C : ℝ}
    (hAcard : #A = k) (hBcard : #B = k) (hAB : #(A + B) ≤ C * k) :
    #((A ∪ B) + (A ∪ B)) ≤ κ C * k := by
  obtain rfl | hk := eq_or_ne k 0
  · simp [card_eq_zero.1 hAcard, card_eq_zero.1 hBcard]
  have hkAB := card_le_card_add_right (s := A) (card_pos.1 (hBcard ▸ hk.bot_lt))
  rw [hAcard, ← Nat.cast_le (α := ℝ)] at hkAB
  have hC : 1 ≤ C := le_of_mul_le_mul_right (by linarith) (Nat.cast_pos.2 hk.bot_lt)
  rw [κ]
  linarith [card_union_add_union_le_three_mul hAcard hBcard hAB hC,
    mul_nonneg (sq_nonneg C) (Nat.cast_nonneg (α := ℝ) k)]

/-- If `|A| = |B| = k`, `|A + B| ≤ C * k` with `C ≥ 1`, and `A₀ ⊆ A`, `B₀ ⊆ B` satisfy
`|A₀ ∪ B₀| ≥ k / 2`, then `|(A₀ ∪ B₀) + (A₀ ∪ B₀)| ≤ κ C * |A₀ ∪ B₀|`. -/
lemma card_large_subset_union_add_union_le_κ_mul_card
    {G : Type*} [DecidableEq G] [AddCommGroup G]
    {A B A₀ B₀ : Finset G} {k : ℕ} {C : ℝ}
    (hA₀A : A₀ ⊆ A) (hB₀B : B₀ ⊆ B)
    (hAcard : #A = k) (hBcard : #B = k)
    (hAB : #(A + B) ≤ C * k)
    (hXlower : (k : ℝ) / 2 ≤ (#(A₀ ∪ B₀) : ℝ))
    (hC_one : 1 ≤ C) :
    (#((A₀ ∪ B₀) + (A₀ ∪ B₀)) : ℝ) ≤ κ C * (#(A₀ ∪ B₀) : ℝ) := by
  rw [κ]
  linarith [card_union_add_union_le_three_mul hAcard hBcard hAB hC_one,
    (Nat.cast_le (α := ℝ)).2 (card_le_card (add_subset_add (union_subset_union hA₀A hB₀B)
      (union_subset_union hA₀A hB₀B))), mul_le_mul_of_nonneg_left hXlower (sq_nonneg C)]

/-- Let `A` and `B` be nonempty with `|B| ≤ |A|` and `freimanDim (A ∪ B) = r ≥ 1`. If
`r ≤ ε * k` and `|A|, |B| ≥ (1 - ε) * k`, then `|A + B| ≥ (1 - 2 * ε) * r * k`. -/
lemma asym_large_subsets_sum_lower
    {G : Type*} [DecidableEq G] [AddCommMonoid G]
    {A B : Finset G} {r k : ℕ} {ε : ℝ}
    (hr : 1 ≤ r) (hB : B.Nonempty) (hBA : #B ≤ #A) (hdim : freimanDim (A ∪ B) = r)
    (hr_le_εk : (r : ℝ) ≤ ε * (k : ℝ))
    (hA_large : (1 - ε) * (k : ℝ) ≤ (#A : ℝ))
    (hB_large : (1 - ε) * (k : ℝ) ≤ (#B : ℝ)) :
    (1 - 2 * ε) * (r : ℝ) * (k : ℝ) ≤ (#(A + B) : ℝ) := by
  have hr₁ : (1 : ℝ) ≤ r := mod_cast hr
  have h := card_add_mul_card_sub_choose_le_card_add_of_freimanDim_union hr hB hBA hdim
  rw [tsub_le_iff_right, ← Nat.cast_le (α := ℝ)] at h
  push_cast [Nat.cast_sub hr, Nat.cast_choose_two] at h
  linarith [mul_le_mul_of_nonneg_left hB_large (sub_nonneg.2 hr₁),
    mul_le_mul_of_nonneg_left hr_le_εk (zero_le_one.trans hr₁),
    mul_nonneg (zero_le_one.trans hr₁) (sub_nonneg.2 hr₁)]

end

end DenseSetsWithoutLargeSumsets
