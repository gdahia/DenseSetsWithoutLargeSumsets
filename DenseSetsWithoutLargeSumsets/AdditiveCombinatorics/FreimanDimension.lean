/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.FreimanDimensionSumsetBounds

/-!
# A self-sumset bound for the Freiman dimension

This file derives the Freiman-dimension bound used in the small-sumset argument from the summed
lower bound for a union of two finite sets.
-/

namespace DenseSetsWithoutLargeSumsets

open scoped Pointwise

noncomputable section

private lemma truncated_sum_eq {b r : ℕ} (hr : 1 ≤ r) (hrb : r ≤ b) :
    (Finset.Icc 1 (b - 1)).sum (fun t => min (r - 1) (b - t)) =
      Nat.choose r 2 + (b - r) * (r - 1) := by
  classical
  rw [← Finset.Ico_add_one_right_eq_Icc 1 (b - 1)]
  have hreflect :
      (Finset.Ico 1 b).sum (fun t => min (r - 1) (b - t)) =
        (Finset.Ico 1 b).sum (fun s => min (r - 1) s) := by
    convert
      (Finset.sum_Ico_reflect (fun s => min (r - 1) s) 1
        (m := b) (n := b) (Nat.le_succ b)) using 1
    congr 2
    all_goals omega
  rw [Nat.sub_add_cancel (hr.trans hrb), hreflect,
    ← Finset.sum_Ico_consecutive (fun s => min (r - 1) s) hr hrb]
  congr 1
  · trans (Finset.Ico 1 r).sum fun s => s
    · apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mem_Ico] at hs
      exact Nat.min_eq_right (by omega)
    · rw [← Nat.sub_add_cancel hr]
      rw [Finset.Ico_add_one_right_eq_Icc 1 (r - 1)]
      simpa [Nat.sub_add_cancel hr] using (Nat.sum_Icc_choose (r - 1) 1)
  · trans (Finset.Ico r b).sum fun _s => r - 1
    · apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mem_Ico] at hs
      exact Nat.min_eq_left (by omega)
    · simp [Finset.sum_const, Nat.card_Ico]

private lemma truncated_bound_contradiction {b r κ : ℚ} (hr : 0 < r) (hrb : r ≤ b)
    (hκr : 2 * κ ≤ r)
    (hbound : b + (r * (r - 1) / 2 + (b - r) * (r - 1)) ≤ κ * b) : False := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hκr) (hr.le.trans hrb),
    mul_nonneg hr.le (sub_nonneg.mpr hrb)]

private lemma lt_two_mul_of_truncated_bound {b r κ : ℕ} (hr : 1 ≤ r) (hrb : r ≤ b)
    (hbound : b + (Nat.choose r 2 + (b - r) * (r - 1)) ≤ κ * b) :
    r < 2 * κ := by
  by_contra hnot
  refine truncated_bound_contradiction (b := (b : ℚ)) (r := (r : ℚ)) (κ := (κ : ℚ))
    ?_ ?_ ?_ ?_
  · exact_mod_cast hr
  · exact_mod_cast hrb
  · exact_mod_cast Nat.le_of_not_gt hnot
  · rw [← Nat.cast_choose_two, ← Nat.cast_sub hrb]
    exact_mod_cast hbound

/-- If `#(X + X) ≤ κ #X`, then `X` has Freiman dimension at most `2 * κ - 1`. -/
theorem freimanDim_le_two_mul_sub_one_of_card_add_le {q κ : ℕ} (X : Finset (ZMod q))
    (_hq : Nat.Prime q)
    (hXX : (X + X).card ≤ κ * X.card) : freimanDim X ≤ 2 * κ - 1 := by
  classical
  let r := freimanDim X
  have hrX : r ≤ X.card := by
    dsimp [r, freimanDim]
    exact Nat.findGreatest_le X.card
  by_cases hr0 : r = 0
  · simp [r, hr0]
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
  have hX : X.Nonempty := Finset.card_pos.mp (hr.trans hrX)
  refine Nat.le_sub_one_of_lt (lt_two_mul_of_truncated_bound hr hrX ?_)
  rw [← truncated_sum_eq hr hrX]
  refine (card_add_sum_min_le_of_freimanDim_union r X X hr hX hX le_rfl ?_).trans hXX
  · simp [r]

end

end DenseSetsWithoutLargeSumsets
