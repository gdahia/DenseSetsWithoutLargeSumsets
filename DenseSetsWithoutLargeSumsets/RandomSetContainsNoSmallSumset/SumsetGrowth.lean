/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.WitnessPairProbability
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.FreimanDimension
import DenseSetsWithoutLargeSumsets.Probability
import DenseSetsWithoutLargeSumsets.Common
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.GeneralizedArithmeticProgression
import DenseSetsWithoutLargeSumsets.LargeSumsetsFromMediumSizedSubsets.MediumSizedSubsets
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.Chang.Reduction
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.NumberTheory.Bertrand

/-!
Doubling of the union of two sets with a small mixed sumset.

Plünnecke--Ruzsa consequences of `#(A + B) ≤ C * k` for `k`-sets `A, B`: the self-sumset of
`A ∪ B` doubles by at most `κ C`, and this doubling bound survives passing to large subsets
(`card_union_add_union_le_κ_mul`, `card_large_subset_union_add_union_le_κ_mul_card`), plus the
asymmetric lower bound on `#(A + B)` coming from a Freiman-dimension lower bound on `A ∪ B`.
-/

namespace DenseSetsWithoutLargeSumsets

open Nat hiding div_pos
open scoped Pointwise

noncomputable section

private lemma card_add_self_le_sq_mul {G : Type*} [DecidableEq G] [AddCommGroup G]
    {A B : Finset G} {k : ℕ} {C : ℝ} (hk : k ≠ 0)
    (_hAcard : A.card = k) (hBcard : B.card = k) (hAB : (A + B).card ≤ C * k) :
    (A + A).card ≤ C ^ 2 * k := by
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have hratio : ((A + B).card : ℝ) / k ≤ C := by
    refine (div_le_iff₀ ?_).mpr hAB
    exact_mod_cast hkpos
  have hratio_nonneg : 0 ≤ ((A + B).card : ℝ) / k := by positivity
  refine le_trans
    (b := (((A + B).card : ℝ) / k) ^ 2 * k) ?_ ?_
  · rw [← two_nsmul A]
    have hplu :
        ((2 • A).card : ℚ≥0) ≤ (((A + B).card : ℚ≥0) / k) ^ 2 * k := by
      rw [← hBcard, add_comm]
      apply Finset.pluennecke_ruzsa_inequality_nsmul_add
      rw [← Finset.card_pos, hBcard]
      exact hkpos
    simpa using (NNRat.cast_le (K := ℝ)).mpr hplu
  · apply mul_le_mul_of_nonneg_right
    · nlinarith [mul_nonneg (sub_nonneg.mpr hratio)
        (add_nonneg (hratio_nonneg.trans hratio) hratio_nonneg)]
    · positivity

/--
Pluennecke-Ruzsa input for the small-sumset argument: two `k`-sets with small mixed sumset
have a union whose self-sumset has cardinality at most `κ C * k`.
-/
lemma card_union_add_union_le_κ_mul {G : Type*} [DecidableEq G] [AddCommGroup G]
    {A B : Finset G} {k : ℕ} {C : ℝ}
    (hAcard : A.card = k) (hBcard : B.card = k) (hAB : (A + B).card ≤ C * k) :
    ((A ∪ B) + (A ∪ B)).card ≤ κ C * k := by
  by_cases hk : k = 0
  · rw [hk] at hAcard hBcard ⊢
    rw [Finset.card_eq_zero] at hAcard hBcard
    simp [hAcard, hBcard]
  · rw [Finset.union_add, Finset.add_union, Finset.add_union, add_comm B A]
    simp only [Finset.union_assoc, Finset.union_left_idem]
    refine le_trans (b := ((A + A).card : ℝ) + (A + B).card + (B + B).card) ?_ ?_
    · norm_cast
      simpa only [Finset.union_assoc] using
        (Finset.card_union_le ((A + A) ∪ (A + B)) (B + B)).trans
          (Nat.add_le_add_right (Finset.card_union_le (A + A) (A + B)) (B + B).card)
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hk_le_sum : k ≤ (A + B).card := by
      rw [← hAcard]
      apply Finset.card_le_card_add_right
      apply Finset.card_pos.mp
      rw [hBcard]
      exact hkpos
    have hCone : (1 : ℝ) ≤ C := by
      nlinarith [(by exact_mod_cast hkpos : (0 : ℝ) < k),
        (by exact_mod_cast hk_le_sum : (k : ℝ) ≤ (A + B).card), hAB]
    have hBB : ((B + B).card : ℝ) ≤ C ^ 2 * k := by
      exact_mod_cast card_add_self_le_sq_mul (A := B) (B := A) hk hBcard hAcard
        (by simpa [add_comm] using hAB)
    rw [κ]
    nlinarith [hCone, card_add_self_le_sq_mul (A := A) (B := B) hk hAcard hBcard hAB,
      hBB, hAB]

lemma card_large_subset_union_add_union_le_κ_mul_card
    {G : Type*} [DecidableEq G] [AddCommGroup G]
    {A B A₀ B₀ : Finset G} {k : ℕ} {C : ℝ}
    (hA₀A : A₀ ⊆ A) (hB₀B : B₀ ⊆ B)
    (hAcard : A.card = k) (hBcard : B.card = k)
    (hAB : (A + B).card ≤ C * k)
    (hXlower : (k : ℝ) / 2 ≤ ((A₀ ∪ B₀).card : ℝ))
    (hC_one : 1 ≤ C) :
    (((A₀ ∪ B₀) + (A₀ ∪ B₀)).card : ℝ) ≤
      κ C * ((A₀ ∪ B₀).card : ℝ) := by
  by_cases hk : k = 0
  · rw [hk] at hAcard hBcard
    simp [
      Finset.card_eq_zero.mp
        (Nat.eq_zero_of_le_zero (by simpa [hAcard] using Finset.card_le_card hA₀A)),
      Finset.card_eq_zero.mp
        (Nat.eq_zero_of_le_zero (by simpa [hBcard] using Finset.card_le_card hB₀B))]
  · refine le_trans
      (b := ((A + A).card : ℝ) + (A + B).card + (B + B).card) ?_ ?_
    · exact_mod_cast ((Finset.card_le_card (by
        intro x hx
        rw [Finset.mem_add] at hx
        rcases hx with ⟨a, ha, b, hb, rfl⟩
        rw [Finset.mem_union] at ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · simp [Finset.add_mem_add (hA₀A ha) (hA₀A hb)]
        · simp [Finset.add_mem_add (hA₀A ha) (hB₀B hb)]
        · simp [(by
            simpa [add_comm] using
              (Finset.add_mem_add (hA₀A hb) (hB₀B ha) : b + a ∈ A + B) :
            a + b ∈ A + B)]
        · simp [Finset.add_mem_add (hB₀B ha) (hB₀B hb)])).trans
          ((Finset.card_union_le ((A + A) ∪ (A + B)) (B + B)).trans
            (Nat.add_le_add_right (Finset.card_union_le (A + A) (A + B)) (B + B).card)))
    · refine le_trans (b := C ^ 2 * k + C * k + C ^ 2 * k) ?_ ?_
      · nlinarith [card_add_self_le_sq_mul hk hAcard hBcard hAB,
          hAB, card_add_self_le_sq_mul hk hBcard hAcard
            (by simpa [add_comm] using hAB)]
      · refine le_trans (b := 3 * C ^ 2 * k) ?_ ?_
        · nlinarith [sq_nonneg C, hC_one]
        · refine (by nlinarith [sq_nonneg C] :
            3 * C ^ 2 * k ≤ 6 * C ^ 2 * ((A₀ ∪ B₀).card : ℝ)).trans_eq ?_
          rw [κ]

private lemma choose_succ_two_le_sq (r : ℕ) :
    Nat.choose (r + 1) 2 ≤ r * r := by
  rw [Nat.choose_two_right]
  apply Nat.div_le_of_le_mul
  rw [Nat.add_sub_cancel]
  nlinarith

private lemma choose_succ_two_le_add_pred_mul {r a b : ℕ}
    (hr : 1 ≤ r) (hrb : r ≤ b) (hba : b ≤ a) :
    Nat.choose (r + 1) 2 ≤ a + (r - 1) * b := by
  refine (choose_succ_two_le_sq r).trans ?_
  refine (Nat.mul_le_mul_left r hrb).trans ?_
  rw [← Nat.sub_add_cancel hr]
  rw [Nat.add_mul, one_mul]
  rw [add_comm ((r - 1) * b) b]
  exact Nat.add_le_add_right hba ((r - 1) * b)

lemma asym_large_subsets_sum_lower
    {G : Type*} [DecidableEq G] [AddCommMonoid G]
    {A B : Finset G} {r k : ℕ} {ε : ℝ}
    (hr : 1 ≤ r) (hA : A.Nonempty) (hB : B.Nonempty)
    (hBA : B.card ≤ A.card) (hdim : freimanDim (A ∪ B) = r)
    (_hε_nonneg : 0 ≤ ε) (hε_le_half : ε ≤ 1 / 2)
    (hr_le_εk : (r : ℝ) ≤ ε * (k : ℝ))
    (hA_large : (1 - ε) * (k : ℝ) ≤ (A.card : ℝ))
    (hB_large : (1 - ε) * (k : ℝ) ≤ (B.card : ℝ)) :
    (1 - 2 * ε) * (r : ℝ) * (k : ℝ) ≤ ((A + B).card : ℝ) := by
  refine (by
    rw [Nat.cast_sub hr]
    norm_num
    nlinarith [hA_large, hB_large,
      (by exact_mod_cast hr : (1 : ℝ) ≤ (r : ℝ)),
      (by
        nlinarith [
          (by exact_mod_cast choose_succ_two_le_sq r :
            (Nat.choose (r + 1) 2 : ℝ) ≤ (r : ℝ) * (r : ℝ)),
          mul_le_mul_of_nonneg_left hr_le_εk (by positivity : 0 ≤ (r : ℝ))] :
        (Nat.choose (r + 1) 2 : ℝ) ≤ ε * (r : ℝ) * (k : ℝ))] :
    (1 - 2 * ε) * (r : ℝ) * (k : ℝ) ≤
      (A.card : ℝ) + ((r - 1 : ℕ) : ℝ) * (B.card : ℝ) -
        (Nat.choose (r + 1) 2 : ℝ)).trans ?_
  rw [← Nat.cast_mul, ← Nat.cast_add]
  rw [← Nat.cast_sub (choose_succ_two_le_add_pred_mul hr
    (by
      exact_mod_cast (by nlinarith : (r : ℝ) ≤ (B.card : ℝ)) : r ≤ B.card)
    hBA)]
  exact_mod_cast card_add_lower_bound_of_freimanDim_union (G := G) r A B hr hA hB hBA hdim

end

end DenseSetsWithoutLargeSumsets
