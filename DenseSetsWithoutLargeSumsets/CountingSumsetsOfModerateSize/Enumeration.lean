/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.SmallSumsetIsomorphismClasses.CoreParameters
public import DenseSetsWithoutLargeSumsets.Common
public import DenseSetsWithoutLargeSumsets.CountingSumsetsOfModerateSize.BoundedFreimanDimSets
import SumOfSetsInSeveralDimensions.FreimanDimensionSumsetBounds
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa

/-!
# Counting sumsets of moderate size

Let `Y = A + B` with `A, B ⊆ [n]`, `|A| = |B| = k` and `|Y| ≤ m < k * (k + 1) / 2`. The set
`X = A ∪ B` has between `k` and `2 * k` elements, Freiman dimension at most `2 * m / k` and, by
the Ruzsa triangle inequality, `|X + X| ≤ 3 * m ^ 2 / k`. Since `A` and `B` are `k`-subsets of
`X`, the number of such `Y` is at most the sum over `k ≤ t ≤ 2 * k` of the number of sets `X ⊆ [n]`
of size `t` with these properties times `(t.choose k) ^ 2`. The counts of the sets `X` are in
`CountingSumsetsOfModerateSize.BoundedFreimanDimSets`. This is Section 3 of *Dense sets without
large sumsets* (Dahia, Marciano, Souza).

## Main definitions

* `pairSumsetsFamily n k m`: the sets `A + B` with `A, B ⊆ [n]`, `|A| = |B| = k` and
  `|A + B| ≤ m`.
* `moderateSumsetAuxExponent`: the exponent `ξ = 2⁻⁸`.

## Main statements

* `pairSumsetsFamily_ncard_le`: if `m < k * (k + 1) / 2`, then
  `|pairSumsetsFamily n k m| ≤ n ^ (2 * m / k + 1) * k ^ (24 * k)`.
* `pairSumsetsFamily_ncard_le_of_small_sumset`: if moreover `k` is large and `m ≤ k ^ (1 + c)` with
  `c ≤ 2⁻⁸`, then `|pairSumsetsFamily n k m|` is at most
  `n ^ (2 * m / k + 1) * (6 * e * m / k) ^ (6 * k) * exp (k ^ (1 - 2 * c))`.
-/

@[expose] public section

namespace DenseSetsWithoutLargeSumsets

open Finset CountingSetsWithSmallSumset SumOfSetsInSeveralDimensions
open scoped Pointwise

noncomputable section

/-- The family of sets `Y ⊆ [2n]` with `|Y| ≤ m` that are a sumset `A + B` of two `k`-subsets `A`,
`B` of `[n]`. -/
def pairSumsetsFamily (n k m : ℕ) : Set (Finset ℕ) :=
  {Y : Finset ℕ |
    Y ⊆ interval (2 * n) ∧
      ∃ A B : Finset ℕ,
        A ⊆ interval n ∧ B ⊆ interval n ∧
          #A = k ∧ #B = k ∧ A + B = Y ∧ #Y ≤ m}

/-- The exponent `ξ = 2⁻⁸`. Sumsets of size at most `k ^ (1 + ξ)` are counted with the bound for
sets of small doubling. -/
def moderateSumsetAuxExponent : ℝ :=
  1 / (2 : ℝ) ^ (8 : ℕ)

private lemma add_sum_Icc_sub (k : ℕ) :
    k + ∑ t ∈ Icc 1 (k - 1), (k - t) = k * (k + 1) / 2 := by
  have h (j : ℕ) (hj : j ≤ k) : 2 * ∑ t ∈ Icc 1 j, (k - t) + j * (j + 1) = 2 * j * k := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [sum_Icc_succ_top (by grind)]
      grind
  obtain _ | k := k
  · simp
  grind

/-- If `|A| = |B| = k` and `|A + B| < k * (k + 1) / 2`, then the Freiman dimension of `A ∪ B` is
less than `k`. -/
private lemma freimanDim_union_lt {A B : Finset ℕ} {k m : ℕ} (hk : 0 < k) (hA : #A = k)
    (hB : #B = k) (hAB : #(A + B) ≤ m) (hm : m < k * (k + 1) / 2) : freimanDim (A ∪ B) < k := by
  by_contra! hr
  have h := card_add_sum_min_le_of_freimanDim_union (A := A) (B := B) (by grind)
    (card_pos.mp (by grind)) (by grind) rfl
  rw [hA, hB, sum_congr rfl (g := fun t ↦ k - t) (by grind), add_sum_Icc_sub] at h
  grind

/-- If `|A| = |B| = k` and `|A + B| ≤ m < k * (k + 1) / 2`, then the Freiman dimension of `A ∪ B`
is at most `2 * m / k`. -/
private lemma freimanDim_union_le_two_mul_div {A B : Finset ℕ} {k m : ℕ} (hk : 0 < k)
    (hA : #A = k) (hB : #B = k) (hAB : #(A + B) ≤ m) (hm : m < k * (k + 1) / 2) :
    freimanDim (A ∪ B) ≤ 2 * m / k := by
  have hr := freimanDim_union_lt hk hA hB hAB hm
  rw [Nat.le_div_iff_mul_le hk]
  generalize hr' : freimanDim (A ∪ B) = r at hr ⊢
  obtain _ | r := r
  · simp
  have h := card_add_mul_card_sub_choose_le_card_add_of_freimanDim_union (by grind)
    (card_pos.mp (by grind)) (by grind) hr'
  rw [hA, hB, Nat.choose_two_right, add_tsub_cancel_right] at h
  grind [Nat.div_mul_le_self ((r + 1 + 1) * (r + 1)) 2, Nat.mul_le_mul_right (r + 1) hr]

private lemma card_add_self_le_mul_div {A B : Finset ℕ} {k m : ℕ} (hk : 0 < k) (hB : #B = k)
    (hAB : #(A + B) ≤ m) : #(A + A) ≤ m * m / k := by
  rw [Nat.le_div_iff_mul_le hk, ← hB, ← natCastImage_sum_card, ← natCastImage_card B]
  refine (ruzsa_triangle_inequality_add_add_add _ _ _).trans ?_
  rw [natCastImage_sum_card, natCastImage_sum_card, add_comm B]
  exact Nat.mul_le_mul hAB hAB

/-- If `|A| = |B| = k` and `|A + B| ≤ m`, then `|(A ∪ B) + (A ∪ B)| ≤ 3 * m ^ 2 / k`. -/
private lemma card_union_add_union_le {A B : Finset ℕ} {k m : ℕ} (hk : 0 < k) (hA : #A = k)
    (hB : #B = k) (hAB : #(A + B) ≤ m) : #((A ∪ B) + (A ∪ B)) ≤ 3 * (m * m / k) := by
  have hkm : k ≤ m := hA ▸ (card_le_card_add_right (card_pos.mp (by grind))).trans hAB
  have hm := (Nat.le_div_iff_mul_le hk).2 (Nat.mul_le_mul_left m hkm)
  have hAA := card_add_self_le_mul_div hk hB hAB
  have hBB := card_add_self_le_mul_div hk hA (add_comm A B ▸ hAB)
  rw [union_add, add_union, add_union, add_comm B A, union_assoc, union_left_idem]
  grind [card_union_le]

/-- The sumsets `A + B` of two `k`-subsets `A`, `B` of a set of the family `𝒳`. -/
private def subsetPairSums (k : ℕ) (𝒳 : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  𝒳.biUnion fun X ↦ (X.powersetCard k ×ˢ X.powersetCard k).image fun p ↦ p.1 + p.2

private lemma add_mem_subsetPairSums {k : ℕ} {𝒳 : Finset (Finset ℕ)} {A B : Finset ℕ}
    (hA : #A = k) (hB : #B = k) (h : A ∪ B ∈ 𝒳) : A + B ∈ subsetPairSums k 𝒳 := by
  simp only [subsetPairSums, mem_biUnion, mem_image, mem_product, mem_powersetCard, Prod.exists]
  exact ⟨A ∪ B, h, A, B, ⟨⟨subset_union_left, hA⟩, subset_union_right, hB⟩, rfl⟩

private lemma card_subsetPairSums_le {k t : ℕ} {𝒳 : Finset (Finset ℕ)} (h : ∀ X ∈ 𝒳, #X = t) :
    #(subsetPairSums k 𝒳) ≤ #𝒳 * (t.choose k * t.choose k) := by
  refine card_biUnion_le_card_mul _ _ _ fun X hX ↦ card_image_le.trans ?_
  simp [h X hX]

/-- Let `𝒳 t` be a family of `t`-subsets of `[n]` for each `t`. If every `Y ∈ 𝒴` is a sumset
`A + B` of two `k`-sets with `A ∪ B ∈ 𝒳 |A ∪ B|`, then
`|𝒴| ≤ ∑ t ∈ [k, 2 * k], |𝒳 t| * (t.choose k) ^ 2`. -/
private lemma ncard_le_sum_ncard_mul_choose {𝒴 : Set (Finset ℕ)} {𝒳 : ℕ → Set (Finset ℕ)}
    {n k : ℕ} (h𝒳 : ∀ t, ∀ X ∈ 𝒳 t, X ⊆ interval n ∧ #X = t)
    (h𝒴 : ∀ Y ∈ 𝒴, ∃ A B : Finset ℕ, #A = k ∧ #B = k ∧ A + B = Y ∧ A ∪ B ∈ 𝒳 #(A ∪ B)) :
    𝒴.ncard ≤ ∑ t ∈ Icc k (2 * k), (𝒳 t).ncard * t.choose k * t.choose k := by
  have hfin (t : ℕ) : (𝒳 t).Finite :=
    (interval n).powerset.finite_toSet.subset fun X hX ↦ mem_powerset.2 (h𝒳 t X hX).1
  refine (Set.ncard_le_ncard (t := ↑((Icc k (2 * k)).biUnion fun t ↦
    subsetPairSums k (hfin t).toFinset)) ?_ (finite_toSet _)).trans ?_
  · intro Y hY
    obtain ⟨A, B, hA, hB, rfl, hX⟩ := h𝒴 Y hY
    rw [mem_coe, mem_biUnion]
    refine ⟨#(A ∪ B), mem_Icc.2 ⟨hA ▸ card_le_card subset_union_left, ?_⟩,
      add_mem_subsetPairSums hA hB ((hfin _).mem_toFinset.2 hX)⟩
    grind [card_union_le]
  rw [Set.ncard_coe_finset]
  refine card_biUnion_le.trans (sum_le_sum ?_)
  intro t _
  rw [Set.ncard_eq_toFinset_card _ (hfin t), mul_assoc]
  exact card_subsetPairSums_le fun X hX ↦ (h𝒳 t X ((hfin t).mem_toFinset.1 hX)).2

private lemma pairSumsetsFamily_ncard_le_sum {n k m : ℕ} (hk : 0 < k)
    (hm : m < k * (k + 1) / 2) :
    (pairSumsetsFamily n k m).ncard ≤ ∑ t ∈ Icc k (2 * k),
      (boundedFreimanDimSets n (2 * m / k) t).ncard * t.choose k * t.choose k := by
  refine ncard_le_sum_ncard_mul_choose (fun t X hX ↦ ⟨hX.1, hX.2.1⟩) ?_
  rintro Y ⟨-, A, B, hAn, hBn, hA, hB, rfl, hY⟩
  exact ⟨A, B, hA, hB, rfl, union_subset hAn hBn, rfl,
    freimanDim_union_le_two_mul_div hk hA hB hY hm⟩

private lemma pairSumsetsFamily_ncard_le_sum_smallSumset {n k m : ℕ} (hk : 0 < k)
    (hm : m < k * (k + 1) / 2) :
    (pairSumsetsFamily n k m).ncard ≤ ∑ t ∈ Icc k (2 * k),
      (smallSumsetFreimanDimSets n (2 * m / k) (3 * (m * m / k)) t).ncard * t.choose k *
        t.choose k := by
  refine ncard_le_sum_ncard_mul_choose (fun t X hX ↦ ⟨hX.1, hX.2.1⟩) ?_
  rintro Y ⟨-, A, B, hAn, hBn, hA, hB, rfl, hY⟩
  exact ⟨A, B, hA, hB, rfl, union_subset hAn hBn, rfl,
    freimanDim_union_le_two_mul_div hk hA hB hY hm, card_union_add_union_le hk hA hB hY⟩

private lemma pairSumsetsFamily_eq_empty {n k m : ℕ} (h : n < k ∨ m < k) :
    pairSumsetsFamily n k m = ∅ := by
  refine Set.eq_empty_of_forall_notMem ?_
  rintro Y ⟨-, A, B, hAn, -, rfl, hB, rfl, hY⟩
  obtain h | h := h
  · exact h.not_ge (by simpa [interval] using card_le_card hAn)
  · exact h.not_ge ((card_le_card_add_right (card_pos.mp (by grind))).trans hY)

/-- For `k ≥ 2`, `(k + 1) * (2 * k) ^ (10 * k) ≤ k ^ (24 * k)`. -/
lemma medium_counting_factor_bound {k : ℕ} (hk : 2 ≤ k) :
    (#(Icc k (2 * k)) : ℝ) * ((2 * k : ℕ) : ℝ) ^ (10 * k) ≤ (k : ℝ) ^ (24 * k) := by
  norm_cast
  rw [Nat.card_Icc]
  refine (Nat.mul_le_mul_right _ (by grind : 2 * k + 1 - k ≤ 2 * k)).trans ?_
  rw [← pow_succ']
  refine (Nat.pow_le_pow_left (by nlinarith : 2 * k ≤ k ^ 2) _).trans ?_
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by grind) (by grind)

private lemma six_le_rpow {k : ℕ} {u : ℝ} (hk : 2 ^ 200 ≤ k) (hu : 3 / 128 ≤ u) :
    (6 : ℝ) ≤ (k : ℝ) ^ u := by
  have hk' : (2 : ℝ) ^ (128 : ℕ) ≤ k := le_trans (by norm_num) (Nat.cast_le.2 hk)
  have h : (6 : ℝ) ≤ ((2 : ℝ) ^ (128 : ℕ)) ^ ((3 : ℝ) / 128) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
    norm_num
  exact h.trans ((Real.rpow_le_rpow (by positivity) hk' (by norm_num)).trans
    (Real.rpow_le_rpow_of_exponent_le (le_trans (by norm_num) hk') hu))

private lemma three_mul_sq_div_le_rpow {k m t : ℕ} {c : ℝ} (hc : c ≤ 1 / (2 : ℝ) ^ (8 : ℕ))
    (hk : 2 ^ 200 ≤ k) (hm : (m : ℝ) ≤ (k : ℝ) ^ (1 + c)) (hkt : k ≤ t) :
    ((3 * (m * m / k) : ℕ) : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30) / 2 := by
  have hk₀ : (0 : ℝ) < k := mod_cast (by grind : 0 < k)
  have h₁ : ((m * m / k : ℕ) : ℝ) ≤ (k : ℝ) ^ (1 + 2 * c) := by
    refine Nat.cast_div_le.trans ?_
    rw [div_le_iff₀ hk₀, ← Real.rpow_add_one hk₀.ne', Nat.cast_mul]
    refine (mul_le_mul hm hm (by positivity) (by positivity)).trans_eq ?_
    rw [← Real.rpow_add hk₀]
    ring_nf
  have h₂ := mul_le_mul_of_nonneg_right
    (six_le_rpow (u := 31 / 30 - (1 + 2 * c)) hk (by linarith))
    (Real.rpow_nonneg hk₀.le (1 + 2 * c))
  rw [← Real.rpow_add hk₀, sub_add_cancel] at h₂
  have h₃ := Real.rpow_le_rpow hk₀.le (Nat.cast_le (α := ℝ).2 hkt) (by norm_num : (0 : ℝ) ≤ 31 / 30)
  push_cast
  linarith

private lemma pow_mul_choose_sq_le {k m t : ℕ} (hk : 0 < k) (hkm : k ≤ m) (hkt : k ≤ t)
    (htk : t ≤ 2 * k) :
    ((2 * Real.exp 1 * ((3 * (m * m / k) : ℕ) : ℝ)) / (t : ℝ)) ^ t *
        ((t.choose k : ℝ) * (t.choose k : ℝ)) ≤
      ((6 * Real.exp 1 * (m : ℝ)) / (k : ℝ)) ^ (6 * k) := by
  have hk₀ : (0 : ℝ) < k := mod_cast hk
  have hkt' : (k : ℝ) ≤ t := mod_cast hkt
  have hq : (1 : ℝ) ≤ m / k := (one_le_div₀ hk₀).2 (mod_cast hkm)
  have hE : (2 : ℝ) ≤ 6 * Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hfloor : ((m * m / k : ℕ) : ℝ) ≤ (m / k : ℝ) ^ 2 * t := by
    refine Nat.cast_div_le.trans (le_trans (le_of_eq ?_)
      (mul_le_mul_of_nonneg_left hkt' (by positivity)))
    push_cast
    field_simp
  have hbase : 2 * Real.exp 1 * ((3 * (m * m / k) : ℕ) : ℝ) / t ≤
      6 * Real.exp 1 * (m / k : ℝ) ^ 2 := by
    rw [div_le_iff₀ (hk₀.trans_le hkt')]
    push_cast
    linarith [mul_le_mul_of_nonneg_left hfloor (Real.exp_pos 1).le]
  have hchoose : (t.choose k : ℝ) * t.choose k ≤ (6 * Real.exp 1) ^ (4 * k) := by
    have h : (t.choose k : ℝ) ≤ 2 ^ t := mod_cast Nat.choose_le_two_pow t k
    refine (mul_le_mul h h (by positivity) (by positivity)).trans ?_
    rw [← pow_add]
    exact (pow_le_pow_right₀ one_le_two (by grind)).trans (pow_le_pow_left₀ zero_le_two hE _)
  refine (mul_le_mul (pow_le_pow_left₀ (by positivity) hbase t) hchoose (by positivity)
    (by positivity)).trans ?_
  refine (mul_le_mul_of_nonneg_right (pow_le_pow_right₀
    (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hq)) htk) (by positivity)).trans ?_
  rw [mul_div_assoc, mul_pow _ (m / k : ℝ)]
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hq (by grind : 4 * k ≤ 6 * k)) (by positivity))
  ring

private lemma card_Icc_mul_exp_le {k : ℕ} {c : ℝ} (hc : c ≤ 1 / (2 : ℝ) ^ (8 : ℕ))
    (hk : 2 ^ 200 ≤ k) :
    (#(Icc k (2 * k)) : ℝ) * Real.exp (((2 * k : ℕ) : ℝ) ^ ((31 : ℝ) / 32)) ≤
      Real.exp ((k : ℝ) ^ (1 - 2 * c)) := by
  have hk₀ : 0 < k := by grind
  have hk₀' : (0 : ℝ) < k := mod_cast hk₀
  have hcard : (#(Icc k (2 * k)) : ℝ) ≤ Real.exp (Real.log ((2 * k : ℕ) : ℝ)) := by
    rw [Real.exp_log (mod_cast by grind), Nat.card_Icc]
    exact mod_cast (by grind : 2 * k + 1 - k ≤ 2 * k)
  have h₁ : ((2 * k : ℕ) : ℝ) ^ ((31 : ℝ) / 32) ≤ 2 * (k : ℝ) ^ ((31 : ℝ) / 32) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow zero_le_two hk₀'.le]
    gcongr
    exact (Real.rpow_le_rpow_of_exponent_le one_le_two (by norm_num)).trans_eq (Real.rpow_one 2)
  have h₂ := mul_le_mul_of_nonneg_right
    (six_le_rpow (u := 1 - 2 * c - 31 / 32) hk (by linarith))
    (Real.rpow_nonneg hk₀'.le (31 / 32))
  rw [← Real.rpow_add hk₀', sub_add_cancel] at h₂
  refine (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le).trans ?_
  rw [← Real.exp_add, Real.exp_le_exp]
  linarith [Real.log_le_rpow_div (x := ((2 * k : ℕ) : ℝ)) (by positivity)
    (by norm_num : (0 : ℝ) < 31 / 32), Real.rpow_nonneg hk₀'.le (31 / 32)]

private lemma pow_two_mul_div_add_one_le_rpow {n : ℕ} (k m : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ (2 * m / k + 1) ≤ (n : ℝ) ^ (2 * (m : ℝ) / k + 1) := by
  rw [← Real.rpow_natCast, Nat.cast_add_one]
  refine Real.rpow_le_rpow_of_exponent_le (mod_cast hn) (add_le_add_left ?_ 1)
  exact mod_cast Nat.cast_div_le (α := ℝ) (m := 2 * m) (n := k)

private lemma ncard_boundedFreimanDimSets_mul_choose_sq_le {n r k t : ℕ} (hk : 0 < k)
    (hkt : k ≤ t) (htk : t ≤ 2 * k) :
    (((boundedFreimanDimSets n r t).ncard * t.choose k * t.choose k : ℕ) : ℝ) ≤
      (n : ℝ) ^ (r + 1) * ((2 * k : ℕ) : ℝ) ^ (10 * k) := by
  have ht : (t : ℝ) ≤ (2 * k : ℕ) := mod_cast htk
  have h₁ : (t : ℝ) ^ (4 * t) ≤ ((2 * k : ℕ) : ℝ) ^ (8 * k) :=
    (pow_le_pow_left₀ (by positivity) ht _).trans
      (pow_le_pow_right₀ (mod_cast by grind) (by grind))
  have h₂ : (t.choose k : ℝ) ≤ ((2 * k : ℕ) : ℝ) ^ k :=
    le_trans (mod_cast Nat.choose_le_pow t k) (pow_le_pow_left₀ (by positivity) ht k)
  rw [Nat.cast_mul, Nat.cast_mul, (by grind : 10 * k = 8 * k + k + k), pow_add _ (8 * k + k),
    pow_add _ (8 * k), ← mul_assoc, ← mul_assoc]
  gcongr
  exact (card_boundedFreimanDimSets n r (by grind : 0 < t)).trans
    (mul_le_mul_of_nonneg_left h₁ (by positivity))

/-- If `m < k * (k + 1) / 2`, then the number of sets `A + B` with `A, B ⊆ [n]`,
`|A| = |B| = k` and `|A + B| ≤ m` is at most `n ^ (2 * m / k + 1) * k ^ (24 * k)`. -/
lemma pairSumsetsFamily_ncard_le (n k m : ℕ) (hm : m < k * (k + 1) / 2) :
    ((pairSumsetsFamily n k m).ncard : ℝ) ≤
        (n : ℝ) ^ (2 * (m : ℝ) / (k : ℝ) + 1) * (k : ℝ) ^ (24 * k) := by
  by_cases h : n < k ∨ m < k
  · rw [pairSumsetsFamily_eq_empty h, Set.ncard_empty, Nat.cast_zero]
    positivity
  have hk : 2 ≤ k := by
    rcases k with _ | _ | k <;> grind
  refine (Nat.cast_le.2 (pairSumsetsFamily_ncard_le_sum (by grind) hm)).trans ?_
  rw [Nat.cast_sum]
  refine (sum_le_sum fun t ht ↦ ncard_boundedFreimanDimSets_mul_choose_sq_le (by grind)
    (mem_Icc.1 ht).1 (mem_Icc.1 ht).2).trans ?_
  rw [sum_const, nsmul_eq_mul, mul_left_comm]
  exact mul_le_mul (pow_two_mul_div_add_one_le_rpow k m (by grind))
    (medium_counting_factor_bound hk) (by positivity) (by positivity)

private lemma ncard_smallSumsetFreimanDimSets_mul_choose_sq_le {n k m t : ℕ} {c : ℝ}
    (hc : c ≤ 1 / (2 : ℝ) ^ (8 : ℕ)) (hk : smallSumsetClassCountThreshold ≤ k)
    (hm : (m : ℝ) ≤ (k : ℝ) ^ (1 + c)) (hkm : k ≤ m) (hkt : k ≤ t) (htk : t ≤ 2 * k) :
    (((smallSumsetFreimanDimSets n (2 * m / k) (3 * (m * m / k)) t).ncard * t.choose k *
      t.choose k : ℕ) : ℝ) ≤
      (n : ℝ) ^ (2 * m / k + 1) * ((6 * Real.exp 1 * (m : ℝ)) / (k : ℝ)) ^ (6 * k) *
        Real.exp (((2 * k : ℕ) : ℝ) ^ ((31 : ℝ) / 32)) := by
  have hk' := two_pow_200_le_smallSumsetClassCountThreshold.trans hk
  have hcount := smallSumsetFreimanDimSets_ncard_le n (2 * m / k)
    (3 * (m * m / k)) t (hk.trans hkt) (three_mul_sq_div_le_rpow hc hk' hm hkt)
  have hexp : Real.exp ((t : ℝ) ^ ((31 : ℝ) / 32)) ≤
      Real.exp (((2 * k : ℕ) : ℝ) ^ ((31 : ℝ) / 32)) :=
    Real.exp_le_exp.2 (Real.rpow_le_rpow (by positivity) (mod_cast htk) (by norm_num))
  rw [Nat.cast_mul, Nat.cast_mul, mul_assoc]
  refine (mul_le_mul_of_nonneg_right hcount (by positivity)).trans ?_
  refine le_trans (le_of_eq ?_) (mul_le_mul (mul_le_mul_of_nonneg_left
    (pow_mul_choose_sq_le (by grind) hkm hkt htk)
    (by positivity)) hexp (by positivity) (by positivity))
  ring

/-- If `m < k * (k + 1) / 2`, `k` is large and `m ≤ k ^ (1 + c)` with `c ≤ 2⁻⁸`, then the number
of sets `A + B` with `A, B ⊆ [n]`, `|A| = |B| = k` and `|A + B| ≤ m` is at most
`n ^ (2 * m / k + 1) * (6 * e * m / k) ^ (6 * k) * exp (k ^ (1 - 2 * c))`. -/
lemma pairSumsetsFamily_ncard_le_of_small_sumset (n k m : ℕ) (c : ℝ)
    (hm : m < k * (k + 1) / 2)
    (hc_le : c ≤ 1 / (2 : ℝ) ^ (8 : ℕ))
    (hk_threshold : smallSumsetClassCountThreshold ≤ k)
    (hm_small : (m : ℝ) ≤ (k : ℝ) ^ (1 + c)) :
    ((pairSumsetsFamily n k m).ncard : ℝ) ≤
      (n : ℝ) ^ (2 * (m : ℝ) / (k : ℝ) + 1) *
        ((6 * Real.exp 1 * (m : ℝ)) / (k : ℝ)) ^ (6 * k) *
          Real.exp ((k : ℝ) ^ (1 - 2 * c)) := by
  by_cases h : n < k ∨ m < k
  · rw [pairSumsetsFamily_eq_empty h, Set.ncard_empty, Nat.cast_zero]
    positivity
  have hk := two_pow_200_le_smallSumsetClassCountThreshold.trans hk_threshold
  refine (Nat.cast_le.2 (pairSumsetsFamily_ncard_le_sum_smallSumset (by grind) hm)).trans ?_
  rw [Nat.cast_sum]
  refine (sum_le_sum fun t ht ↦ ncard_smallSumsetFreimanDimSets_mul_choose_sq_le hc_le
    hk_threshold hm_small (by grind) (mem_Icc.1 ht).1 (mem_Icc.1 ht).2).trans ?_
  rw [sum_const, nsmul_eq_mul, mul_left_comm]
  exact mul_le_mul (mul_le_mul_of_nonneg_right (pow_two_mul_div_add_one_le_rpow k m (by grind))
    (by positivity)) (card_Icc_mul_exp_le hc_le hk) (by positivity) (by positivity)

end

end DenseSetsWithoutLargeSumsets
