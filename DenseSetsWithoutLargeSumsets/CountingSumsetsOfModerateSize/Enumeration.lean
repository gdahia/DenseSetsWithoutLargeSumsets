/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.MainTheorem
import DenseSetsWithoutLargeSumsets.SimpleBoundForVeryLargeSumsets
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.SmallSumsetIsomorphismClasses
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
Bounds for counting sumsets of moderate size.
-/

namespace DenseSetsWithoutLargeSumsets

open scoped Pointwise

noncomputable section

/-- Sumsets `Y ⊆ [2n]` represented as `A + B` by two `k`-sets in `[n]` with `#Y ≤ m`. -/
def pairSumsetsFamily (n k m : ℕ) : Set (Finset ℕ) :=
  {Y : Finset ℕ |
    Y ⊆ interval (2 * n) ∧
      ∃ A B : Finset ℕ,
        A ⊆ interval n ∧ B ⊆ interval n ∧
          A.card = k ∧ B.card = k ∧ A + B = Y ∧ Y.card ≤ m}

/-- The fixed auxiliary exponent used in the moderate-sumset range. -/
def moderateSumsetAuxExponent : ℝ :=
  1 / (2 : ℝ) ^ (8 : ℕ)

private lemma sum_Icc_sub_eq_choose (k : ℕ) :
    (Finset.Icc 1 (k - 1)).sum (fun t => k - t) = Nat.choose k 2 := by
  classical
  by_cases hk0 : k = 0
  · simp [hk0]
  rw [← Finset.Ico_add_one_right_eq_Icc 1 (k - 1)]
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)]
  apply ((by
    simpa using
      (Finset.sum_Ico_reflect (fun s => s) 1 (m := k) (n := k) (by omega)) :
        (Finset.Ico 1 k).sum (fun t => k - t) =
          (Finset.Ico 1 k).sum (fun s => s))).trans
  · convert Nat.sum_Icc_choose (k - 1) 1 using 1
    · rw [← Finset.Ico_add_one_right_eq_Icc,
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)]
      apply Finset.sum_congr rfl
      intro m hm
      simp [Nat.choose_one_right]
    · rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)]

private lemma freiman_union_dim_lt_k {A B : Finset ℕ} {k m : ℕ}
    (hk : 0 < k) (hAcard : A.card = k) (hBcard : B.card = k)
    (hABm : (A + B).card ≤ m) (hm : m < k * (k + 1) / 2) :
    freimanDim (A ∪ B) < k := by
  classical
  by_contra hnot
  have hkr : k ≤ freimanDim (A ∪ B) := Nat.le_of_not_gt hnot
  have hrpos : 1 ≤ freimanDim (A ∪ B) := le_trans (Nat.succ_le_of_lt hk) hkr
  have hAne : A.Nonempty := Finset.card_pos.mp (by simpa [hAcard] using hk)
  have hBne : B.Nonempty := Finset.card_pos.mp (by simpa [hBcard] using hk)
  have hsum_le :
      k + (Finset.Icc 1 (k - 1)).sum
          (fun t => min (freimanDim (A ∪ B) - 1) (k - t)) ≤ (A + B).card := by
    simpa [hAcard, hBcard] using
      card_add_sum_min_le_of_freimanDim_union (G := ℕ) (freimanDim (A ∪ B)) A B hrpos hAne hBne
        (by simp [hAcard, hBcard]) rfl
  have hsum_eq :
      (Finset.Icc 1 (k - 1)).sum
          (fun t => min (freimanDim (A ∪ B) - 1) (k - t)) =
        Nat.choose k 2 := by
    refine (Finset.sum_congr rfl ?_).trans (sum_Icc_sub_eq_choose k)
    intro t ht
    rw [Finset.mem_Icc] at ht
    rw [Nat.min_eq_right]
    omega
  apply (not_lt_of_ge ?_) hm
  refine le_trans ?_ hABm
  rw [hsum_eq] at hsum_le
  nth_rewrite 1 [← Nat.choose_one_right k] at hsum_le
  rw [← Nat.choose_succ_succ' k 1, Nat.choose_two_right, Nat.add_sub_cancel,
    Nat.mul_comm] at hsum_le
  exact hsum_le

private lemma freiman_union_dim_mul_le_two_card {A B : Finset ℕ} {k m : ℕ}
    (hk : 0 < k) (hAcard : A.card = k) (hBcard : B.card = k)
    (hABm : (A + B).card ≤ m) (hm : m < k * (k + 1) / 2) :
    freimanDim (A ∪ B) * k ≤ 2 * m := by
  classical
  generalize hrdef : freimanDim (A ∪ B) = r
  by_cases hr0 : r = 0
  · simp [hr0]
  have hrpos : 1 ≤ r := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hr0)
  have hrlt : r < k := by
    simpa [hrdef] using freiman_union_dim_lt_k hk hAcard hBcard hABm hm
  apply le_trans (b := 2 * (k + (r - 1) * k - Nat.choose (r + 1) 2))
  · exact_mod_cast
      (by
        rw [Nat.cast_mul, Nat.cast_sub, Nat.cast_add, Nat.cast_mul,
          Nat.cast_sub hrpos, Nat.cast_choose_two]
        · push_cast
          ring_nf
          nlinarith [(by exact_mod_cast (Nat.succ_le_iff.mpr hrlt) : (r : ℚ) + 1 ≤ k),
            (by exact_mod_cast hrpos : (1 : ℚ) ≤ r),
            (by exact_mod_cast hk : (0 : ℚ) < k)]
        · rw [Nat.choose_two_right]
          apply Nat.div_le_of_le_mul
          rw [Nat.add_sub_cancel]
          nlinarith [Nat.sub_add_cancel hrpos] :
        ((r * k : ℕ) : ℚ) ≤
          2 * ((k + (r - 1) * k - Nat.choose (r + 1) 2 : ℕ) : ℚ))
  · apply Nat.mul_le_mul_left
    apply le_trans (b := (A + B).card)
    · simpa [hAcard, hBcard] using
        card_add_lower_bound_of_freimanDim_union (G := ℕ) r A B hrpos
          (Finset.card_pos.mp (by simpa [hAcard] using hk))
          (Finset.card_pos.mp (by simpa [hBcard] using hk))
          (by simp [hAcard, hBcard]) hrdef
    · exact hABm

private lemma freiman_union_dim_le_two_mul_div {A B : Finset ℕ} {k m : ℕ}
    (hk : 0 < k) (hAcard : A.card = k) (hBcard : B.card = k)
    (hABm : (A + B).card ≤ m) (hm : m < k * (k + 1) / 2) :
    freimanDim (A ∪ B) ≤ 2 * m / k := by
  refine (Nat.le_div_iff_mul_le hk).2
    (freiman_union_dim_mul_le_two_card hk hAcard hBcard hABm hm)

private lemma card_add_self_le_mul_div {A B : Finset ℕ} {k m : ℕ}
    (hk : 0 < k) (_hAcard : A.card = k) (hBcard : B.card = k)
    (hABm : (A + B).card ≤ m) :
    (A + A).card ≤ m * m / k := by
  classical
  generalize hA'def : natCastImage A = A'
  generalize hB'def : natCastImage B = B'
  rw [Nat.le_div_iff_mul_le hk]
  apply le_trans (b := (A' + A').card * B'.card)
  · rw [← hA'def, ← hB'def, natCastImage_sum_card, natCastImage_card, hBcard]
  apply le_trans (b := (A' + B').card * (B' + A').card)
  · exact Finset.ruzsa_triangle_inequality_add_add_add A' B' A'
  rw [← hA'def, ← hB'def, natCastImage_sum_card A B, natCastImage_sum_card B A,
    add_comm B A]
  exact Nat.mul_le_mul hABm hABm

private lemma union_sum_card_le_three_mul_div {A B : Finset ℕ} {k m : ℕ}
    (hk : 0 < k) (hAcard : A.card = k) (hBcard : B.card = k)
    (hABm : (A + B).card ≤ m) :
    ((A ∪ B) + (A ∪ B)).card ≤ 3 * (m * m / k) := by
  classical
  generalize hqdef : m * m / k = q
  have hBne : B.Nonempty := Finset.card_pos.mp (by simpa [hBcard] using hk)
  have hkm : k ≤ m :=
    (le_of_eq hAcard.symm).trans ((Finset.card_le_card_add_right hBne).trans hABm)
  have hmq : m ≤ q := by
    rw [← hqdef]
    exact (Nat.le_div_iff_mul_le hk).2 (Nat.mul_le_mul_left m hkm)
  apply le_trans (b := ((A + A) ∪ (A + B) ∪ (B + B)).card)
  · apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_add] at hx
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    rw [Finset.mem_union] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · simp [Finset.add_mem_add ha hb]
    · simp [Finset.add_mem_add ha hb]
    · have hmid : a + b ∈ A + B := by
        simpa [add_comm] using (Finset.add_mem_add hb ha : b + a ∈ A + B)
      simp [hmid]
    · simp [Finset.add_mem_add ha hb]
  apply le_trans (b := (A + A).card + (A + B).card + (B + B).card)
  · exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  apply le_trans (b := q + m + q)
  · gcongr
    · rw [← hqdef]
      exact card_add_self_le_mul_div hk hAcard hBcard hABm
    · rw [← hqdef]
      exact card_add_self_le_mul_div hk hBcard hAcard (by simpa [add_comm] using hABm)
  omega

private def boundedFreimanDimSetsFinset (n r t : ℕ) : Finset (Finset ℕ) :=
  ((interval n).powersetCard t).filter fun X => freimanDim X ≤ r

private lemma mem_boundedFreimanDimSetsFinset {n r t : ℕ} {X : Finset ℕ} :
    X ∈ boundedFreimanDimSetsFinset n r t ↔
      X ⊆ interval n ∧ X.card = t ∧ freimanDim X ≤ r := by
  rw [boundedFreimanDimSetsFinset, Finset.mem_filter, Finset.mem_powersetCard]
  tauto

private lemma boundedFreimanDimSetsFinset_card (n r t : ℕ) :
    (boundedFreimanDimSetsFinset n r t).card = (boundedFreimanDimSets n r t).ncard := by
  rw [← Set.ncard_coe_finset]
  congr
  ext X
  simp [mem_boundedFreimanDimSetsFinset, boundedFreimanDimSets]

private def smallSumsetFreimanDimSetsFinset (n r s t : ℕ) : Finset (Finset ℕ) :=
  (boundedFreimanDimSetsFinset n r t).filter fun X => (X + X).card ≤ s

private lemma mem_smallSumsetFreimanDimSetsFinset {n r s t : ℕ} {X : Finset ℕ} :
    X ∈ smallSumsetFreimanDimSetsFinset n r s t ↔
      X ⊆ interval n ∧ X.card = t ∧ freimanDim X ≤ r ∧ (X + X).card ≤ s := by
  rw [smallSumsetFreimanDimSetsFinset, Finset.mem_filter]
  simp [mem_boundedFreimanDimSetsFinset, and_assoc]

private lemma smallSumsetFreimanDimSetsFinset_card (n r s t : ℕ) :
    (smallSumsetFreimanDimSetsFinset n r s t).card =
      (smallSumsetFreimanDimSets n r s t).ncard := by
  rw [← Set.ncard_coe_finset]
  congr
  ext X
  simp [mem_smallSumsetFreimanDimSetsFinset, smallSumsetFreimanDimSets]

private def unionWitnesses (n k r t : ℕ) : Finset (Finset ℕ × Finset ℕ × Finset ℕ) :=
  (boundedFreimanDimSetsFinset n r t).biUnion fun X =>
    (X.powersetCard k ×ˢ X.powersetCard k).image fun p => (X, p.1, p.2)

private lemma mem_unionWitnesses {n k r t : ℕ} {w : Finset ℕ × Finset ℕ × Finset ℕ} :
    w ∈ unionWitnesses n k r t ↔
      w.1 ⊆ interval n ∧ w.1.card = t ∧ freimanDim w.1 ≤ r ∧
        w.2.1 ⊆ w.1 ∧ w.2.2 ⊆ w.1 ∧ w.2.1.card = k ∧ w.2.2.card = k := by
  classical
  constructor
  · intro hw
    rw [unionWitnesses, Finset.mem_biUnion] at hw
    rcases hw with ⟨X, hX, hwX⟩
    rw [Finset.mem_image] at hwX
    rcases hwX with ⟨p, hp, rfl⟩
    rw [Finset.mem_product] at hp
    rcases mem_boundedFreimanDimSetsFinset.mp hX with ⟨hXsub, hXcard, hXdim⟩
    rcases Finset.mem_powersetCard.mp hp.1 with ⟨hAsub, hAcard⟩
    rcases Finset.mem_powersetCard.mp hp.2 with ⟨hBsub, hBcard⟩
    exact ⟨hXsub, hXcard, hXdim, hAsub, hBsub, hAcard, hBcard⟩
  · intro hw
    rw [unionWitnesses, Finset.mem_biUnion]
    refine ⟨w.1, mem_boundedFreimanDimSetsFinset.mpr ⟨hw.1, hw.2.1, hw.2.2.1⟩, ?_⟩
    rw [Finset.mem_image]
    refine ⟨(w.2.1, w.2.2), ?_, rfl⟩
    rw [Finset.mem_product]
    refine ⟨Finset.mem_powersetCard.mpr ⟨hw.2.2.2.1, hw.2.2.2.2.2.1⟩,
      Finset.mem_powersetCard.mpr ⟨hw.2.2.2.2.1, hw.2.2.2.2.2.2⟩⟩

private lemma unionWitnesses_card_le (n k r t : ℕ) :
    (unionWitnesses n k r t).card ≤
      (boundedFreimanDimSets n r t).ncard * Nat.choose t k * Nat.choose t k := by
  classical
  apply Finset.card_biUnion_le.trans
  apply (Finset.sum_le_sum fun X hX => Finset.card_image_le).trans
  apply le_trans (b := ∑ X ∈ boundedFreimanDimSetsFinset n r t,
    Nat.choose t k * Nat.choose t k)
  · apply le_of_eq
    apply Finset.sum_congr rfl
    intro X hX
    rcases mem_boundedFreimanDimSetsFinset.mp hX with ⟨_, hXcard, _⟩
    simp [Finset.card_product, Finset.card_powersetCard, hXcard]
  · refine le_trans (b := (boundedFreimanDimSetsFinset n r t).card *
      (Nat.choose t k * Nat.choose t k)) ?_ ?_
    · simp [mul_comm, mul_assoc]
    · rw [boundedFreimanDimSetsFinset_card]
      ring_nf
      exact le_rfl

private def smallUnionWitnesses (n k r s t : ℕ) :
    Finset (Finset ℕ × Finset ℕ × Finset ℕ) :=
  (smallSumsetFreimanDimSetsFinset n r s t).biUnion fun X =>
    (X.powersetCard k ×ˢ X.powersetCard k).image fun p => (X, p.1, p.2)

private lemma mem_smallUnionWitnesses {n k r s t : ℕ}
    {w : Finset ℕ × Finset ℕ × Finset ℕ} :
    w ∈ smallUnionWitnesses n k r s t ↔
      w.1 ⊆ interval n ∧ w.1.card = t ∧ freimanDim w.1 ≤ r ∧
        (w.1 + w.1).card ≤ s ∧
          w.2.1 ⊆ w.1 ∧ w.2.2 ⊆ w.1 ∧ w.2.1.card = k ∧ w.2.2.card = k := by
  classical
  constructor
  · intro hw
    rw [smallUnionWitnesses, Finset.mem_biUnion] at hw
    rcases hw with ⟨X, hX, hwX⟩
    rw [Finset.mem_image] at hwX
    rcases hwX with ⟨p, hp, rfl⟩
    rw [Finset.mem_product] at hp
    rcases mem_smallSumsetFreimanDimSetsFinset.mp hX with ⟨hXsub, hXcard, hXdim, hXsum⟩
    rcases Finset.mem_powersetCard.mp hp.1 with ⟨hAsub, hAcard⟩
    rcases Finset.mem_powersetCard.mp hp.2 with ⟨hBsub, hBcard⟩
    exact ⟨hXsub, hXcard, hXdim, hXsum, hAsub, hBsub, hAcard, hBcard⟩
  · intro hw
    rw [smallUnionWitnesses, Finset.mem_biUnion]
    refine ⟨w.1, mem_smallSumsetFreimanDimSetsFinset.mpr
      ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1⟩, ?_⟩
    rw [Finset.mem_image]
    refine ⟨(w.2.1, w.2.2), ?_, rfl⟩
    rw [Finset.mem_product]
    refine ⟨Finset.mem_powersetCard.mpr ⟨hw.2.2.2.2.1, hw.2.2.2.2.2.2.1⟩,
      Finset.mem_powersetCard.mpr ⟨hw.2.2.2.2.2.1, hw.2.2.2.2.2.2.2⟩⟩

private lemma smallUnionWitnesses_card_le (n k r s t : ℕ) :
    (smallUnionWitnesses n k r s t).card ≤
      (smallSumsetFreimanDimSets n r s t).ncard * Nat.choose t k * Nat.choose t k := by
  classical
  apply Finset.card_biUnion_le.trans
  apply (Finset.sum_le_sum fun X hX => Finset.card_image_le).trans
  apply le_trans (b := ∑ X ∈ smallSumsetFreimanDimSetsFinset n r s t,
    Nat.choose t k * Nat.choose t k)
  · apply le_of_eq
    apply Finset.sum_congr rfl
    intro X hX
    rcases mem_smallSumsetFreimanDimSetsFinset.mp hX with ⟨_, hXcard, _, _⟩
    simp [Finset.card_product, Finset.card_powersetCard, hXcard]
  · refine le_trans (b := (smallSumsetFreimanDimSetsFinset n r s t).card *
      (Nat.choose t k * Nat.choose t k)) ?_ ?_
    · simp [mul_comm, mul_assoc]
    · rw [smallSumsetFreimanDimSetsFinset_card]
      ring_nf
      exact le_rfl

private def allUnionWitnesses (n k m : ℕ) : Finset (Finset ℕ × Finset ℕ × Finset ℕ) :=
  (Finset.Icc k (2 * k)).biUnion fun t => unionWitnesses n k (2 * m / k) t

private lemma pairSumsetsFamily_subset_witnessSums {n k m : ℕ}
    (hk : 0 < k) (hm : m < k * (k + 1) / 2) :
    pairSumsetsFamily n k m ⊆
      ((allUnionWitnesses n k m).image fun w : Finset ℕ × Finset ℕ × Finset ℕ =>
        w.2.1 + w.2.2 : Finset (Finset ℕ)) := by
  classical
  intro Y hY
  rcases hY with ⟨_hYint, A, B, hAint, hBint, hAcard, hBcard, hYeq, hYcard⟩
  generalize hXdef : A ∪ B = X
  have hA_X : A ⊆ X := by rw [← hXdef]; simp
  have hB_X : B ⊆ X := by rw [← hXdef]; simp
  rw [Finset.mem_coe, Finset.mem_image]
  refine ⟨(X, A, B), ?_, by simp [hYeq]⟩
  rw [allUnionWitnesses, Finset.mem_biUnion]
  refine ⟨X.card, Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
  · rw [← hAcard]
    exact Finset.card_le_card hA_X
  · rw [← hXdef]
    apply (Finset.card_union_le A B).trans
    rw [hAcard, hBcard]
    ring_nf
    omega
  rw [mem_unionWitnesses]
  refine ⟨?_, rfl, ?_, hA_X, hB_X, hAcard, hBcard⟩
  · intro x hx
    rw [← hXdef] at hx
    simp at hx
    exact hx.elim (fun hxA => hAint hxA) (fun hxB => hBint hxB)
  · rw [← hXdef]
    exact freiman_union_dim_le_two_mul_div hk hAcard hBcard
      (by simpa [hYeq] using hYcard) hm

private lemma pairSumsetsFamily_ncard_le_sum (n k m : ℕ)
    (hk : 0 < k) (hm : m < k * (k + 1) / 2) :
    (pairSumsetsFamily n k m).ncard ≤
      ∑ t ∈ Finset.Icc k (2 * k),
        (boundedFreimanDimSets n (2 * m / k) t).ncard * Nat.choose t k * Nat.choose t k := by
  classical
  generalize himage_def :
    ((allUnionWitnesses n k m).image fun w : Finset ℕ × Finset ℕ × Finset ℕ =>
      w.2.1 + w.2.2) = imageW
  apply le_trans (b := ((imageW : Finset (Finset ℕ)) : Set (Finset ℕ)).ncard)
  · refine Set.ncard_le_ncard ?_ imageW.finite_toSet
    rw [← himage_def]
    simpa using pairSumsetsFamily_subset_witnessSums (n := n) (k := k) (m := m) hk hm
  apply le_trans (b := imageW.card)
  · simp
  apply le_trans (b := (allUnionWitnesses n k m).card)
  · rw [← himage_def]
    exact Finset.card_image_le
  apply le_trans (b :=
    ∑ t ∈ Finset.Icc k (2 * k), (unionWitnesses n k (2 * m / k) t).card)
  · exact Finset.card_biUnion_le
  exact Finset.sum_le_sum fun t ht => unionWitnesses_card_le n k (2 * m / k) t

private def allSmallUnionWitnesses (n k m : ℕ) :
    Finset (Finset ℕ × Finset ℕ × Finset ℕ) :=
  (Finset.Icc k (2 * k)).biUnion fun t =>
    smallUnionWitnesses n k (2 * m / k) (3 * (m * m / k)) t

private lemma pairSumsetsFamily_subset_smallWitnessSums {n k m : ℕ}
    (hk : 0 < k) (hm : m < k * (k + 1) / 2) :
    pairSumsetsFamily n k m ⊆
      ((allSmallUnionWitnesses n k m).image fun w : Finset ℕ × Finset ℕ × Finset ℕ =>
        w.2.1 + w.2.2 : Finset (Finset ℕ)) := by
  classical
  intro Y hY
  rcases hY with ⟨_hYint, A, B, hAint, hBint, hAcard, hBcard, hYeq, hYcard⟩
  generalize hXdef : A ∪ B = X
  have hA_X : A ⊆ X := by rw [← hXdef]; simp
  have hB_X : B ⊆ X := by rw [← hXdef]; simp
  have hABm : (A + B).card ≤ m := by simpa [hYeq] using hYcard
  rw [Finset.mem_coe, Finset.mem_image]
  refine ⟨(X, A, B), ?_, by simp [hYeq]⟩
  rw [allSmallUnionWitnesses, Finset.mem_biUnion]
  refine ⟨X.card, Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
  · rw [← hAcard]
    exact Finset.card_le_card hA_X
  · rw [← hXdef]
    apply (Finset.card_union_le A B).trans
    rw [hAcard, hBcard]
    ring_nf
    omega
  rw [mem_smallUnionWitnesses]
  refine ⟨?_, rfl, ?_, ?_, hA_X, hB_X, hAcard, hBcard⟩
  · intro x hx
    rw [← hXdef] at hx
    simp at hx
    exact hx.elim (fun hxA => hAint hxA) (fun hxB => hBint hxB)
  · rw [← hXdef]
    exact freiman_union_dim_le_two_mul_div hk hAcard hBcard hABm hm
  · rw [← hXdef]
    exact union_sum_card_le_three_mul_div hk hAcard hBcard hABm

private lemma pairSumsetsFamily_ncard_le_small_sum (n k m : ℕ)
    (hk : 0 < k) (hm : m < k * (k + 1) / 2) :
    (pairSumsetsFamily n k m).ncard ≤
      ∑ t ∈ Finset.Icc k (2 * k),
        (smallSumsetFreimanDimSets n (2 * m / k) (3 * (m * m / k)) t).ncard *
          Nat.choose t k * Nat.choose t k := by
  classical
  generalize himage_def :
    ((allSmallUnionWitnesses n k m).image fun w : Finset ℕ × Finset ℕ × Finset ℕ =>
      w.2.1 + w.2.2) = imageW
  apply le_trans (b := ((imageW : Finset (Finset ℕ)) : Set (Finset ℕ)).ncard)
  · refine Set.ncard_le_ncard ?_ imageW.finite_toSet
    rw [← himage_def]
    simpa using
      pairSumsetsFamily_subset_smallWitnessSums (n := n) (k := k) (m := m) hk hm
  apply le_trans (b := imageW.card)
  · simp
  apply le_trans (b := (allSmallUnionWitnesses n k m).card)
  · rw [← himage_def]
    exact Finset.card_image_le
  apply le_trans (b :=
    ∑ t ∈ Finset.Icc k (2 * k),
      (smallUnionWitnesses n k (2 * m / k) (3 * (m * m / k)) t).card)
  · exact Finset.card_biUnion_le
  exact Finset.sum_le_sum fun t ht =>
    smallUnionWitnesses_card_le n k (2 * m / k) (3 * (m * m / k)) t

lemma medium_counting_factor_bound {k : ℕ} (hk : 2 ≤ k) :
    ((Finset.Icc k (2 * k)).card : ℝ) * ((2 * k : ℕ) : ℝ) ^ (10 * k) ≤
      (k : ℝ) ^ (24 * k) := by
  norm_cast
  apply le_trans (b := (2 * k) * (2 * k) ^ (10 * k))
  · apply Nat.mul_le_mul_right
    apply le_trans (b := (Finset.Icc 1 (2 * k)).card)
    · apply Finset.card_le_card
      intro t ht
      rw [Finset.mem_Icc] at ht ⊢
      omega
    · simp [Nat.card_Icc]
  rw [mul_comm, ← pow_succ]
  apply le_trans (b := (k ^ 2) ^ (10 * k + 1))
  · exact Nat.pow_le_pow_left (by nlinarith) _
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by omega : 0 < k) (by omega)

private lemma pairSumsetsFamily_empty_of_one_zero (n : ℕ) :
    pairSumsetsFamily n 1 0 = ∅ := by
  classical
  ext Y
  constructor
  · intro hY
    rcases hY with ⟨_hYint, A, B, _hAint, _hBint, hAcard, hBcard, hYeq, hYcard⟩
    rcases Finset.card_pos.mp (by rw [hAcard]; norm_num) with ⟨a, ha⟩
    rcases Finset.card_pos.mp (by rw [hBcard]; norm_num) with ⟨b, hb⟩
    have hpos : 0 < (A + B).card := Finset.card_pos.mpr ⟨a + b, Finset.add_mem_add ha hb⟩
    have hzero : (A + B).card ≤ 0 := by simpa [← hYeq] using hYcard
    omega
  · simp

private lemma six_le_two_pow_200_rpow_three_div_128 :
    (6 : ℝ) ≤ ((2 : ℝ) ^ (200 : ℕ)) ^ ((3 : ℝ) / 128) := by
  rw [← Real.rpow_le_rpow_iff (by norm_num : (0 : ℝ) ≤ 6)
    (Real.rpow_nonneg (by positivity) _) (by norm_num : (0 : ℝ) < 128)]
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (200 : ℕ))]
  norm_num

private lemma six_le_k_rpow_three_div_128 {k : ℕ}
    (hk : (2 : ℕ) ^ (200 : ℕ) ≤ k) :
    (6 : ℝ) ≤ (k : ℝ) ^ ((3 : ℝ) / 128) := by
  refine six_le_two_pow_200_rpow_three_div_128.trans
    (Real.rpow_le_rpow (by positivity) ?_ (by norm_num))
  exact_mod_cast hk

private lemma six_le_k_rpow_of_gap {k : ℕ} {u : ℝ}
    (hk : (2 : ℕ) ^ (200 : ℕ) ≤ k) (hu : (3 : ℝ) / 128 ≤ u) :
    (6 : ℝ) ≤ (k : ℝ) ^ u := by
  refine (six_le_k_rpow_three_div_128 hk).trans
    (Real.rpow_le_rpow_of_exponent_le ?_ hu)
  exact_mod_cast (le_trans (by norm_num : (1 : ℕ) ≤ 2 ^ (200 : ℕ)) hk)

private lemma medium_small_admissible {k m t : ℕ} {c : ℝ}
    (hc_le : c ≤ 1 / (2 : ℝ) ^ (8 : ℕ))
    (hk_large : (2 : ℕ) ^ (200 : ℕ) ≤ k)
    (hm_small : (m : ℝ) ≤ (k : ℝ) ^ (1 + c))
    (ht : t ∈ Finset.Icc k (2 * k)) :
    ((3 * (m * m / k) : ℕ) : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30) / 2 := by
  have hkpos : 0 < k :=
    lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ) ^ (200 : ℕ)) hk_large
  have hkR_pos : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have htR_lower : (k : ℝ) ≤ t := by exact_mod_cast (Finset.mem_Icc.mp ht).1
  generalize hqdef : (k : ℝ) ^ (1 + 2 * c) = q
  have hmq : (m : ℝ) * m / k ≤ q := by
    apply (div_le_div_of_nonneg_right
      (mul_le_mul hm_small hm_small (by positivity) (by positivity)) hkR_pos.le).trans
    rw [← hqdef, ← Real.rpow_add hkR_pos]
    nth_rewrite 2 [← Real.rpow_one (x := (k : ℝ))]
    rw [← Real.rpow_sub hkR_pos]
    ring_nf
    exact le_rfl
  have hgap : (3 : ℝ) / 128 ≤ (31 : ℝ) / 30 - (1 + 2 * c) := by
    norm_num at hc_le ⊢
    nlinarith
  have hq_to_pow : 6 * q ≤ (k : ℝ) ^ ((31 : ℝ) / 30) := by
    apply (mul_le_mul_of_nonneg_right
      (six_le_k_rpow_of_gap
        (u := (31 : ℝ) / 30 - (1 + 2 * c)) hk_large hgap)
      (by rw [← hqdef]; positivity)).trans
    rw [← hqdef, ← Real.rpow_add hkR_pos]
    ring_nf
    exact le_rfl
  apply le_trans (b := 3 * q)
  · rw [Nat.cast_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    apply le_trans (b := (m : ℝ) * m / k)
    · rw [le_div_iff₀ hkR_pos]
      exact_mod_cast Nat.div_mul_le_self (m * m) k
    · exact hmq
  apply le_trans (b := (k : ℝ) ^ ((31 : ℝ) / 30) / 2)
  · linarith
  apply div_le_div_of_nonneg_right
  · exact Real.rpow_le_rpow (by positivity) htR_lower (by norm_num)
  · norm_num

private lemma medium_small_pack_bound {k m t : ℕ}
    (hk : 0 < k) (hkm : k ≤ m) (ht_lower : k ≤ t) (ht_upper : t ≤ 2 * k) :
    ((2 * Real.exp 1 * ((3 * (m * m / k) : ℕ) : ℝ)) / (t : ℝ)) ^ t *
        ((Nat.choose t k : ℝ) * (Nat.choose t k : ℝ)) ≤
      ((6 * Real.exp 1 * (m : ℝ)) / (k : ℝ)) ^ (6 * k) := by
  generalize hEdef : 6 * Real.exp 1 = E
  generalize hqdef : (m : ℝ) / (k : ℝ) = q
  have hkR_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have htR_pos : 0 < (t : ℝ) := by exact_mod_cast lt_of_lt_of_le hk ht_lower
  have htR_lower : (k : ℝ) ≤ t := by exact_mod_cast ht_lower
  have hq_one : (1 : ℝ) ≤ q := by
    rw [← hqdef, one_le_div₀ hkR_pos]
    exact_mod_cast hkm
  have hE_two : (2 : ℝ) ≤ E := by
    rw [← hEdef]
    nlinarith [Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)]
  apply le_trans (b := (E * q ^ 2) ^ (2 * k) * (2 : ℝ) ^ (4 * k))
  · apply mul_le_mul
    · refine (pow_le_pow_left₀ (b := E * q ^ 2) (by positivity) ?_ t).trans ?_
      · apply le_trans (b :=
          (2 * Real.exp 1 * (3 * ((m : ℝ) * m / k))) / t)
        · gcongr
          rw [Nat.cast_mul]
          norm_num
          rw [le_div_iff₀ hkR_pos]
          exact_mod_cast Nat.div_mul_le_self (m * m) k
        · refine (div_le_div_of_nonneg_left (by positivity) hkR_pos htR_lower).trans_eq ?_
          rw [← hEdef, ← hqdef]
          field_simp [hkR_pos.ne']
          ring_nf
      · apply pow_le_pow_right₀
        · have hq2_one : (1 : ℝ) ≤ q ^ 2 := by
            simpa only [one_pow] using pow_le_pow_left₀ (by norm_num) hq_one 2
          nlinarith [mul_le_mul hE_two hq2_one (by norm_num : (0 : ℝ) ≤ 1)
            (le_trans (by norm_num) hE_two)]
        · exact ht_upper
    · norm_num only [← Nat.cast_mul, ← Nat.cast_pow]
      exact_mod_cast (Nat.mul_le_mul (Nat.choose_le_two_pow t k)
        (Nat.choose_le_two_pow t k)).trans
          (by
            rw [← pow_add]
            exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega))
    · positivity
    · positivity
  apply le_trans (b := (E * q ^ 2) ^ (2 * k) * E ^ (4 * k))
  · exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hE_two (4 * k)) (by positivity)
  apply le_trans (b := E ^ (6 * k) * q ^ (4 * k))
  · ring_nf
    exact le_rfl
  apply le_trans (b := E ^ (6 * k) * q ^ (6 * k))
  · exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hq_one (by omega : 4 * k ≤ 6 * k)) (by positivity)
  rw [← mul_pow]
  rw [← hEdef, ← hqdef]
  field_simp [hkR_pos.ne']
  exact le_rfl

private lemma medium_small_exp_card_bound {k : ℕ} {c : ℝ}
    (hc_le : c ≤ 1 / (2 : ℝ) ^ (8 : ℕ))
    (hk_large : (2 : ℕ) ^ (200 : ℕ) ≤ k) :
    ((Finset.Icc k (2 * k)).card : ℝ) *
        Real.exp ((((2 * k : ℕ) : ℝ) ^ ((31 : ℝ) / 32))) ≤
      Real.exp ((k : ℝ) ^ (1 - 2 * c)) := by
  have hkpos : 0 < k :=
    lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ) ^ (200 : ℕ)) hk_large
  have hkR_pos : 0 < (k : ℝ) := by exact_mod_cast hkpos
  generalize hpdef : (((2 * k : ℕ) : ℝ) ^ ((31 : ℝ) / 32)) = p
  generalize hqdef : (k : ℝ) ^ (1 - 2 * c) = q
  have hp_nonneg : 0 ≤ p := by rw [← hpdef]; positivity
  have hlog_le : Real.log (((2 * k : ℕ) : ℝ)) ≤ 2 * p := by
    apply (Real.log_le_rpow_div (by positivity)
      (by norm_num : (0 : ℝ) < (31 : ℝ) / 32)).trans
    rw [← hpdef]
    nlinarith
  have hgap : (3 : ℝ) / 128 ≤ (1 - 2 * c) - ((31 : ℝ) / 32) := by
    norm_num at hc_le ⊢
    nlinarith
  have hp_to_q : 3 * p ≤ q := by
    have htwo_pow : (2 : ℝ) ^ ((31 : ℝ) / 32) ≤ 2 := by
      simpa [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : ((31 : ℝ) / 32) ≤ 1)
    rw [← hpdef]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hkR_pos.le]
    apply le_trans (b := 6 * (k : ℝ) ^ ((31 : ℝ) / 32))
    · nlinarith [mul_le_mul_of_nonneg_right
        htwo_pow
        (Real.rpow_nonneg hkR_pos.le ((31 : ℝ) / 32))]
    apply (mul_le_mul_of_nonneg_right
      (six_le_k_rpow_of_gap
        (u := (1 - 2 * c) - (31 : ℝ) / 32) hk_large hgap)
      (Real.rpow_nonneg hkR_pos.le ((31 : ℝ) / 32))).trans
    rw [← hqdef, ← Real.rpow_add hkR_pos]
    ring_nf
    exact le_rfl
  apply le_trans (b := ((2 * k : ℕ) : ℝ) * Real.exp p)
  · apply mul_le_mul_of_nonneg_right
    · norm_cast
      apply le_trans (b := (Finset.Icc 1 (2 * k)).card)
      · apply Finset.card_le_card
        intro t ht
        rw [Finset.mem_Icc] at ht ⊢
        exact ⟨(Nat.succ_le_iff.mpr hkpos).trans ht.1, ht.2⟩
      · simp [Nat.card_Icc]
    · exact (Real.exp_pos p).le
  have htwoK_pos : 0 < (((2 * k : ℕ) : ℝ)) := by
    exact_mod_cast Nat.mul_pos (by norm_num : 0 < 2) hkpos
  rw [← Real.exp_log htwoK_pos, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Counting pair sumsets of moderate size, Theorem `stmt:countingPairsOfSets`. -/
theorem pairSumsetsFamily_ncard_le (n k m : ℕ)
    (hm : m < k * (k + 1) / 2) :
    ((pairSumsetsFamily n k m).ncard : ℝ) ≤
        (n : ℝ) ^ (2 * (m : ℝ) / (k : ℝ) + 1) * (k : ℝ) ^ (24 * k) := by
  classical
  by_cases hk_large : 2 ≤ k
  · by_cases hkn : k ≤ n
    · have hkpos : 0 < k := by omega
      generalize hrdef : 2 * m / k = r
      have hsum :
          ((pairSumsetsFamily n k m).ncard : ℝ) ≤
            ∑ t ∈ Finset.Icc k (2 * k),
              (((boundedFreimanDimSets n r t).ncard *
                  Nat.choose t k * Nat.choose t k : ℕ) : ℝ) := by
        rw [← hrdef]
        exact_mod_cast pairSumsetsFamily_ncard_le_sum n k m hkpos hm
      have hn_pow_le :
          (n : ℝ) ^ (r + 1) ≤ (n : ℝ) ^ (2 * (m : ℝ) / (k : ℝ) + 1) := by
        rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le
        · exact_mod_cast (le_trans (by omega : (1 : ℕ) ≤ 2) (le_trans hk_large hkn))
        · rw [← hrdef, Nat.cast_add, Nat.cast_one]
          have hkR_pos : (0 : ℝ) < k := by exact_mod_cast hkpos
          have hdiv : ((2 * m / k : ℕ) : ℝ) ≤ 2 * (m : ℝ) / k := by
            rw [le_div_iff₀ hkR_pos]
            exact_mod_cast Nat.div_mul_le_self (2 * m) k
          linarith
      have hterm :
          ∀ t ∈ Finset.Icc k (2 * k),
            (((boundedFreimanDimSets n r t).ncard * Nat.choose t k * Nat.choose t k : ℕ) : ℝ) ≤
              (n : ℝ) ^ (r + 1) * ((2 * k : ℕ) : ℝ) ^ (10 * k) := by
        intro t ht
        have ht_lower : k ≤ t := (Finset.mem_Icc.mp ht).1
        have ht_upper : t ≤ 2 * k := (Finset.mem_Icc.mp ht).2
        have hpack :
            (t : ℝ) ^ (4 * t) * (t : ℝ) ^ k * (t : ℝ) ^ k ≤
              ((2 * k : ℕ) : ℝ) ^ (10 * k) := by
          rw [← pow_add, ← pow_add]
          apply (pow_le_pow_left₀ (b := ((2 * k : ℕ) : ℝ))
            (by positivity) (by exact_mod_cast ht_upper) _).trans
          apply pow_le_pow_right₀
          · exact_mod_cast (by omega : 1 ≤ 2 * k)
          · omega
        norm_num only [Nat.cast_mul]
        apply le_trans (b := ((n : ℝ) ^ (r + 1) * (t : ℝ) ^ (4 * t)) *
          (t : ℝ) ^ k * (t : ℝ) ^ k)
        · gcongr
          · exact card_boundedFreimanDimSets n r t (by omega)
          · exact_mod_cast Nat.choose_le_pow t k
          · exact_mod_cast Nat.choose_le_pow t k
        · simpa only [mul_assoc, Nat.cast_mul, Nat.cast_ofNat] using
            mul_le_mul_of_nonneg_left hpack (pow_nonneg (Nat.cast_nonneg n) (r + 1))
      apply hsum.trans
      apply le_trans (b := ∑ t ∈ Finset.Icc k (2 * k),
        (n : ℝ) ^ (r + 1) * ((2 * k : ℕ) : ℝ) ^ (10 * k))
      · apply Finset.sum_le_sum
        intro t ht
        exact hterm t ht
      · simp only [Finset.sum_const, nsmul_eq_mul]
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul hn_pow_le (medium_counting_factor_bound hk_large)
            (by positivity) (by positivity)
    · have hempty : pairSumsetsFamily n k m = ∅ := by
        ext Y
        constructor
        · intro hY
          rcases hY with ⟨_hYint, A, _B, hAint, _hBint, hAcard, _hBcard, _hYeq, _hYcard⟩
          apply False.elim (hkn ?_)
          rw [← hAcard]
          simpa [interval, Nat.card_Icc] using Finset.card_le_card hAint
        · simp
      rw [hempty]
      simp only [Set.ncard_empty, CharP.cast_eq_zero]
      positivity
  · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · omega
    · obtain rfl : m = 0 := by omega
      rw [pairSumsetsFamily_empty_of_one_zero n]
      simp

/-- The small-sumset refinement of the moderate-sumset counting estimate. -/
theorem pairSumsetsFamily_ncard_le_of_small_sumset (n k m : ℕ) (c : ℝ)
    (hm : m < k * (k + 1) / 2)
    (hc_le : c ≤ 1 / (2 : ℝ) ^ (8 : ℕ))
    (hk_threshold : smallSumsetClassCountThreshold ≤ k)
    (hm_small : (m : ℝ) ≤ (k : ℝ) ^ (1 + c)) :
    ((pairSumsetsFamily n k m).ncard : ℝ) ≤
      (n : ℝ) ^ (2 * (m : ℝ) / (k : ℝ) + 1) *
        ((6 * Real.exp 1 * (m : ℝ)) / (k : ℝ)) ^ (6 * k) *
          Real.exp ((k : ℝ) ^ (1 - 2 * c)) := by
  classical
  have hk_large : (2 : ℕ) ^ (200 : ℕ) ≤ k :=
    two_pow_200_le_smallSumsetClassCountThreshold.trans hk_threshold
  have hkpos : 0 < k :=
    lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ) ^ (200 : ℕ)) hk_large
  by_cases hkn : k ≤ n
  · by_cases hkm : k ≤ m
    · generalize hrdef : 2 * m / k = r
      generalize hsdef : 3 * (m * m / k) = s
      generalize hpackdef : ((6 * Real.exp 1 * (m : ℝ)) / (k : ℝ)) ^ (6 * k) = pack
      generalize hpmaxdef : (((2 * k : ℕ) : ℝ) ^ ((31 : ℝ) / 32)) = pmax
      have hsum :
          ((pairSumsetsFamily n k m).ncard : ℝ) ≤
            ∑ t ∈ Finset.Icc k (2 * k),
              (((smallSumsetFreimanDimSets n r s t).ncard *
                    Nat.choose t k * Nat.choose t k : ℕ) : ℝ) := by
        rw [← hrdef, ← hsdef]
        exact_mod_cast pairSumsetsFamily_ncard_le_small_sum n k m hkpos hm
      have hn_pow_le :
          (n : ℝ) ^ (r + 1) ≤ (n : ℝ) ^ (2 * (m : ℝ) / (k : ℝ) + 1) := by
        rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le
        · exact_mod_cast (le_trans (Nat.succ_le_of_lt hkpos) hkn)
        · rw [← hrdef, Nat.cast_add, Nat.cast_one]
          have hkR_pos : (0 : ℝ) < k := by exact_mod_cast hkpos
          have hdiv : ((2 * m / k : ℕ) : ℝ) ≤ 2 * (m : ℝ) / k := by
            rw [le_div_iff₀ hkR_pos]
            exact_mod_cast Nat.div_mul_le_self (2 * m) k
          linarith
      have hterm :
          ∀ t ∈ Finset.Icc k (2 * k),
            (((smallSumsetFreimanDimSets n r s t).ncard *
                  Nat.choose t k * Nat.choose t k : ℕ) : ℝ) ≤
              (n : ℝ) ^ (r + 1) * pack * Real.exp pmax := by
        intro t ht
        have ht_lower : k ≤ t := (Finset.mem_Icc.mp ht).1
        have ht_upper : t ≤ 2 * k := (Finset.mem_Icc.mp ht).2
        have hcount := smallSumsetFreimanDimSets_ncard_le_of_class_cover n r s t
          (hk_threshold.trans ht_lower)
          (by
            rw [← hsdef]
            exact medium_small_admissible hc_le hk_large hm_small ht)
        have hpack :
            ((2 * Real.exp 1 * (s : ℝ)) / (t : ℝ)) ^ t *
                ((Nat.choose t k : ℝ) * (Nat.choose t k : ℝ)) ≤ pack := by
          rw [← hsdef, ← hpackdef]
          exact medium_small_pack_bound hkpos hkm ht_lower ht_upper
        have hexp : Real.exp ((t : ℝ) ^ ((31 : ℝ) / 32)) ≤ Real.exp pmax := by
          apply Real.exp_le_exp.mpr
          rw [← hpmaxdef]
          exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast ht_upper) (by norm_num)
        norm_num only [Nat.cast_mul]
        apply le_trans (b :=
          (n : ℝ) ^ (r + 1) *
            (((2 * Real.exp 1 * (s : ℝ)) / t) ^ t *
              ((Nat.choose t k : ℝ) * (Nat.choose t k : ℝ))) *
            Real.exp ((t : ℝ) ^ ((31 : ℝ) / 32)))
        · simpa only [mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_right hcount
              (by positivity : 0 ≤ (Nat.choose t k : ℝ) * Nat.choose t k)
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hpack (by positivity))
            hexp (by positivity) (by rw [← hpackdef]; positivity)
      apply hsum.trans
      apply le_trans (b := ∑ t ∈ Finset.Icc k (2 * k),
        (n : ℝ) ^ (r + 1) * pack * Real.exp pmax)
      · apply Finset.sum_le_sum
        intro t ht
        exact hterm t ht
      · simp only [Finset.sum_const, nsmul_eq_mul]
        have hcardexp : ((Finset.Icc k (2 * k)).card : ℝ) * Real.exp pmax ≤
            Real.exp ((k : ℝ) ^ (1 - 2 * c)) := by
          rw [← hpmaxdef]
          exact medium_small_exp_card_bound hc_le hk_large
        have hpack_nonneg : 0 ≤ pack := by rw [← hpackdef]; positivity
        have hright := mul_le_mul_of_nonneg_left hcardexp hpack_nonneg
        have hleft_nonneg :
            0 ≤ pack * (((Finset.Icc k (2 * k)).card : ℝ) * Real.exp pmax) :=
          mul_nonneg hpack_nonneg
            (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos pmax).le)
        apply le_trans (b :=
          (n : ℝ) ^ (2 * (m : ℝ) / k + 1) * pack *
            Real.exp ((k : ℝ) ^ (1 - 2 * c)))
        · simpa only [mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul hn_pow_le hright hleft_nonneg (by positivity)
        · rw [← hpackdef]
    · have hempty : pairSumsetsFamily n k m = ∅ := by
        ext Y
        constructor
        · intro hY
          rcases hY with ⟨_hYint, A, B, _hAint, _hBint, hAcard, hBcard, hYeq, hYcard⟩
          apply False.elim (hkm ?_)
          apply le_trans (b := (A + B).card)
          · rw [← hAcard]
            apply Finset.card_le_card_add_right
            exact Finset.card_pos.mp (by simpa [hBcard] using hkpos)
          · simpa [hYeq] using hYcard
        · simp
      rw [hempty]
      simp only [Set.ncard_empty, CharP.cast_eq_zero]
      positivity
  · have hempty : pairSumsetsFamily n k m = ∅ := by
      ext Y
      constructor
      · intro hY
        rcases hY with ⟨_hYint, A, _B, hAint, _hBint, hAcard, _hBcard, _hYeq, _hYcard⟩
        apply False.elim (hkn ?_)
        rw [← hAcard]
        simpa [interval, Nat.card_Icc] using Finset.card_le_card hAint
      · simp
    rw [hempty]
    simp only [Set.ncard_empty, CharP.cast_eq_zero]
    positivity

end

end DenseSetsWithoutLargeSumsets
