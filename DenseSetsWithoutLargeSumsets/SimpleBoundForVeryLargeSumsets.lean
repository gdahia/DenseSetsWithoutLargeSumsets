/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DenseSetsWithoutLargeSumsets.Probability
import Mathlib.Combinatorics.Additive.RuzsaCovering

/-!
# The union bound for sumsets of very large size

This file formalises Section 4 of *Dense sets without large sumsets* (Dahia, Marciano, Souza). Let
`k = ⌈(3 + γ) * log n / log (1 / δ)⌉` and let `S` be a random subset of `[n]` that contains each
element independently with probability `δ`. The probability that `S` contains a sumset `A + B`
with `A, B ⊆ [n]`, `|A| = |B| = k` and `|A + B| ≥ (k + 1) * k / 2` is at most
`k ^ 2 / n ^ (γ * k / 3)`.

The proof is a union bound over the pairs `(A, B)`, grouped by `m = |A + B|`. A fixed sumset of
size `m` is contained in `S` with probability at most `δ ^ m`. The pairs with `|A + B| ≤ m` are
counted with the Ruzsa covering lemma: there is `F ⊆ A` with `|F| ≤ m / k` and `A ⊆ F + B - B`, so
the pair is determined by `B`, by `F` and by a `k`-subset of `F + B - B`, a set of size at most
`k ^ 3`.

## Main definitions

* `veryLargeSumsetEvent n k S`: the set `S` contains a sumset `A + B` with `A, B ⊆ [n]`,
  `|A| = |B| = k` and `|A + B| ≥ (k + 1) * k / 2`.
* `veryLargeSumsetStrictThreshold γ c`: the probability bound holds for `n` larger than this.

## Main statements

* `pair_small_sumset_family_card_le`: there are at most `n ^ (k + m / k) * (k ^ 3).choose k`
  pairs `(A, B)` of `k`-subsets of `[n]` with `|A + B| ≤ m`.
* `very_large_sumset_probability_le`: the probability bound above, for `n ^ (-1 / 2) < δ ≤ 1 - c`.
-/

@[expose] public section

namespace DenseSetsWithoutLargeSumsets

open Finset MeasureTheory Real
open scoped Pointwise

noncomputable section

/-- The interval `[n]` as a set of integers. -/
def integerInterval (n : ℕ) : Finset ℤ :=
  natCastImage (interval n)

private lemma card_integerInterval (n : ℕ) : #(integerInterval n) = n := by
  simp [integerInterval, natCastImage_card, interval]

private lemma natCastImage_injective : Function.Injective natCastImage :=
  image_injective Int.ofNat_injective

/-- The image in `ℤ` of a pair of finite sets of natural numbers. -/
private def castPair : Finset ℕ × Finset ℕ → Finset ℤ × Finset ℤ :=
  Prod.map natCastImage natCastImage

private lemma castPair_injective : Function.Injective castPair :=
  natCastImage_injective.prodMap natCastImage_injective

/-- The Ruzsa covering lemma for sets of integers, with a bound in `ℕ`: if `|A + B| ≤ m`, then
there is `F ⊆ A` with `|F| ≤ m / |B|` and `A ⊆ F + (B - B)`. -/
lemma ruzsa_covering_int {A B : Finset ℤ} {m : ℕ} (hB : B.Nonempty) (hAB : #(A + B) ≤ m) :
    ∃ F ⊆ A, #F ≤ m / #B ∧ A ⊆ F + (B - B) := by
  have hB₀ : (0 : ℝ) < #B := mod_cast hB.card_pos
  obtain ⟨F, hFA, hF, hcover⟩ := ruzsa_covering_add (K := m / #B) hB
    ((Nat.cast_le.2 hAB).trans (div_mul_cancel₀ _ hB₀.ne').ge)
  refine ⟨F, hFA, (Nat.le_div_iff_mul_le hB.card_pos).2 ?_, hcover⟩
  exact_mod_cast (le_div_iff₀ hB₀).1 hF

/-- If `|F| ≤ k` and `|B| = k`, then `|F + B - B| ≤ k ^ 3`. -/
lemma ruzsa_container_card_le_cube {F B : Finset ℤ} {k : ℕ} (hF : #F ≤ k) (hB : #B = k) :
    #(F + B - B) ≤ k ^ 3 := by
  subst hB
  refine card_sub_le.trans ((Nat.mul_le_mul_right _ card_add_le).trans ?_)
  rw [pow_three']
  gcongr

/-- Every pair `(A, B)` of `k`-subsets of `[n]` with `|A + B| ≤ m` is given by a `k`-set `B`, a set
`F` with `|F| ≤ m / k` and a `k`-subset `A` of `F + B - B`. -/
lemma pair_small_sumset_family_subset_ruzsa_encoding (n k m : ℕ) :
    {p : Finset ℤ × Finset ℤ |
      p.1 ⊆ integerInterval n ∧ p.2 ⊆ integerInterval n ∧
        #p.1 = k ∧ #p.2 = k ∧ #(p.1 + p.2) ≤ m} ⊆
    {p : Finset ℤ × Finset ℤ |
      ∃ F : Finset ℤ,
        F ⊆ integerInterval n ∧ #F ≤ m / k ∧
          p.2 ∈ (integerInterval n).powersetCard k ∧
            p.1 ∈ (F + p.2 - p.2).powersetCard k} := by
  rintro ⟨A, B⟩ ⟨hA, hB, hAk, rfl, hAB⟩
  obtain hB₀ | hB₀ := B.eq_empty_or_nonempty
  · exact ⟨∅, by simp_all⟩
  · obtain ⟨F, hFA, hF, hcover⟩ := ruzsa_covering_int hB₀ hAB
    exact ⟨F, hFA.trans hA, hF, mem_powersetCard.2 ⟨hB, rfl⟩,
      mem_powersetCard.2 ⟨by rwa [add_sub_assoc], hAk⟩⟩

/-- The pairs `(A, B)` such that `B` is a `k`-subset of `[n]` and `A` is a `k`-subset of
`F + B - B` for some `r`-subset `F` of `[n]`. -/
private def coverFinset (n k r : ℕ) : Finset (Finset ℤ × Finset ℤ) :=
  ((integerInterval n).powersetCard k).biUnion fun B ↦
    ((integerInterval n).powersetCard r).biUnion fun F ↦
      ((F + B - B).powersetCard k).image fun A ↦ (A, B)

private lemma coverFinset_card_le (n k r : ℕ) (hrk : r ≤ k) :
    #(coverFinset n k r) ≤ n.choose k * n.choose r * (k ^ 3).choose k := by
  rw [coverFinset, mul_assoc]
  refine card_biUnion_le.trans ((sum_le_card_nsmul _ _ (n.choose r * (k ^ 3).choose k) ?_).trans_eq
    (by simp [card_integerInterval]))
  intro B hB
  refine card_biUnion_le.trans ((sum_le_card_nsmul _ _ ((k ^ 3).choose k) ?_).trans_eq
    (by simp [card_integerInterval]))
  intro F hF
  obtain ⟨-, hB⟩ := mem_powersetCard.1 hB
  obtain ⟨-, hF⟩ := mem_powersetCard.1 hF
  refine card_image_le.trans ((card_powersetCard _ _).trans_le (Nat.choose_le_choose k ?_))
  exact ruzsa_container_card_le_cube (hF.trans_le hrk) hB

/-- The pairs `(A, B)` of `k`-subsets of `[n]` with `|A + B| ≤ m`. -/
private abbrev smallSumsetPairs (n k m : ℕ) : Set (Finset ℕ × Finset ℕ) :=
  {p | p.1 ⊆ interval n ∧ p.2 ⊆ interval n ∧ #p.1 = k ∧ #p.2 = k ∧ #(p.1 + p.2) ≤ m}

private lemma castPair_mem_coverFinset {n k m : ℕ} (hrn : m / k ≤ n) {p : Finset ℕ × Finset ℕ}
    (hp : p ∈ smallSumsetPairs n k m) :
    castPair p ∈ coverFinset n k (m / k) := by
  obtain ⟨hA, hB, hAk, hBk, hAB⟩ := hp
  obtain ⟨F₀, hF₀I, hF₀, hBmem, hAmem⟩ :=
    @pair_small_sumset_family_subset_ruzsa_encoding n k m (castPair p)
      ⟨image_subset_image hA, image_subset_image hB, (natCastImage_card _).trans hAk,
        (natCastImage_card _).trans hBk, (natCastImage_sum_card _ _).trans_le hAB⟩
  obtain ⟨F, hF₀F, hFI, hF⟩ := exists_subsuperset_card_eq hF₀I hF₀ (by rwa [card_integerInterval])
  obtain ⟨hAsub, hAcard⟩ := mem_powersetCard.1 hAmem
  simp only [coverFinset, mem_biUnion, mem_image, mem_powersetCard]
  exact ⟨_, mem_powersetCard.1 hBmem, F, ⟨hFI, hF⟩, _, ⟨hAsub.trans (by gcongr), hAcard⟩, rfl⟩

private lemma smallSumsetPairs_subset (n k m : ℕ) :
    smallSumsetPairs n k m ⊆ ↑((interval n).powersetCard k ×ˢ (interval n).powersetCard k) := by
  rintro p ⟨hA, hB, hAk, hBk, -⟩
  simp [*]

private lemma ncard_smallSumsetPairs_le (n k m : ℕ) :
    (smallSumsetPairs n k m).ncard ≤ n.choose k * n.choose k := by
  refine (Set.ncard_le_ncard (smallSumsetPairs_subset n k m) (finite_toSet _)).trans_eq ?_
  simp [interval]

private lemma ncard_smallSumsetPairs_le_of_le_div {n k m : ℕ} (hkm : k ≤ m / k) :
    (smallSumsetPairs n k m).ncard ≤ n ^ (k + m / k) * (k ^ 3).choose k := by
  refine (ncard_smallSumsetPairs_le n k m).trans ?_
  refine le_mul_of_le_of_one_le ?_ (Nat.choose_pos (Nat.le_self_pow three_ne_zero k))
  obtain rfl | hn := n.eq_zero_or_pos
  · obtain rfl | hk := k.eq_zero_or_pos
    · simp
    · simp [Nat.choose_eq_zero_of_lt hk]
  · rw [pow_add]
    gcongr
    · exact Nat.choose_le_pow n k
    · exact (Nat.choose_le_pow n k).trans (Nat.pow_le_pow_right hn hkm)

/-- There are at most `n ^ (k + m / k) * (k ^ 3).choose k` pairs `(A, B)` of `k`-subsets of `[n]`
with `|A + B| ≤ m`. -/
lemma pair_small_sumset_family_card_le (n k m : ℕ) :
    {p : Finset ℕ × Finset ℕ |
      p.1 ⊆ interval n ∧ p.2 ⊆ interval n ∧
        #p.1 = k ∧ #p.2 = k ∧ #(p.1 + p.2) ≤ m}.ncard ≤
      n ^ (k + m / k) * (k ^ 3).choose k := by
  obtain hnk | hkn := lt_or_ge n k
  · exact (ncard_smallSumsetPairs_le n k m).trans (by simp [Nat.choose_eq_zero_of_lt hnk])
  obtain hkm | hmk := le_total k (m / k)
  · exact ncard_smallSumsetPairs_le_of_le_div hkm
  rw [← Set.ncard_image_of_injective _ castPair_injective, pow_add]
  refine (Set.ncard_le_ncard (t := ↑(coverFinset n k (m / k))) ?_ (finite_toSet _)).trans ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact castPair_mem_coverFinset (hmk.trans hkn) hp
  · rw [Set.ncard_coe_finset]
    refine (coverFinset_card_le n k (m / k) hmk).trans ?_
    gcongr <;> exact Nat.choose_le_pow _ _

/-- The inequality `∑ m, n ^ (k + m / k) * (k ^ 3).choose k * δ ^ m ≤ k ^ 2 / n ^ (γ * k / 3)` for
`k = pairCardThreshold (3 + γ) n δ`, where `m` ranges over `(k + 1) * k / 2 ≤ m ≤ k * k`. The left
side is the union bound for `veryLargeSumsetEvent n k`. -/
def veryLargeSumsetAnalyticBound (γ : ℝ) (n : ℕ) (δ : unitInterval) : Prop :=
  ∑ m ∈ Icc ((pairCardThreshold (3 + γ) n δ + 1) * pairCardThreshold (3 + γ) n δ / 2)
      (pairCardThreshold (3 + γ) n δ * pairCardThreshold (3 + γ) n δ),
      (n ^ (pairCardThreshold (3 + γ) n δ + m / pairCardThreshold (3 + γ) n δ) *
        (pairCardThreshold (3 + γ) n δ ^ 3).choose (pairCardThreshold (3 + γ) n δ) : ℝ) *
        (δ : ℝ) ^ m
    ≤ (pairCardThreshold (3 + γ) n δ : ℝ) ^ 2 /
      (n : ℝ) ^ (γ * (pairCardThreshold (3 + γ) n δ : ℝ) / 3)

/-- The number `⌈(18 * q / γ) ^ (36 / γ)⌉` with `q = densityCoefficient (3 + γ) c`. If `n` is at
least this number, then `18 * log (q * log n) ≤ γ * log n`. -/
def veryLargeSumsetThreshold (γ c : ℝ) : ℕ :=
  ⌈(18 * densityCoefficient (3 + γ) c / γ) ^ ((36 : ℝ) / γ)⌉₊

/-- One less than `veryLargeSumsetThreshold γ c`, so that `veryLargeSumsetStrictThreshold γ c < n`
implies `veryLargeSumsetThreshold γ c ≤ n`. -/
def veryLargeSumsetStrictThreshold (γ c : ℝ) : ℕ :=
  veryLargeSumsetThreshold γ c - 1

private lemma veryLargeSumsetThreshold_le {γ c : ℝ} {n : ℕ}
    (hn : veryLargeSumsetStrictThreshold γ c < n) : veryLargeSumsetThreshold γ c ≤ n := by
  grind [veryLargeSumsetStrictThreshold]

private lemma one_lt_mul_densityCoefficient_div {γ c : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1)
    (hc_pos : 0 < c) (hc_lt : c < 1) : 1 < 18 * densityCoefficient (3 + γ) c / γ := by
  rw [one_lt_div hγ_pos]
  linarith [densityCoefficient_gt_one (add_pos three_pos hγ_pos) hc_pos hc_lt]

private lemma two_le_of_veryLargeSumsetStrictThreshold_lt {γ c : ℝ} (hγ_pos : 0 < γ)
    (hγ_le : γ ≤ 1) (hc_pos : 0 < c) (hc_lt : c < 1) {n : ℕ}
    (hn : veryLargeSumsetStrictThreshold γ c < n) : 2 ≤ n := by
  refine le_trans (Nat.succ_le_of_lt (Nat.lt_ceil.2 ?_)) (veryLargeSumsetThreshold_le hn)
  rw [Nat.cast_one]
  exact one_lt_rpow (one_lt_mul_densityCoefficient_div hγ_pos hγ_le hc_pos hc_lt) (by positivity)

private lemma log_densityCoefficient_mul_log_le {γ c : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1)
    (hc_pos : 0 < c) (hc_lt : c < 1) {n : ℕ} (hn : veryLargeSumsetStrictThreshold γ c < n) :
    18 * log (densityCoefficient (3 + γ) c * log n) ≤ γ * log n := by
  have hb := one_lt_mul_densityCoefficient_div hγ_pos hγ_le hc_pos hc_lt
  have hb₀ := zero_lt_one.trans hb
  have hx : 36 / γ * log (18 * densityCoefficient (3 + γ) c / γ) ≤ log n := by
    rw [← log_rpow hb₀]
    exact log_le_log (rpow_pos_of_pos hb₀ _)
      ((Nat.le_ceil _).trans (mod_cast veryLargeSumsetThreshold_le hn))
  have hn₀ : 0 < log (n : ℝ) := (mul_pos (by positivity) (log_pos hb)).trans_le hx
  have hy : 0 < γ * log n / 18 := by positivity
  have h : densityCoefficient (3 + γ) c * log n =
      18 * densityCoefficient (3 + γ) c / γ * (γ * log n / 18) := by
    field_simp
  rw [div_mul_eq_mul_div, div_le_iff₀ hγ_pos] at hx
  rw [h, log_mul hb₀.ne' hy.ne']
  linarith [log_le_half_self hy]

private lemma pairCardThreshold_pos (n : ℕ) (τ : ℝ) (δ : unitInterval) (hτ : 0 < τ)
    (hδ : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) (hn : 1 < n) :
    0 < pairCardThreshold τ n δ := by
  rw [pairCardThreshold, Nat.ceil_pos]
  exact div_pos (mul_pos hτ (log_pos (mod_cast hn))) (log_pos (one_lt_one_div hδ hδ_lt))

private lemma log_pairCardThreshold_le {γ c : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1)
    (hc_pos : 0 < c) {n : ℕ} (hn : veryLargeSumsetStrictThreshold γ c < n) {δ : unitInterval}
    (hδ_pos : 0 < (δ : ℝ)) (hδ_upper : (δ : ℝ) ≤ 1 - c)
    (hk : 0 < pairCardThreshold (3 + γ) n δ) :
    18 * log (pairCardThreshold (3 + γ) n δ) ≤ γ * log n := by
  have hc_lt : c < 1 := by linarith
  refine le_trans ?_ (log_densityCoefficient_mul_log_le hγ_pos hγ_le hc_pos hc_lt hn)
  gcongr
  exact pairCardThreshold_le_densityCoefficient_mul_log (by linarith) hc_pos
    (two_le_of_veryLargeSumsetStrictThreshold_lt hγ_pos hγ_le hc_pos hc_lt hn) hδ_pos hδ_upper

/-- The pairs `(A, B)` of `k`-subsets of `[n]` with `|A + B| = m`. -/
def veryLargeSumsetPairSlice (n k m : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((interval n).powersetCard k ×ˢ (interval n).powersetCard k).filter fun p ↦
    #(p.1 + p.2) = m

private lemma mem_veryLargeSumsetPairSlice {n k m : ℕ} {p : Finset ℕ × Finset ℕ} :
    p ∈ veryLargeSumsetPairSlice n k m ↔
      p.1 ⊆ interval n ∧ p.2 ⊆ interval n ∧ #p.1 = k ∧ #p.2 = k ∧ #(p.1 + p.2) = m := by
  simp only [veryLargeSumsetPairSlice, mem_filter, mem_product, mem_powersetCard]
  tauto

/-- There are at most `n ^ (k + m / k) * (k ^ 3).choose k` pairs `(A, B)` of `k`-subsets of `[n]`
with `|A + B| = m`. -/
lemma veryLargeSumsetPairSlice_card_le (n k m : ℕ) :
    #(veryLargeSumsetPairSlice n k m) ≤ n ^ (k + m / k) * (k ^ 3).choose k := by
  rw [← Set.ncard_coe_finset]
  refine (Set.ncard_le_ncard ?_ ((finite_toSet _).subset (smallSumsetPairs_subset n k m))).trans
    (pair_small_sumset_family_card_le n k m)
  intro p hp
  obtain ⟨hA, hB, hAk, hBk, hAB⟩ := mem_veryLargeSumsetPairSlice.1 (mem_coe.1 hp)
  exact ⟨hA, hB, hAk, hBk, hAB.le⟩

/-- The set `S` contains a sumset `A + B` with `A, B ⊆ [n]`, `|A| = |B| = k` and
`|A + B| ≥ (k + 1) * k / 2`. -/
def veryLargeSumsetEvent (n k : ℕ) (S : Finset ℕ) : Prop :=
  ∃ A B : Finset ℕ,
    A ⊆ interval n ∧ B ⊆ interval n ∧ #A = k ∧ #B = k ∧
      (k + 1) * k / 2 ≤ #(A + B) ∧ A + B ⊆ S

/-- The union bound for `veryLargeSumsetEvent`, over the pairs `(A, B)` grouped by `m = |A + B|`.
Here `prob m` bounds the probability that a fixed sumset of size `m` is contained in the random
set. -/
lemma veryLargeSumsetEvent_measure_le_sum (n k : ℕ) {δ : unitInterval} (prob : ℕ → ℝ)
    (hprob_nonneg : ∀ m, 0 ≤ prob m)
    (hpair :
      ∀ m (p : Finset ℕ × Finset ℕ), p ∈ veryLargeSumsetPairSlice n k m →
        (binomialFinsetSubset (Set.Icc 1 n) δ).real
          {S : Finset ℕ | p.1 + p.2 ⊆ S} ≤ prob m) :
    (binomialFinsetSubset (Set.Icc 1 n) δ).real {S : Finset ℕ | veryLargeSumsetEvent n k S} ≤
      ∑ m ∈ Icc ((k + 1) * k / 2) (k * k),
        (n ^ (k + m / k) * (k ^ 3).choose k : ℝ) * prob m := by
  have hsub : {S : Finset ℕ | veryLargeSumsetEvent n k S} ⊆
      ⋃ m ∈ Icc ((k + 1) * k / 2) (k * k),
        ⋃ p ∈ veryLargeSumsetPairSlice n k m, {S : Finset ℕ | p.1 + p.2 ⊆ S} := by
    rintro S ⟨A, B, hA, hB, hAk, hBk, hlarge, hS⟩
    refine Set.mem_iUnion₂.2 ⟨#(A + B), mem_Icc.2 ⟨hlarge, ?_⟩, Set.mem_iUnion₂.2 ⟨(A, B), ?_, hS⟩⟩
    · exact card_add_le.trans_eq (by rw [hAk, hBk])
    · exact mem_veryLargeSumsetPairSlice.2 ⟨hA, hB, hAk, hBk, rfl⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le _ _).trans ?_)
  gcongr with m
  refine (measureReal_biUnion_finset_le _ _).trans ((sum_le_card_nsmul _ _ _ (hpair m)).trans ?_)
  rw [nsmul_eq_mul]
  gcongr
  · exact hprob_nonneg m
  · exact_mod_cast veryLargeSumsetPairSlice_card_le n k m

/-- For fixed `A` and `B`, the probability that the random subset of `[n]` of density `δ` contains
`A + B` is at most `δ ^ |A + B|`. -/
lemma fixed_pair_sumset_probability_le (n : ℕ) (δ : unitInterval) (A B : Finset ℕ) :
    (binomialFinsetSubset (Set.Icc 1 n) δ).real {S : Finset ℕ | A + B ⊆ S} ≤
      (δ : ℝ) ^ #(A + B) :=
  binomialFinsetSubset_real_superset_nat δ (Set.finite_Icc 1 n)

/-- If `k = pairCardThreshold τ n δ` is positive, then `δ ^ m ≤ n ^ (-τ * m / k)`. -/
lemma unitInterval_pow_le_exp_div_mul_log (n m : ℕ) (τ : ℝ) (δ : unitInterval)
    (hδ : 0 < δ) (hδ_lt : δ < 1) (hn : 1 < n)
    (hkpos : 0 < pairCardThreshold τ n δ) :
    (δ : ℝ) ^ m ≤ (n : ℝ) ^ (-τ * (m : ℝ) / pairCardThreshold τ n δ : ℝ) := by
  have hδ₀ : (0 : ℝ) < δ := hδ
  have hk : (0 : ℝ) < pairCardThreshold τ n δ := mod_cast hkpos
  have hceil : τ * log n / log (1 / δ) ≤ pairCardThreshold τ n δ := Nat.le_ceil _
  rw [div_le_iff₀ (log_pos (one_lt_one_div hδ₀ hδ_lt)), one_div, log_inv] at hceil
  rw [← rpow_natCast, rpow_def_of_pos hδ₀, rpow_def_of_pos (by positivity), exp_le_exp,
    ← mul_div_assoc, le_div_iff₀ hk]
  linarith [mul_le_mul_of_nonneg_right hceil (Nat.cast_nonneg m)]

private lemma le_two_mul_div {k m : ℕ} (hk : 0 < k) (hm : (k + 1) * k / 2 ≤ m) :
    k ≤ 2 * (m / k) := by
  by_contra! h
  have h₁ : (m / k + 1) * k ≤ (k + 1) * k / 2 := by
    rw [Nat.le_div_iff_mul_le two_pos]
    nlinarith
  exact ((Nat.div_lt_iff_lt_mul hk).1 (Nat.lt_succ_self _)).not_ge (h₁.trans hm)

private lemma choose_cube_le_rpow {γ : ℝ} {n k : ℕ} (hn : (0 : ℝ) < n) (hk : 0 < k)
    (hlogk : 18 * log k ≤ γ * log n) :
    ((k ^ 3).choose k : ℝ) ≤ (n : ℝ) ^ (γ * k / 6) := by
  have hk₀ : (0 : ℝ) < k := mod_cast hk
  refine (Nat.cast_le.2 (Nat.choose_le_pow (k ^ 3) k)).trans ?_
  rw [← pow_mul, Nat.cast_pow, ← rpow_natCast, rpow_def_of_pos hk₀, rpow_def_of_pos hn, exp_le_exp,
    Nat.cast_mul, Nat.cast_ofNat]
  linarith [mul_le_mul_of_nonneg_right hlogk hk₀.le]

private lemma cast_add_div_add_le {γ : ℝ} (hγ : 0 < γ) {k m : ℕ} (hk : 0 < k)
    (hm : (k + 1) * k / 2 ≤ m) :
    ((k + m / k : ℕ) : ℝ) + -(3 + γ) * m / k ≤ -γ * k / 2 := by
  have hk₀ : (0 : ℝ) < k := mod_cast hk
  have h₁ : (k : ℝ) ≤ 2 * (m / k : ℕ) := mod_cast le_two_mul_div hk hm
  have h₂ : ((m / k : ℕ) : ℝ) * k ≤ m := mod_cast Nat.div_mul_le_self m k
  have h₃ : -(3 + γ) * m / k ≤ -(3 + γ) * (m / k : ℕ) := by
    rw [div_le_iff₀ hk₀]
    nlinarith
  push_cast
  nlinarith

/-- The summand of `veryLargeSumsetAnalyticBound` is at most `n ^ (-γ * k / 3)`. -/
private lemma rpow_mul_choose_mul_pow_le {γ δ : ℝ} (hγ : 0 < γ) {n k m : ℕ} (hn : 1 < n)
    (hk : 0 < k) (hm : (k + 1) * k / 2 ≤ m) (hlogk : 18 * log k ≤ γ * log n) (hδ₀ : 0 ≤ δ)
    (hδ : δ ^ m ≤ (n : ℝ) ^ (-(3 + γ) * m / k)) :
    (n : ℝ) ^ (k + m / k) * (k ^ 3).choose k * δ ^ m ≤ (n : ℝ) ^ (-γ * k / 3) := by
  have hn₀ : (0 : ℝ) < n := by positivity
  refine (mul_le_mul (mul_le_mul_of_nonneg_left (choose_cube_le_rpow hn₀ hk hlogk) (by positivity))
    hδ (by positivity) (by positivity)).trans ?_
  rw [← rpow_natCast, ← rpow_add hn₀, ← rpow_add hn₀]
  exact rpow_le_rpow_of_exponent_le (mod_cast hn.le) (by linarith [cast_add_div_add_le hγ hk hm])

private lemma card_Icc_le_sq {k : ℕ} (hk : 0 < k) : #(Icc ((k + 1) * k / 2) (k * k)) ≤ k ^ 2 := by
  rw [Nat.card_Icc, sq]
  grind [(Nat.div_pos (by nlinarith) two_pos : 0 < (k + 1) * k / 2)]

private lemma veryLargeSumsetAnalyticBound_of_lt {γ c : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1)
    (hc_pos : 0 < c) {n : ℕ} (hn : veryLargeSumsetStrictThreshold γ c < n) {δ : unitInterval}
    (hδ_lower : (n : ℝ) ^ (-(1 / 2 : ℝ)) < (δ : ℝ)) (hδ_upper : (δ : ℝ) ≤ 1 - c) :
    veryLargeSumsetAnalyticBound γ n δ := by
  have hδ₀ : (0 : ℝ) < δ := (rpow_nonneg (Nat.cast_nonneg n) _).trans_lt hδ_lower
  have hδ₁ : (δ : ℝ) < 1 := by linarith
  have hn₂ := two_le_of_veryLargeSumsetStrictThreshold_lt hγ_pos hγ_le hc_pos (by linarith) hn
  have hn₀ : (0 : ℝ) < n := by positivity
  have hk := pairCardThreshold_pos n (3 + γ) δ (by linarith) hδ₀ hδ₁ hn₂
  have hlogk := log_pairCardThreshold_le hγ_pos hγ_le hc_pos hn hδ₀ hδ_upper hk
  have hpow (m : ℕ) :=
    unitInterval_pow_le_exp_div_mul_log n m (3 + γ) δ hδ₀ hδ₁ hn₂ hk
  rw [veryLargeSumsetAnalyticBound]
  generalize pairCardThreshold (3 + γ) n δ = k at hk hlogk hpow ⊢
  refine (sum_le_card_nsmul _ _ ((n : ℝ) ^ (-γ * k / 3)) ?_).trans ?_
  · intro m hm
    obtain ⟨hm, -⟩ := mem_Icc.1 hm
    exact rpow_mul_choose_mul_pow_le hγ_pos hn₂ hk hm hlogk (unitInterval.nonneg δ) (hpow m)
  · rw [nsmul_eq_mul, neg_mul, neg_div, rpow_neg hn₀.le, ← div_eq_mul_inv]
    gcongr
    exact_mod_cast card_Icc_le_sq hk

/-- The probability of `veryLargeSumsetEvent` is at most `k ^ 2 / n ^ (γ * k / 3)` when the union
bound `veryLargeSumsetAnalyticBound` holds. -/
lemma veryLargeSumsetEvent_measure_le (γ : ℝ) (n : ℕ) (δ : unitInterval)
    (hanalytic : veryLargeSumsetAnalyticBound γ n δ) :
    (binomialFinsetSubset (Set.Icc 1 n) δ).real
      {S : Finset ℕ | veryLargeSumsetEvent n (pairCardThreshold (3 + γ) n δ) S} ≤
      (pairCardThreshold (3 + γ) n δ : ℝ) ^ 2 /
        (n : ℝ) ^ (γ * (pairCardThreshold (3 + γ) n δ : ℝ) / 3) := by
  refine (veryLargeSumsetEvent_measure_le_sum n _ (fun m ↦ (δ : ℝ) ^ m)
    (fun m ↦ pow_nonneg (unitInterval.nonneg δ) m) ?_).trans hanalytic
  rintro m ⟨A, B⟩ hp
  obtain ⟨-, -, -, -, rfl⟩ := mem_veryLargeSumsetPairSlice.1 hp
  exact fixed_pair_sumset_probability_le n δ A B

/-- Let `k = ⌈(3 + γ) * log n / log (1 / δ)⌉` and `n ^ (-1 / 2) < δ ≤ 1 - c`. If `n` is large, then
the random subset of `[n]` of density `δ` contains a sumset `A + B` with `A, B ⊆ [n]`,
`|A| = |B| = k` and `|A + B| ≥ (k + 1) * k / 2` with probability at most
`k ^ 2 / n ^ (γ * k / 3)`. -/
lemma very_large_sumset_probability_le {γ c : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1)
    (hc_pos : 0 < c) {n : ℕ} (hn : veryLargeSumsetStrictThreshold γ c < n) {δ : unitInterval}
    (hδ_lower : (n : ℝ) ^ (-(1 / 2 : ℝ)) < (δ : ℝ)) (hδ_upper : (δ : ℝ) ≤ 1 - c) :
    (binomialFinsetSubset (Set.Icc 1 n) δ).real
      {S : Finset ℕ | veryLargeSumsetEvent n (pairCardThreshold (3 + γ) n δ) S} ≤
      (pairCardThreshold (3 + γ) n δ : ℝ) ^ 2 /
        (n : ℝ) ^ (γ * (pairCardThreshold (3 + γ) n δ : ℝ) / 3) :=
  veryLargeSumsetEvent_measure_le γ n δ
    (veryLargeSumsetAnalyticBound_of_lt hγ_pos hγ_le hc_pos hn hδ_lower hδ_upper)

end

end DenseSetsWithoutLargeSumsets
