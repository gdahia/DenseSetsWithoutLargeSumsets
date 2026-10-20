/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.WitnessPairs
public import DenseSetsWithoutLargeSumsets.Probability

/-!
# The probability that a random set contains a given sumset

Let `S` be a `δ`-random subset of `[n]`. For a pair `(A', B')` of sets of integers, the
probability that `A' + B' ⊆ S` is at most `δ ^ |A' + B'|`. We sum this bound over the pairs in
`bltDimSmallWitnessPairs` and over the proper progressions of each dimension. This is the union
bound of Section 2 of *Dense sets without large sumsets* (Dahia, Marciano, Souza).

## Main statements

* `bltWitnessPair_probability_le`: the probability that `A' + B' ⊆ S` is at most
  `δ ^ |A' + B'|`.
* `dim_fingerprint_sum_le_gap_dim_sum`: the sum of `δ ^ |A' + B'|` over the proper progressions
  `P` of dimension `1 ≤ d ≤ k` with at most `s` points and over the pairs `(A', B')` in
  `bltDimSmallWitnessPairs` of the preimage of `P` is at most the sum over `d` of the number of
  progressions times `((m + 1) * (s + 1) ^ m) ^ 2 * exp (-(1 - 3 * ε γ) * d * k * log (1 / δ))`,
  where `m = ⌈lowerBltConstant C γ * √k⌉₊`.
-/

@[expose] public section

namespace DenseSetsWithoutLargeSumsets

open Finset MeasureTheory ChangFreimanRuzsa
open scoped Pointwise

noncomputable section

private lemma toNat_injOn_of_subset_natCastImage {T : Finset ℤ} {S : Finset ℕ}
    (hT : T ⊆ natCastImage S) :
    Set.InjOn Int.toNat (T : Set ℤ) := by
  intro z hz w hw hzw
  obtain ⟨a, -, rfl⟩ := mem_image.1 (hT hz)
  obtain ⟨b, -, rfl⟩ := mem_image.1 (hT hw)
  simpa using hzw

/-- Let `S` be a `δ`-random subset of `[n]`. The probability that the sumset of the pair `p` is
contained in `S` is at most `δ ^ |p.1 + p.2|`. -/
lemma bltWitnessPair_probability_le (n : ℕ) {δ : unitInterval}
    (p : Finset ℤ × Finset ℤ) :
    (binomialFinsetSubset (Set.Icc 1 n) δ).real
        {S : Finset ℕ | bltWitnessPairSumsetIsSubset p S} ≤
      (δ : ℝ) ^ #(p.1 + p.2) := by
  obtain h | ⟨S₀, hS₀⟩ :=
    Set.eq_empty_or_nonempty {S : Finset ℕ | bltWitnessPairSumsetIsSubset p S}
  · rw [h, measureReal_empty]
    exact pow_nonneg δ.2.1 _
  rw [← card_image_of_injOn (toNat_injOn_of_subset_natCastImage hS₀)]
  refine (measureReal_mono ?_).trans
    (binomialFinsetSubset_real_superset_nat δ (Set.finite_Icc 1 n))
  intro S hS x hx
  obtain ⟨z, hz, rfl⟩ := mem_image.1 hx
  obtain ⟨s, hs, rfl⟩ := mem_image.1 (hS hz)
  simpa using hs

private lemma pow_le_exp_neg_mul_log_one_div {δ : unitInterval} {m : ℕ} {L : ℝ}
    (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) (hL : L ≤ (m : ℝ)) :
    (δ : ℝ) ^ m ≤ Real.exp (-L * Real.log (1 / δ)) := by
  rw [one_div, Real.log_inv, neg_mul_neg, mul_comm, ← Real.rpow_def_of_pos hδ_pos,
    ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt.le hL

private lemma sum_bltDimSmallWitnessPairs_pow_le (P : Finset ℕ) (D k : ℕ)
    (C γ : ℝ) {δ : unitInterval} (hC : 0 < 2 * C) (hε : 0 < ε γ)
    (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) :
    ∑ p ∈ bltDimSmallWitnessPairs P D k C γ, (δ : ℝ) ^ #(p.1 + p.2) ≤
      (((⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1) *
          (#(natCastImage P) + 1) ^
            ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ : ℝ) *
        ((⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1) *
          (#(natCastImage P) + 1) ^
            ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ : ℝ)) *
        Real.exp (-((1 - 3 * ε γ) * (D : ℝ) * (k : ℝ)) * Real.log (1 / δ)) := by
  have h : ∀ p ∈ bltDimSmallWitnessPairs P D k C γ, (δ : ℝ) ^ #(p.1 + p.2) ≤
      Real.exp (-((1 - 3 * ε γ) * (D : ℝ) * (k : ℝ)) * Real.log (1 / δ)) := by
    intro p hp
    rw [bltDimSmallWitnessPairs, mem_filter] at hp
    exact pow_le_exp_neg_mul_log_one_div hδ_pos hδ_lt hp.2.2
  refine (sum_le_card_nsmul _ _ _ h).trans ?_
  rw [nsmul_eq_mul]
  gcongr
  exact mod_cast bltDimSmallWitnessPairs_card_le P D k C γ hC hε

/-- The sum of `δ ^ |A' + B'|` over the proper progressions `P` of dimension `1 ≤ d ≤ k` with at
most `s` points in `ZMod q` and over the pairs `(A', B')` in `bltDimSmallWitnessPairs` of the
preimage of `P` under `ψ`. For each `d` it is at most the number of progressions times
`((m + 1) * (s + 1) ^ m) ^ 2 * exp (-(1 - 3 * ε γ) * d * k * log (1 / δ))`, where
`m = ⌈lowerBltConstant C γ * √k⌉₊`. -/
lemma dim_fingerprint_sum_le_gap_dim_sum {q n k s : ℕ} (ψ : ℕ → ZMod q)
    (hqpos : 0 < q) (hψinj : Set.InjOn ψ (interval n : Set ℕ))
    {C γ : ℝ} {δ : unitInterval} (hC : 0 < 2 * C) (hε : 0 < ε γ)
    (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) :
    ∑ P ∈ (by
        classical
        exact (Finset.Icc 1 k).biUnion (fun d ↦ properGAPsZModOfDim d s hqpos) :
        Finset (GAP (ZMod q))),
        ∑ p ∈ bltDimSmallWitnessPairs (zmodGAPPreimageContainer n ψ P) P.dim k C γ,
          (δ : ℝ) ^ #(p.1 + p.2) ≤
      ∑ d ∈ Finset.Icc 1 k,
        (#(properGAPsZModOfDim d s hqpos) : ℝ) *
          (((⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1) *
              (s + 1) ^
                ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ : ℝ) *
            ((⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1) *
              (s + 1) ^
                ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ : ℝ)) *
          Real.exp (-((1 - 3 * ε γ) * (d : ℝ) * (k : ℝ)) * Real.log (1 / δ)) := by
  classical
  rw [sum_biUnion]
  · refine sum_le_sum ?_
    intro d _
    rw [mul_assoc, ← nsmul_eq_mul]
    refine sum_le_card_nsmul _ _ _ ?_
    intro P hP
    obtain ⟨-, rfl, hPs⟩ := (mem_properGAPsZModOfDim hqpos).1 hP
    have hcard := (zmodGAPPreimageContainer_card_le_carrier P hψinj).trans hPs
    refine (sum_bltDimSmallWitnessPairs_pow_le _ _ k C γ hC hε hδ_pos hδ_lt).trans ?_
    rw [natCastImage_card]
    gcongr
  · intro d _ d' _ hdd'
    refine disjoint_left.2 ?_
    intro P hP hP'
    obtain ⟨-, hPd, -⟩ := (mem_properGAPsZModOfDim hqpos).1 hP
    obtain ⟨-, hPd', -⟩ := (mem_properGAPsZModOfDim hqpos).1 hP'
    exact hdd' (hPd.symm.trans hPd')

end

end DenseSetsWithoutLargeSumsets
