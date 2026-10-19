/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.CountingBaseBounds
public import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.WitnessPairs
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.LargeSubsetsGAP

/-!
# Sets that contain a small sumset contain the sumset of a small pair

Let `k = pairCardThreshold (3 + γ) n δ` and let `S` contain `A + B` for some `A, B ⊆ [n]` of size
`k` with `|A + B| ≤ C * k`. Theorem 2 of Bollobás, Leader and Tiba gives `A' ⊆ A'' ⊆ A` and
`B' ⊆ B'' ⊆ B` with `|A'|, |B'| ≤ lowerBltConstant C γ * √k`, `|A''|, |B''| ≥ (1 - ε γ) * k` and
`|A' + B'| ≥ (1 - ε γ) * |A'' + B''|`. By Chang's theorem, `A''` and `B''` are contained in the
preimage of a proper progression `P` of `ZMod q`, and
`(1 - ε γ) * |A'' + B''| ≥ (1 - 3 * ε γ) * P.dim * k`. So `(A', B')` is one of the pairs of
`bltDimSmallWitnessPairs` for `P`, and `A' + B' ⊆ S`.

## Main statements

* `pairSumsetIsSubset_event_subset_zmodGAPPreimageDimSmallWitnessPairs`: the sets `S` as above
  are covered by the events `bltWitnessPairSumsetIsSubset p S`, where `P` ranges over
  `lowerModelGAPs` and `p` over the pairs of `bltDimSmallWitnessPairs` for `P`.
-/

@[expose] public section

namespace DenseSetsWithoutLargeSumsets

open Finset ChangFreimanRuzsa LargeSumsetsFromSubsets
open scoped Pointwise

noncomputable section

private lemma one_le_dim_of_subset_zmodGAPPreimageContainer {γ : ℝ} {n q k : ℕ}
    {ψ : ℕ → ZMod q} {A₀ : Finset ℕ} {P : GAP (ZMod q)} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1)
    (hk : 2 ≤ k) (hψ : Set.InjOn ψ (interval n : Set ℕ))
    (hA₀P : A₀ ⊆ zmodGAPPreimageContainer n ψ P) (hA₀large : (1 - ε γ) * k ≤ #A₀) :
    1 ≤ P.dim := by
  by_contra! hdim
  have h := (card_le_card hA₀P).trans (zmodGAPPreimageContainer_card_le_carrier P hψ)
  rw [card_carrier_eq_one_of_dim_eq_zero P (by grind), ← Nat.cast_le (α := ℝ), Nat.cast_one] at h
  have hk₂ : (2 : ℝ) ≤ k := mod_cast hk
  have hε := ε_le_one_twelfth hγ_pos hγ_le
  linarith [mul_le_mul_of_nonneg_left hk₂ (by linarith : 0 ≤ 1 - ε γ)]

private lemma mem_bltDimSmallWitnessPairs_of_le {Q : Finset ℕ} {A' B' : Finset ℤ} {D k : ℕ}
    {C γ : ℝ} (hC : 0 < 2 * C) (hε : 0 < ε γ) (hA'Q : A' ⊆ natCastImage Q)
    (hB'Q : B' ⊆ natCastImage Q) (hA' : #A' ≤ lowerBltConstant C γ hC hε * Real.sqrt k)
    (hB' : #B' ≤ lowerBltConstant C γ hC hε * Real.sqrt k) (hD : 1 ≤ D)
    (hlower : (1 - 3 * ε γ) * D * k ≤ #(A' + B')) :
    (A', B') ∈ bltDimSmallWitnessPairs Q D k C γ := by
  rw [bltDimSmallWitnessPairs, mem_filter, bltSmallWitnessPairs, mem_filter, mem_product,
    mem_powerset, mem_powerset]
  exact ⟨⟨⟨hA'Q, hB'Q⟩, hC, hε, hA', hB'⟩, hD, hlower⟩

private lemma one_sub_mul_le_of_min_le {e C k N a b M : ℝ} (he : e ≤ 1 / 2) (hC : 0 < C)
    (hk : 0 ≤ k) (hN : N ≤ C * k) (ha : (1 - e) * k ≤ a) (hb : (1 - e) * k ≤ b)
    (hmin : min (min ((1 - e) * N) (2 * C * a)) (2 * C * b) ≤ M) :
    (1 - e) * N ≤ M := by
  have he₁ : 0 ≤ 1 - e := by linarith
  have h₁ := mul_le_mul_of_nonneg_left hN he₁
  have h₂ := mul_le_mul_of_nonneg_left ha hC.le
  have h₃ := mul_le_mul_of_nonneg_left hb hC.le
  have h₄ := mul_nonneg hC.le (mul_nonneg he₁ hk)
  exact (le_min (le_min le_rfl (by linarith)) (by linarith)).trans hmin

/-- Let `k = pairCardThreshold (3 + γ) n δ`. If `S` contains `A + B` for some `A, B ⊆ [n]` of size
`k` with `|A + B| ≤ C * k`, then there are a progression `P` in `lowerModelGAPs` and a pair `p` in
`bltDimSmallWitnessPairs` of the preimage of `P` such that `S` contains the sumset of `p`. -/
theorem pairSumsetIsSubset_event_subset_zmodGAPPreimageDimSmallWitnessPairs {γ C c : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (C_pos : 0 < C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c) :
    {S : Finset ℕ |
      pairSumsetIsSubset n (pairCardThreshold (3 + γ) n δ) 0
        (C * pairCardThreshold (3 + γ) n δ) S} ⊆
      ⋃ P ∈ lowerModelGAPs δ hγ_pos C_pos hn,
        ⋃ p ∈ bltDimSmallWitnessPairs
            (zmodGAPPreimageContainer n (zmodModelEmbedding hγ_pos C_pos hn) P)
            P.dim (pairCardThreshold (3 + γ) n δ) C γ,
          {S : Finset ℕ | bltWitnessPairSumsetIsSubset p S} := by
  classical
  rintro S ⟨A, B, hAint, hBint, hAcard, hBcard, -, hAB, hABS⟩
  have hk := pairCardThreshold_pos_of_lower_density hγ_pos hn hδ_lower hδ_upper
  have hC := one_le_sumset_card_coefficient_of_threshold_pair_sumset hγ_pos hn hδ_lower hδ_upper
    hAcard hBcard hAB
  have hψ := zmodModelEmbedding_iso hγ_pos C_pos hn
  obtain ⟨A', A'', B', B'', hA'A'', hA''A, hB'B'', hB''B, hA''card, hB''card, hA'card, hB'card,
      hsum⟩ :=
    exists_medium_sized_subsets_with_large_sumset_subsets (σ := 2 * C) (ε := ε γ) (by positivity)
      (ε_pos hγ_pos) (natCastImage_nonempty_of_card_eq hAcard hk)
      (natCastImage_nonempty_of_card_eq hBcard hk)
  have hA₀large := bltLargePreimage_large_of_blt hAcard hA''A hA''card
  have hB₀large := bltLargePreimage_large_of_blt hBcard hB''B hB''card
  have hA₀ := natCastImage_bltLargePreimage_eq_of_subset hA''A
  have hB₀ := natCastImage_bltLargePreimage_eq_of_subset hB''B
  simp only [natCastImage_card, hAcard, hBcard, max_self] at hA''card hB''card hA'card hB'card
  obtain ⟨P, hP, hA₀P, hB₀P, hPdim, hdim⟩ :=
    largeSubsets_exists_zmodGAPPreimageContainer hγ_pos hγ_le C_pos hc_pos hc_lt hn hn_gap
      hδ_lower hδ_upper hδ_upper_c hAint hBint hAcard hBcard (bltLargePreimage_subset A A'')
      (bltLargePreimage_subset B B'') hA₀large hB₀large hAB
  rw [mem_properGAPsZModUpToDim] at hP
  have hdim₁ := one_le_dim_of_subset_zmodGAPPreimageContainer hγ_pos hγ_le
    (two_le_pairCardThreshold_of_one_le hγ_pos hC hn hδ_lower hδ_upper) hψ.bijOn.injOn hA₀P
    hA₀large
  have hlower := large_subsets_first_term_lower_by_dim hγ_pos hγ_le hC
    (one_lt_nat_of_lowerSizeThreshold_lt hn) hδ_lower hδ_upper hψ
    ((bltLargePreimage_subset A A'').trans hAint) ((bltLargePreimage_subset B B'').trans hBint)
    rfl hk hA₀large hB₀large hPdim hdim
  rw [hA₀, hB₀] at hlower
  rw [← natCastImage_card (A + B)] at hAB
  have hA''B'' := (Nat.cast_le (α := ℝ)).2
    (card_le_card (natCastImage_add_subset hA''A hB''B subset_rfl))
  refine Set.mem_iUnion₂.2 ⟨P, mem_biUnion.2 ⟨P.dim, mem_Icc.2 ⟨hdim₁, hP.2.1⟩,
    (mem_properGAPsZModOfDim _).2 ⟨hP.1, rfl, hP.2.2⟩⟩, ?_⟩
  refine Set.mem_iUnion₂.2 ⟨(A', B'), ?_,
    natCastImage_add_subset (hA'A''.trans hA''A) (hB'B''.trans hB''B) hABS⟩
  refine mem_bltDimSmallWitnessPairs_of_le (by positivity) (ε_pos hγ_pos) ?_ ?_ hA'card hB'card
    hdim₁ ?_
  · exact hA'A''.trans (hA₀.superset.trans (natCastImage_mono hA₀P))
  · exact hB'B''.trans (hB₀.superset.trans (natCastImage_mono hB₀P))
  · exact hlower.trans (one_sub_mul_le_of_min_le (ε_lt_one_half hγ_pos hγ_le).le C_pos
      (Nat.cast_nonneg _) (hA''B''.trans hAB) hA''card hB''card hsum)

end

end DenseSetsWithoutLargeSumsets
