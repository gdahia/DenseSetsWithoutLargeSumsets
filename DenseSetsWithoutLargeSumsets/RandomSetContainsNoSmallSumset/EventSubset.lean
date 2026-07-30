/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.ExponentBounds
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.FreimanDimension
import DenseSetsWithoutLargeSumsets.Probability
import DenseSetsWithoutLargeSumsets.Common
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.GeneralizedArithmeticProgression
import DenseSetsWithoutLargeSumsets.LargeSumsetsFromMediumSizedSubsets.MediumSizedSubsets
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.Chang.Reduction
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.NumberTheory.Bertrand

/-!
Reduction of the small-sumset event to a union over GAPs and witness pairs.

Proves `pairSumsetIsSubset_event_subset_zmodGAPPreimageDimSmallWitnessPairs`: a pair with small
sumset always produces a large-subset pair contained in some proper GAP's preimage, whose BLT
fingerprint pair is dimension-compatible small witness pair, so the small-sumset event is
covered by the corresponding union of witness-pair sumset events.
-/

namespace DenseSetsWithoutLargeSumsets

open Nat hiding div_pos
open scoped Pointwise

noncomputable section

private lemma eleven_twelfths_le_one_sub_ε {γ : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) :
    (11 / 12 : ℝ) ≤ 1 - ε γ := by
  linarith [ε_le_one_twelfth hγ_pos hγ_le]

private lemma one_lt_eleven_twelfths_mul_pairCardThreshold {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    (1 : ℝ) < (11 / 12 : ℝ) * pairCardThreshold (3 + γ) n δ := by
  refine (by norm_num : (1 : ℝ) < (11 / 12 : ℝ) * 2).trans_le ?_
  apply mul_le_mul_of_nonneg_left
  · exact_mod_cast two_le_pairCardThreshold_of_one_le hγ_pos hC_one hn hδ_lower hδ_upper
  · norm_num

private lemma properGAP_dim_pos_of_large_preimage {γ C : ℝ} {n q : ℕ}
    {δ : unitInterval} {ψ : ℕ → ZMod q} {A₀ : Finset ℕ} {P : ProperGAP (ZMod q)}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ)
    (hA₀P : A₀ ⊆ zmodGAPPreimageContainer n ψ P)
    (hA₀large : (1 - ε γ) * (pairCardThreshold (3 + γ) n δ : ℝ) ≤ (A₀.card : ℝ)) :
    1 ≤ P.dim := by
  by_contra hdim_not
  exact (not_lt_of_ge
    ((Finset.card_le_card hA₀P).trans
      ((zmodGAPPreimageContainer_card_le_carrier P hψ.bijOn.injOn).trans_eq
        (properGAP_card_eq_one_of_dim_zero P (Nat.eq_zero_of_not_pos hdim_not)))))
    (by
      exact_mod_cast
        ((one_lt_eleven_twelfths_mul_pairCardThreshold hγ_pos hC_one hn hδ_lower hδ_upper).trans_le
          ((mul_le_mul_of_nonneg_right (eleven_twelfths_le_one_sub_ε hγ_pos hγ_le)
            (by positivity)).trans hA₀large)))

private lemma subset_natCast_preimage_of_blt_subset {A Q : Finset ℕ} {A' A'' : Finset ℤ}
    (hA'A'' : A' ⊆ A'') (hA''A : A'' ⊆ natCastImage A)
    (hA₀P : bltLargePreimage A A'' ⊆ Q) :
    A' ⊆ natCastImage Q := by
  intro z hz
  apply natCastImage_mono hA₀P
  rw [natCastImage_bltLargePreimage_eq_of_subset hA''A]
  exact hA'A'' hz

private lemma max_natCastImage_card_eq_of_cards {A B : Finset ℕ} {k : ℕ}
    (hAcard : A.card = k) (hBcard : B.card = k) :
    max ((natCastImage A).card : ℝ) ((natCastImage B).card : ℝ) = (k : ℝ) := by
  rw [natCastImage_card A, natCastImage_card B, hAcard, hBcard]
  simp

private lemma mem_bltSmallWitnessPairs_of_subsets_and_sizes {Q : Finset ℕ}
    {A' B' : Finset ℤ} {k : ℕ} {C γ : ℝ}
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ)
    (hA'Q : A' ⊆ natCastImage Q) (hB'Q : B' ⊆ natCastImage Q)
    (hA'size : (A'.card : ℝ) ≤ lowerBltConstant C γ hC_two hε * Real.sqrt (k : ℝ))
    (hB'size : (B'.card : ℝ) ≤ lowerBltConstant C γ hC_two hε * Real.sqrt (k : ℝ)) :
    (A', B') ∈ bltSmallWitnessPairs Q k C γ := by
  rw [bltSmallWitnessPairs, Finset.mem_filter]
  refine ⟨?_, hC_two, hε, hA'size, hB'size⟩
  rw [Finset.mem_product]
  constructor
  · rw [Finset.mem_powerset]
    exact hA'Q
  · rw [Finset.mem_powerset]
    exact hB'Q

private lemma first_lower_for_bltLargePreimage {γ C : ℝ} {n q : ℕ}
    {δ : unitInterval} {ψ : ℕ → ZMod q} {A B : Finset ℕ} {A'' B'' : Finset ℤ}
    {D k : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ)
    (hAint : A ⊆ interval n) (hBint : B ⊆ interval n)
    (hA''A : A'' ⊆ natCastImage A) (hB''B : B'' ⊆ natCastImage B)
    (hkdef : k = pairCardThreshold (3 + γ) n δ) (hkpos : 0 < k)
    (hA₀large :
      (1 - ε γ) * (k : ℝ) ≤ ((bltLargePreimage A A'').card : ℝ))
    (hB₀large :
      (1 - ε γ) * (k : ℝ) ≤ ((bltLargePreimage B B'').card : ℝ))
    (hDdim : D ≤ freimanDim ((bltLargePreimage A A'').image ψ ∪
      (bltLargePreimage B B'').image ψ))
    (hdim_bound : freimanDim ((bltLargePreimage A A'').image ψ ∪
      (bltLargePreimage B B'').image ψ) ≤ 2 * ⌈κ C⌉₊ - 1) :
    (1 - 3 * ε γ) * (D : ℝ) * (k : ℝ) ≤
      (1 - ε γ) * ((A'' + B'').card : ℝ) := by
  simpa [natCastImage_bltLargePreimage_eq_of_subset hA''A,
    natCastImage_bltLargePreimage_eq_of_subset hB''B] using
    large_subsets_first_term_lower_by_dim (γ := γ) (C := C) (n := n) (q := q)
      (δ := δ) (ψ := ψ) (A₀ := bltLargePreimage A A'')
      (B₀ := bltLargePreimage B B'') (D := D) (k := k)
      hγ_pos hγ_le hC_one (one_lt_nat_of_lowerSizeThreshold_lt hn) hδ_lower hδ_upper hψ
      ((bltLargePreimage_subset A A'').trans hAint)
      ((bltLargePreimage_subset B B'').trans hBint) hkdef hkpos hA₀large hB₀large
      hDdim hdim_bound

private lemma blt_large_sum_card_le {A B : Finset ℕ} {A'' B'' : Finset ℤ}
    {k : ℕ} {C : ℝ}
    (hA''A : A'' ⊆ natCastImage A) (hB''B : B'' ⊆ natCastImage B)
    (hAB : (A + B).card ≤ C * k) :
    ((A'' + B'').card : ℝ) ≤ C * (k : ℝ) := by
  refine (by
    exact_mod_cast Finset.card_le_card
      (natCastImage_add_subset hA''A hB''B (by intro x hx; exact hx)) :
    ((A'' + B'').card : ℝ) ≤ ((natCastImage (A + B)).card : ℝ)).trans ?_
  rw [natCastImage_card]
  exact hAB

private lemma first_term_le_two_mul_large_card {γ C : ℝ} {k : ℕ} {A'' B'' : Finset ℤ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (C_pos : 0 < C)
    (hAB : ((A'' + B'').card : ℝ) ≤ C * (k : ℝ))
    (hA''large : (1 - ε γ) * (k : ℝ) ≤ (A''.card : ℝ)) :
    (1 - ε γ) * ((A'' + B'').card : ℝ) ≤ (2 * C) * (A''.card : ℝ) := by
  refine (mul_le_mul_of_nonneg_left hAB
    ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans (half_le_one_sub_ε hγ_pos hγ_le))).trans ?_
  refine le_trans (b := C * ((1 - ε γ) * (k : ℝ))) ?_ ?_
  · ring_nf
    exact le_rfl
  · refine (mul_le_mul_of_nonneg_left hA''large C_pos.le).trans ?_
    nlinarith [mul_nonneg C_pos.le (by positivity : 0 ≤ (A''.card : ℝ))]

private lemma first_term_le_two_mul_right_large_card {γ C : ℝ} {k : ℕ} {A'' B'' : Finset ℤ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (C_pos : 0 < C)
    (hAB : ((A'' + B'').card : ℝ) ≤ C * (k : ℝ))
    (hB''large : (1 - ε γ) * (k : ℝ) ≤ (B''.card : ℝ)) :
    (1 - ε γ) * ((A'' + B'').card : ℝ) ≤ (2 * C) * (B''.card : ℝ) := by
  refine (mul_le_mul_of_nonneg_left hAB
    ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans (half_le_one_sub_ε hγ_pos hγ_le))).trans ?_
  refine le_trans (b := C * ((1 - ε γ) * (k : ℝ))) ?_ ?_
  · ring_nf
    exact le_rfl
  · refine (mul_le_mul_of_nonneg_left hB''large C_pos.le).trans ?_
    nlinarith [mul_nonneg C_pos.le (by positivity : 0 ≤ (B''.card : ℝ))]

private lemma first_term_le_blt_pair_sum {γ C : ℝ} {A' B' A'' B'' : Finset ℤ}
    (hfirst_le_second :
      (1 - ε γ) * ((A'' + B'').card : ℝ) ≤ (2 * C) * (A''.card : ℝ))
    (hfirst_le_third :
      (1 - ε γ) * ((A'' + B'').card : ℝ) ≤ (2 * C) * (B''.card : ℝ))
    (hsum :
      min (min ((1 - ε γ) * ((A'' + B'').card : ℝ)) ((2 * C) * (A''.card : ℝ)))
          ((2 * C) * (B''.card : ℝ)) ≤ ((A' + B').card : ℝ)) :
    (1 - ε γ) * ((A'' + B'').card : ℝ) ≤ ((A' + B').card : ℝ) := by
  simpa [min_eq_left hfirst_le_second, min_eq_left hfirst_le_third] using hsum

private lemma mem_bltDimSmallWitnessPairs_of_lower {Q : Finset ℕ} {A' B' : Finset ℤ}
    {D k : ℕ} {C γ : ℝ}
    (hsmall : (A', B') ∈ bltSmallWitnessPairs Q k C γ)
    (hDpos : 1 ≤ D)
    (hlower : (1 - 3 * ε γ) * (D : ℝ) * (k : ℝ) ≤ ((A' + B').card : ℝ)) :
    (A', B') ∈ bltDimSmallWitnessPairs Q D k C γ := by
  rw [bltDimSmallWitnessPairs, Finset.mem_filter]
  exact ⟨hsmall, hDpos, hlower⟩

private lemma mem_lowerModelGAPs_of_mem_upToDim {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    {hγ_pos : 0 < γ} {C_pos : 0 < C} {hn : lowerSizeThreshold C γ < n}
    {P : ProperGAP (ZMod (zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn))}
    (hPmem : P ∈ properGAPsZModUpToDim (pairCardThreshold (3 + γ) n δ)
      ⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊
      (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).pos)
    (hPdim_pos : 1 ≤ P.dim) :
    P ∈ lowerModelGAPs (γ := γ) (C := C) (n := n) δ hγ_pos C_pos hn := by
  classical
  rw [lowerModelGAPs, Finset.mem_biUnion]
  refine ⟨P.dim, Finset.mem_Icc.mpr ⟨hPdim_pos,
    ((mem_properGAPsZModUpToDim
      (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).pos).1 hPmem).1⟩,
    ?_⟩
  rw [mem_properGAPsZModOfDim
    (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).pos]
  exact ⟨rfl, ((mem_properGAPsZModUpToDim
    (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).pos).1 hPmem).2⟩

/--
Direct structural reduction for the small-sumset event. This is the BLT-first version:
the GAP is chosen for the large BLT subsets, and only the small BLT fingerprint pair is required
to lie in the integer preimage container.
-/
lemma pairSumsetIsSubset_event_subset_zmodGAPPreimageDimSmallWitnessPairs {γ C c : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (C_pos : 0 < C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c) :
    {S : Finset ℕ |
      pairSumsetIsSubset n (pairCardThreshold (3 + γ) n δ) 0
        (C * pairCardThreshold (3 + γ) n δ) S} ⊆
      ⋃ P ∈ lowerModelGAPs (γ := γ) (C := C) (n := n) δ hγ_pos C_pos hn,
        ⋃ p ∈ bltDimSmallWitnessPairs
            (zmodGAPPreimageContainer n
              (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) P)
            P.dim (pairCardThreshold (3 + γ) n δ) C γ,
          {S : Finset ℕ | bltWitnessPairSumsetIsSubset p S} := by
  classical
  intro S hS
  rcases hS with ⟨A, B, hAint, hBint, hAcard, hBcard, _hAB_lower, hAB, hAB_subset⟩
  obtain ⟨A', A'', B', B'', hblt⟩ :=
    exists_medium_sized_subsets_with_large_sumset_subsets (G := ℤ) (σ := 2 * C) (ε := ε γ)
      (by positivity) (ε_pos hγ_pos)
      (natCastImage_nonempty_of_card_eq hAcard
        (pairCardThreshold_pos_of_lower_density hγ_pos hn hδ_lower hδ_upper))
      (natCastImage_nonempty_of_card_eq hBcard
        (pairCardThreshold_pos_of_lower_density hγ_pos hn hδ_lower hδ_upper))
  rcases hblt with
    ⟨hA'A'', hA''A, hB'B'', hB''B, hA''card, hB''card, hA'card, hB'card, hsum⟩
  obtain ⟨P, hPmem, hA₀P, hB₀P, hPdim, hdim_bound⟩ :=
    largeSubsets_exists_zmodGAPPreimageContainer (γ := γ) (C := C) (c := c) (n := n)
      (δ := δ) hγ_pos hγ_le C_pos hc_pos hc_lt hn hn_gap hδ_lower hδ_upper hδ_upper_c
      hAint hBint hAcard hBcard
      (bltLargePreimage_subset A A'') (bltLargePreimage_subset B B'')
      (bltLargePreimage_large_of_blt hAcard hA''A hA''card)
      (bltLargePreimage_large_of_blt hBcard hB''B hB''card) hAB
  refine Set.mem_iUnion₂.mpr ⟨P, ?_, ?_⟩
  · exact mem_lowerModelGAPs_of_mem_upToDim hPmem
      (properGAP_dim_pos_of_large_preimage hγ_pos hγ_le
        (one_le_sumset_card_coefficient_of_threshold_pair_sumset hγ_pos hn hδ_lower hδ_upper
          hAcard hBcard hAB)
        hn hδ_lower hδ_upper
        (zmodModelEmbedding_iso (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) hA₀P
        (bltLargePreimage_large_of_blt hAcard hA''A hA''card))
  refine Set.mem_iUnion₂.mpr ⟨(A', B'), ?_, ?_⟩
  · apply mem_bltDimSmallWitnessPairs_of_lower
    · exact mem_bltSmallWitnessPairs_of_subsets_and_sizes
        (by positivity : 0 < 2 * C) (ε_pos hγ_pos)
        (subset_natCast_preimage_of_blt_subset hA'A'' hA''A hA₀P)
        (subset_natCast_preimage_of_blt_subset hB'B'' hB''B hB₀P)
        (by
          simpa [lowerBltConstant, max_natCastImage_card_eq_of_cards hAcard hBcard] using
            hA'card)
        (by
          simpa [lowerBltConstant, max_natCastImage_card_eq_of_cards hAcard hBcard] using
            hB'card)
    · exact properGAP_dim_pos_of_large_preimage hγ_pos hγ_le
        (one_le_sumset_card_coefficient_of_threshold_pair_sumset hγ_pos hn hδ_lower hδ_upper
          hAcard hBcard hAB)
        hn hδ_lower hδ_upper
        (zmodModelEmbedding_iso (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) hA₀P
        (bltLargePreimage_large_of_blt hAcard hA''A hA''card)
    · exact (first_lower_for_bltLargePreimage hγ_pos hγ_le
        (one_le_sumset_card_coefficient_of_threshold_pair_sumset hγ_pos hn hδ_lower hδ_upper
          hAcard hBcard hAB)
        hn hδ_lower hδ_upper
        (zmodModelEmbedding_iso (γ := γ) (C := C) (n := n) hγ_pos C_pos hn)
        hAint hBint hA''A hB''B rfl
        (pairCardThreshold_pos_of_lower_density hγ_pos hn hδ_lower hδ_upper)
        (bltLargePreimage_large_of_blt hAcard hA''A hA''card)
        (bltLargePreimage_large_of_blt hBcard hB''B hB''card) hPdim hdim_bound).trans
        (first_term_le_blt_pair_sum
          (first_term_le_two_mul_large_card hγ_pos hγ_le C_pos
            (blt_large_sum_card_le hA''A hB''B hAB)
            (by simpa [natCastImage_card A, hAcard] using hA''card))
          (first_term_le_two_mul_right_large_card hγ_pos hγ_le C_pos
            (blt_large_sum_card_le hA''A hB''B hAB)
            (by simpa [natCastImage_card B, hBcard] using hB''card))
          hsum)
  exact natCastImage_add_subset
    (by intro x hx; exact hA''A (hA'A'' hx))
    (by intro x hx; exact hB''B (hB'B'' hx))
    hAB_subset


end

end DenseSetsWithoutLargeSumsets
