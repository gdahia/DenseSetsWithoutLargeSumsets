/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.ZModModel
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.FreimanDimension
import DenseSetsWithoutLargeSumsets.Probability
import DenseSetsWithoutLargeSumsets.Common
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.GeneralizedArithmeticProgression
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.LargeSumsetsFromMediumSizedSubsets.MediumSizedSubsets
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.Chang.Reduction
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.NumberTheory.Bertrand

/-!
Existence of a proper GAP containing two large subsets.

Given a pair `A, B` with small sumset and large subsets `A₀ ⊆ A`, `B₀ ⊆ B`, produces (via
Chang's theorem in the `ZMod q` model) a proper GAP of bounded dimension and carrier size whose
preimage contains `A₀` and `B₀` (`largeSubsets_exists_zmodGAPPreimageContainer`), and the
matching Freiman-dimension lower bound on the mixed sumset of `A₀` and `B₀`.
-/

namespace DenseSetsWithoutLargeSumsets

open Nat hiding div_pos
open scoped Pointwise

noncomputable section

lemma one_le_sumset_card_coefficient_of_threshold_pair_sumset
    {G : Type*} [DecidableEq G] [Add G]
    [IsRightCancelAdd G] {γ C : ℝ} {n : ℕ} {δ : unitInterval} {A B : Finset G}
    (hγ_pos : 0 < γ) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hAcard : A.card = pairCardThreshold (2 + γ) n δ)
    (hBcard : B.card = pairCardThreshold (2 + γ) n δ)
    (hAB : (A + B).card ≤ C * pairCardThreshold (2 + γ) n δ) :
    1 ≤ C := by
  exact one_le_sumset_card_coefficient_of_small_pair_sumset
    (pairCardThreshold_pos_of_lower_density hγ_pos hn hδ_lower hδ_upper) hAcard hBcard hAB

private lemma freiman_image_card_eq_of_subset {q n : ℕ} {ψ : ℕ → ZMod q}
    {S : Finset ℕ}
    (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ)
    (hS : S ⊆ interval n) :
    (S.image ψ).card = S.card := by
  rw [Finset.card_image_of_injOn (hψ.bijOn.injOn.mono (by
    intro x hx
    exact hS hx))]

private lemma half_threshold_le_image_union_card {γ : ℝ} {q n k : ℕ}
    {ψ : ℕ → ZMod q} {A A₀ B₀ : Finset ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1)
    (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ)
    (hAint : A ⊆ interval n) (hA₀A : A₀ ⊆ A)
    (hA₀large : (1 - ε γ) * (k : ℝ) ≤ (A₀.card : ℝ)) :
    (k : ℝ) / 2 ≤ ((A₀.image ψ ∪ B₀.image ψ).card : ℝ) := by
  apply (by
    nlinarith [half_le_one_sub_ε hγ_pos hγ_le, hA₀large,
      (by positivity : 0 ≤ (k : ℝ))] :
    (k : ℝ) / 2 ≤ (A₀.card : ℝ)).trans
  exact_mod_cast (by
    rw [← freiman_image_card_eq_of_subset hψ (hA₀A.trans hAint)]
    exact Finset.card_le_card Finset.subset_union_left :
    A₀.card ≤ (A₀.image ψ ∪ B₀.image ψ).card)

private lemma image_union_card_le_two_mul_threshold {q n k : ℕ}
    {ψ : ℕ → ZMod q} {A B A₀ B₀ : Finset ℕ}
    (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ)
    (hAint : A ⊆ interval n) (hBint : B ⊆ interval n)
    (hAcard : A.card = k) (hBcard : B.card = k)
    (hA₀A : A₀ ⊆ A) (hB₀B : B₀ ⊆ B) :
    (A₀.image ψ ∪ B₀.image ψ).card ≤ 2 * k := by
  apply (Finset.card_union_le (A₀.image ψ) (B₀.image ψ)).trans
  rw [freiman_image_card_eq_of_subset hψ (hA₀A.trans hAint),
    freiman_image_card_eq_of_subset hψ (hB₀B.trans hBint)]
  apply (Nat.add_le_add (Finset.card_le_card hA₀A) (Finset.card_le_card hB₀B)).trans
  rw [hAcard, hBcard]
  omega

private lemma image_union_card_le_density_coeff_log {γ C c : ℝ} {n q : ℕ}
    {δ : unitInterval} {ψ : ℕ → ZMod q} {A B A₀ B₀ : Finset ℕ}
    (hγ_pos : 0 < γ) (hc_pos : 0 < c) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ))
    (hδ_upper : (δ : ℝ) ≤ 1 - c)
    (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ)
    (hAint : A ⊆ interval n) (hBint : B ⊆ interval n)
    (hAcard : A.card = pairCardThreshold (2 + γ) n δ)
    (hBcard : B.card = pairCardThreshold (2 + γ) n δ)
    (hA₀A : A₀ ⊆ A) (hB₀B : B₀ ⊆ B) :
    ((A₀.image ψ ∪ B₀.image ψ).card : ℝ) ≤
      2 * densityCoefficient (2 + γ) c * Real.log (n : ℝ) := by
  apply (by
    exact_mod_cast image_union_card_le_two_mul_threshold hψ hAint hBint hAcard hBcard hA₀A
      hB₀B :
    ((A₀.image ψ ∪ B₀.image ψ).card : ℝ) ≤
      ((2 * pairCardThreshold (2 + γ) n δ : ℕ) : ℝ)).trans
  rw [Nat.cast_mul]
  norm_num only [Nat.cast_ofNat]
  convert mul_le_mul_of_nonneg_left
    (pairCardThreshold_le_density_log_of_lower_density hγ_pos hc_pos hn hδ_lower hδ_upper)
    (by norm_num : (0 : ℝ) ≤ 2) using 1
  all_goals ring

private lemma image_union_card_lt_exp_neg_mul_q {γ C c : ℝ} {n q : ℕ}
    {δ : unitInterval} {ψ : ℕ → ZMod q} {A B A₀ B₀ : Finset ℕ}
    (hγ_pos : 0 < γ) (hc_pos : 0 < c) (hc_lt : c < 1)
    (hn : lowerGapThreshold C γ c < n) (hq_lower : 2 * n ≤ q)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ))
    (hδ_upper : (δ : ℝ) ≤ 1 - c)
    (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ)
    (hAint : A ⊆ interval n) (hBint : B ⊆ interval n)
    (hAcard : A.card = pairCardThreshold (2 + γ) n δ)
    (hBcard : B.card = pairCardThreshold (2 + γ) n δ)
    (hA₀A : A₀ ⊆ A) (hB₀B : B₀ ⊆ B) :
    ((A₀.image ψ ∪ B₀.image ψ).card : ℝ) < Real.exp (-(changExponent C)) * q := by
  exact (image_union_card_le_density_coeff_log hγ_pos hc_pos
    ((lowerSizeThreshold_le_lowerGapThreshold C γ c).trans_lt hn) hδ_lower hδ_upper hψ hAint
    hBint hAcard hBcard hA₀A hB₀B).trans_lt
    (density_coeff_log_lt_exp_neg_mul_q hγ_pos hc_pos hc_lt hn hq_lower)

private lemma image_union_card_lt_chang_exp_mul_q {γ C c : ℝ} {n q : ℕ}
    {δ : unitInterval} {ψ : ℕ → ZMod q} {A B A₀ B₀ : Finset ℕ}
    (hγ_pos : 0 < γ) (hc_pos : 0 < c) (hc_lt : c < 1)
    (hn : lowerGapThreshold C γ c < n) (hq_lower : 2 * n ≤ q)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ))
    (hδ_upper : (δ : ℝ) ≤ 1 - c)
    (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ)
    (hAint : A ⊆ interval n) (hBint : B ⊆ interval n)
    (hAcard : A.card = pairCardThreshold (2 + γ) n δ)
    (hBcard : B.card = pairCardThreshold (2 + γ) n δ)
    (hA₀A : A₀ ⊆ A) (hB₀B : B₀ ⊆ B) :
    ((A₀.image ψ ∪ B₀.image ψ).card : ℝ) <
      Real.exp (-changTheoremExponent (κ C)) * q := by
  simpa [changExponent, neg_mul, mul_assoc] using
    image_union_card_lt_exp_neg_mul_q hγ_pos hc_pos hc_lt hn hq_lower hδ_lower hδ_upper hψ
      hAint hBint hAcard hBcard hA₀A hB₀B

private lemma image_union_add_union_le_κ_mul_card {γ C : ℝ} {n q k : ℕ}
    {ψ : ℕ → ZMod q} {A B A₀ B₀ : Finset ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C)
    (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ)
    (hAint : A ⊆ interval n) (hBint : B ⊆ interval n)
    (hAcard : A.card = k) (hBcard : B.card = k)
    (hA₀A : A₀ ⊆ A) (hB₀B : B₀ ⊆ B)
    (hA₀large : (1 - ε γ) * (k : ℝ) ≤ (A₀.card : ℝ))
    (hAB : (A + B).card ≤ C * k) :
    (((A₀.image ψ ∪ B₀.image ψ) + (A₀.image ψ ∪ B₀.image ψ)).card : ℝ) ≤
      κ C * ((A₀.image ψ ∪ B₀.image ψ).card : ℝ) := by
  apply card_large_subset_union_add_union_le_κ_mul_card
  · exact Finset.image_mono ψ hA₀A
  · exact Finset.image_mono ψ hB₀B
  · rw [freiman_image_card_eq_of_subset hψ hAint, hAcard]
  · rw [freiman_image_card_eq_of_subset hψ hBint, hBcard]
  · rw [freiman_image_sum_card hψ hAint hBint]
    exact hAB
  · exact half_threshold_le_image_union_card hγ_pos hγ_le hψ hAint hA₀A hA₀large
  · exact hC_one

private lemma chang_threshold_lt_image_union_card {γ C : ℝ} {n q : ℕ}
    {δ : unitInterval} {ψ : ℕ → ZMod q} {A A₀ B₀ : Finset ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ)
    (hAint : A ⊆ interval n) (hA₀A : A₀ ⊆ A)
    (hA₀large : (1 - ε γ) * (pairCardThreshold (2 + γ) n δ : ℝ) ≤ (A₀.card : ℝ)) :
    Real.exp (changContainerExponent (κ C)) <
      ((A₀.image ψ ∪ B₀.image ψ).card : ℝ) := by
  nlinarith [two_mul_chang_size_threshold_lt_pairCardThreshold hγ_pos hC_one
    (one_lt_nat_of_lowerSizeThreshold_lt hn) hδ_lower hδ_upper,
    half_threshold_le_image_union_card (B₀ := B₀) hγ_pos hγ_le hψ hAint hA₀A hA₀large]

private lemma image_union_freimanDim_le_two_ceil_κ_sub_one {γ C : ℝ}
    {n q k : ℕ} {ψ : ℕ → ZMod q} {A B A₀ B₀ : Finset ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C)
    (hq : Nat.Prime q) (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ)
    (hAint : A ⊆ interval n) (hBint : B ⊆ interval n)
    (hAcard : A.card = k) (hBcard : B.card = k)
    (hA₀A : A₀ ⊆ A) (hB₀B : B₀ ⊆ B)
    (hA₀large : (1 - ε γ) * (k : ℝ) ≤ (A₀.card : ℝ))
    (hAB : (A + B).card ≤ C * k) :
    freimanDim (A₀.image ψ ∪ B₀.image ψ) ≤ 2 * ⌈κ C⌉₊ - 1 := by
  apply freimanDim_le_two_mul_sub_one_of_card_add_le (A₀.image ψ ∪ B₀.image ψ) hq
  exact_mod_cast
    ((image_union_add_union_le_κ_mul_card hγ_pos hγ_le hC_one hψ hAint hBint
      hAcard hBcard hA₀A hB₀B hA₀large hAB).trans
      (mul_le_mul_of_nonneg_right (Nat.le_ceil (κ C)) (by positivity)) :
    (((A₀.image ψ ∪ B₀.image ψ) + (A₀.image ψ ∪ B₀.image ψ)).card : ℝ) ≤
      (⌈κ C⌉₊ : ℝ) * ((A₀.image ψ ∪ B₀.image ψ).card : ℝ))

private lemma chang_carrier_card_le_ceil_of_card_le {C : ℝ} {q k : ℕ}
    {X : Finset (ZMod q)} {P : ProperGAP (ZMod q)}
    (hXcard : X.card ≤ 2 * k)
    (hPcard : (P.carrier.card : ℝ) ≤ changCarrierBound X.card (κ C)) :
    P.carrier.card ≤ ⌈changCarrierBound (2 * k) (κ C)⌉₊ := by
  exact_mod_cast ((hPcard.trans
    ((by
      unfold changCarrierBound
      gcongr) :
      changCarrierBound X.card (κ C) ≤ changCarrierBound (2 * k) (κ C))).trans
    (Nat.le_ceil (changCarrierBound (2 * k) (κ C))))

private lemma large_subset_nonempty_of_card_lower {γ : ℝ} {S : Finset ℕ} {k : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hkpos : 0 < k)
    (hSlarge : (1 - ε γ) * (k : ℝ) ≤ (S.card : ℝ)) :
    S.Nonempty := by
  apply Finset.card_pos.mp
  exact_mod_cast (by
    nlinarith [half_le_one_sub_ε hγ_pos hγ_le,
      (by exact_mod_cast hkpos : (0 : ℝ) < k), hSlarge] :
    (0 : ℝ) < S.card)

private lemma freiman_image_nonempty_of_card_lower {γ : ℝ} {q n : ℕ}
    {ψ : ℕ → ZMod q} {S : Finset ℕ} {k : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1)
    (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ)
    (hS : S ⊆ interval n) (hkpos : 0 < k)
    (hSlarge : (1 - ε γ) * (k : ℝ) ≤ (S.card : ℝ)) :
    (S.image ψ).Nonempty := by
  apply Finset.card_pos.mp
  rw [freiman_image_card_eq_of_subset hψ hS]
  exact Finset.card_pos.mpr (large_subset_nonempty_of_card_lower hγ_pos hγ_le hkpos hSlarge)

private lemma freimanDim_image_union_le_ε_mul_threshold {γ C : ℝ} {n q : ℕ}
    {δ : unitInterval} {ψ : ℕ → ZMod q} {A₀ B₀ : Finset ℕ} {k : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn_one : 1 < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hkdef : k = pairCardThreshold (2 + γ) n δ)
    (hdim_bound : freimanDim (A₀.image ψ ∪ B₀.image ψ) ≤ 2 * ⌈κ C⌉₊ - 1) :
    (freimanDim (A₀.image ψ ∪ B₀.image ψ) : ℝ) ≤ ε γ * (k : ℝ) := by
  rw [hkdef]
  apply (by exact_mod_cast hdim_bound :
    (freimanDim (A₀.image ψ ∪ B₀.image ψ) : ℝ) ≤
      ((2 * ⌈κ C⌉₊ - 1 : ℕ) : ℝ)).trans
  exact two_mul_ceil_κ_sub_one_le_ε_mul_pairCardThreshold hγ_pos hγ_le hC_one hn_one
    hδ_lower hδ_upper

private lemma large_subsets_image_sum_lower {γ C : ℝ} {n q : ℕ}
    {δ : unitInterval} {ψ : ℕ → ZMod q} {A₀ B₀ : Finset ℕ} {k : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn_one : 1 < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ)
    (hA₀int : A₀ ⊆ interval n) (hB₀int : B₀ ⊆ interval n)
    (hkdef : k = pairCardThreshold (2 + γ) n δ) (hkpos : 0 < k)
    (hA₀large : (1 - ε γ) * (k : ℝ) ≤ (A₀.card : ℝ))
    (hB₀large : (1 - ε γ) * (k : ℝ) ≤ (B₀.card : ℝ))
    (hdim_bound : freimanDim (A₀.image ψ ∪ B₀.image ψ) ≤ 2 * ⌈κ C⌉₊ - 1) :
    (1 - 2 * ε γ) * (freimanDim (A₀.image ψ ∪ B₀.image ψ) : ℝ) * (k : ℝ) ≤
      ((A₀.image ψ + B₀.image ψ).card : ℝ) := by
  by_cases hr0 : freimanDim (A₀.image ψ ∪ B₀.image ψ) = 0
  · simp [hr0]
  · by_cases hBA : (B₀.image ψ).card ≤ (A₀.image ψ).card
    · exact asym_large_subsets_sum_lower (G := ZMod q) (A := A₀.image ψ)
        (B := B₀.image ψ) (r := freimanDim (A₀.image ψ ∪ B₀.image ψ))
        (k := k) (ε := ε γ) (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hr0))
        (freiman_image_nonempty_of_card_lower hγ_pos hγ_le hψ hA₀int hkpos hA₀large)
        (freiman_image_nonempty_of_card_lower hγ_pos hγ_le hψ hB₀int hkpos hB₀large)
        hBA rfl (ε_pos hγ_pos).le (le_of_lt (ε_lt_one_half hγ_pos hγ_le))
        (freimanDim_image_union_le_ε_mul_threshold hγ_pos hγ_le hC_one hn_one
          hδ_lower hδ_upper hkdef hdim_bound)
        (by simpa [freiman_image_card_eq_of_subset hψ hA₀int] using hA₀large)
        (by simpa [freiman_image_card_eq_of_subset hψ hB₀int] using hB₀large)
    · simpa [add_comm] using
        asym_large_subsets_sum_lower (G := ZMod q) (A := B₀.image ψ)
          (B := A₀.image ψ) (r := freimanDim (A₀.image ψ ∪ B₀.image ψ))
          (k := k) (ε := ε γ) (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hr0))
          (freiman_image_nonempty_of_card_lower hγ_pos hγ_le hψ hB₀int hkpos hB₀large)
          (freiman_image_nonempty_of_card_lower hγ_pos hγ_le hψ hA₀int hkpos hA₀large)
          (le_of_not_ge hBA) (by simp [Finset.union_comm])
          (ε_pos hγ_pos).le (le_of_lt (ε_lt_one_half hγ_pos hγ_le))
          (freimanDim_image_union_le_ε_mul_threshold hγ_pos hγ_le hC_one hn_one
            hδ_lower hδ_upper hkdef hdim_bound)
          (by simpa [freiman_image_card_eq_of_subset hψ hB₀int] using hB₀large)
          (by simpa [freiman_image_card_eq_of_subset hψ hA₀int] using hA₀large)

lemma largeSubsets_exists_zmodGAPPreimageContainer {γ C c : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (C_pos : 0 < C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c) :
    ∀ {A B A₀ B₀ : Finset ℕ}, A ⊆ interval n → B ⊆ interval n →
      A.card = pairCardThreshold (2 + γ) n δ → B.card = pairCardThreshold (2 + γ) n δ →
      A₀ ⊆ A → B₀ ⊆ B →
      (1 - ε γ) * (pairCardThreshold (2 + γ) n δ : ℝ) ≤ (A₀.card : ℝ) →
      (1 - ε γ) * (pairCardThreshold (2 + γ) n δ : ℝ) ≤ (B₀.card : ℝ) →
      (A + B).card ≤ C * pairCardThreshold (2 + γ) n δ →
      ∃ P ∈ properGAPsZModUpToDim (pairCardThreshold (2 + γ) n δ)
          ⌈changCarrierBound (2 * pairCardThreshold (2 + γ) n δ) (κ C)⌉₊
          (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).pos,
        A₀ ⊆ zmodGAPPreimageContainer n
            (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) P ∧
          B₀ ⊆ zmodGAPPreimageContainer n
              (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) P ∧
            P.dim ≤ freimanDim
                (A₀.image (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) ∪
                  B₀.image (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn)) ∧
              freimanDim
                  (A₀.image (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) ∪
                    B₀.image (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn))
                ≤ 2 * ⌈κ C⌉₊ - 1 := by
  intro A B A₀ B₀ hAint hBint hAcard hBcard hA₀A hB₀B hA₀large hB₀large hAB
  obtain ⟨P, hXP, hPdim, hPcard⟩ :=
    exists_properGAP_of_small_sumset
      (A₀.image (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) ∪
        B₀.image (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn))
      (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn)
      (two_le_κ_of_one_le
        (one_le_sumset_card_coefficient_of_threshold_pair_sumset hγ_pos hn hδ_lower hδ_upper
          hAcard hBcard hAB))
      (image_union_add_union_le_κ_mul_card hγ_pos hγ_le
        (one_le_sumset_card_coefficient_of_threshold_pair_sumset hγ_pos hn hδ_lower hδ_upper
          hAcard hBcard hAB)
        (zmodModelEmbedding_iso (γ := γ) (C := C) (n := n) hγ_pos C_pos hn)
        hAint hBint hAcard hBcard hA₀A hB₀B hA₀large hAB)
      (chang_threshold_lt_image_union_card (B₀ := B₀) hγ_pos hγ_le
        (one_le_sumset_card_coefficient_of_threshold_pair_sumset hγ_pos hn hδ_lower hδ_upper
          hAcard hBcard hAB)
        hn hδ_lower hδ_upper
        (zmodModelEmbedding_iso (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) hAint hA₀A
        hA₀large)
      (image_union_card_lt_chang_exp_mul_q hγ_pos hc_pos hc_lt hn_gap
        (zmodModelQ_lower (γ := γ) (C := C) (n := n) hγ_pos C_pos hn)
        hδ_lower hδ_upper_c
        (zmodModelEmbedding_iso (γ := γ) (C := C) (n := n) hγ_pos C_pos hn)
        hAint hBint hAcard hBcard hA₀A hB₀B)
  refine ⟨P, ?_, ?_, ?_, hPdim, ?_⟩
  · apply (mem_properGAPsZModUpToDim
      (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).pos).2
    constructor
    · exact (hPdim.trans
        (image_union_freimanDim_le_two_ceil_κ_sub_one hγ_pos hγ_le
          (one_le_sumset_card_coefficient_of_threshold_pair_sumset hγ_pos hn hδ_lower hδ_upper
            hAcard hBcard hAB)
          (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn)
          (zmodModelEmbedding_iso (γ := γ) (C := C) (n := n) hγ_pos C_pos hn)
          hAint hBint hAcard hBcard hA₀A hB₀B hA₀large hAB)).trans
        (two_mul_ceil_κ_sub_one_le_pairCardThreshold hγ_pos
          (one_le_sumset_card_coefficient_of_threshold_pair_sumset hγ_pos hn hδ_lower hδ_upper
            hAcard hBcard hAB)
          (one_lt_nat_of_lowerSizeThreshold_lt hn) hδ_lower hδ_upper)
    · apply chang_carrier_card_le_ceil_of_card_le
      · exact image_union_card_le_two_mul_threshold
          (zmodModelEmbedding_iso (γ := γ) (C := C) (n := n) hγ_pos C_pos hn)
          hAint hBint hAcard hBcard hA₀A hB₀B
      · exact hPcard
  · intro a ha
    rw [zmodGAPPreimageContainer, Finset.mem_filter]
    constructor
    · exact hA₀A.trans hAint ha
    apply hXP
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.2 ⟨a, ha, rfl⟩))
  · intro b hb
    rw [zmodGAPPreimageContainer, Finset.mem_filter]
    constructor
    · exact hB₀B.trans hBint hb
    apply hXP
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.2 ⟨b, hb, rfl⟩))
  · exact image_union_freimanDim_le_two_ceil_κ_sub_one hγ_pos hγ_le
      (one_le_sumset_card_coefficient_of_threshold_pair_sumset hγ_pos hn hδ_lower hδ_upper
        hAcard hBcard hAB)
      (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn)
      (zmodModelEmbedding_iso (γ := γ) (C := C) (n := n) hγ_pos C_pos hn)
      hAint hBint hAcard hBcard hA₀A hB₀B hA₀large hAB

lemma large_subsets_first_term_lower_by_dim {γ C : ℝ} {n q : ℕ}
    {δ : unitInterval} {ψ : ℕ → ZMod q} {A₀ B₀ : Finset ℕ} {D k : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn_one : 1 < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ)
    (hA₀int : A₀ ⊆ interval n) (hB₀int : B₀ ⊆ interval n)
    (hkdef : k = pairCardThreshold (2 + γ) n δ) (hkpos : 0 < k)
    (hA₀large : (1 - ε γ) * (k : ℝ) ≤ (A₀.card : ℝ))
    (hB₀large : (1 - ε γ) * (k : ℝ) ≤ (B₀.card : ℝ))
    (hDdim : D ≤ freimanDim (A₀.image ψ ∪ B₀.image ψ))
    (hdim_bound : freimanDim (A₀.image ψ ∪ B₀.image ψ) ≤ 2 * ⌈κ C⌉₊ - 1) :
    (1 - 3 * ε γ) * (D : ℝ) * (k : ℝ) ≤
      (1 - ε γ) * ((natCastImage A₀ + natCastImage B₀).card : ℝ) := by
  apply le_trans (b :=
      (1 - ε γ) *
        ((1 - 2 * ε γ) * (freimanDim (A₀.image ψ ∪ B₀.image ψ) : ℝ) * (k : ℝ)))
  · refine le_trans (b :=
        (1 - 3 * ε γ) * (freimanDim (A₀.image ψ ∪ B₀.image ψ) : ℝ) * (k : ℝ)) ?_ ?_
    · gcongr
      · exact (one_sub_three_mul_ε_pos hγ_pos hγ_le).le
    · ring_nf
      nlinarith [mul_nonneg (sq_nonneg (ε γ))
        (mul_nonneg
          (Nat.cast_nonneg (freimanDim (A₀.image ψ ∪ B₀.image ψ)) :
            (0 : ℝ) ≤ freimanDim (A₀.image ψ ∪ B₀.image ψ))
          (Nat.cast_nonneg k : (0 : ℝ) ≤ k))]
  apply (mul_le_mul_of_nonneg_left
    (large_subsets_image_sum_lower hγ_pos hγ_le hC_one hn_one hδ_lower hδ_upper hψ
      hA₀int hB₀int hkdef hkpos hA₀large hB₀large hdim_bound)
    (by
      exact (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (half_le_one_sub_ε hγ_pos hγ_le))).trans_eq
  rw [freiman_image_sum_card hψ hA₀int hB₀int, natCastImage_sum_card A₀ B₀]


end

end DenseSetsWithoutLargeSumsets
