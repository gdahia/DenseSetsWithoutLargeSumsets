/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.ZModModel
public import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.WitnessPairs
import SumOfSetsInSeveralDimensions.FreimanDimensionSumsetBounds
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.SumsetGrowth
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.ThresholdEstimates

/-!
# A progression that contains two large subsets

Let `A, B ⊆ [n]` have size `k = pairCardThreshold (3 + γ) n δ` and satisfy `|A + B| ≤ C * k`. Let
`A₀ ⊆ A` and `B₀ ⊆ B` have size at least `(1 - ε γ) * k`, and let `X` be the image of `A₀ ∪ B₀`
in `ZMod q`. Then `|X + X| ≤ κ C * |X|`. By Chang's theorem, `X` is contained in a proper
generalized arithmetic progression of dimension at most `freimanDim X` with at most
`changCarrierBound (2 * k) (κ C)` points. Also `freimanDim X ≤ 2 * ⌈κ C⌉₊ - 1`, and Ruzsa's bound
for sumsets in several dimensions gives `|A₀ + B₀| ≥ (1 - 2 * ε γ) * freimanDim X * k`.

## Main statements

* `largeSubsets_exists_zmodGAPPreimageContainer`: there is a proper progression `P` of dimension
  at most `freimanDim X` with at most `changCarrierBound (2 * k) (κ C)` points whose preimage in
  `[n]` contains `A₀` and `B₀`.
* `large_subsets_first_term_lower_by_dim`: if `D ≤ freimanDim X`, then
  `(1 - 3 * ε γ) * D * k ≤ (1 - ε γ) * |A₀ + B₀|`.
-/

@[expose] public section

namespace DenseSetsWithoutLargeSumsets

open Finset ChangFreimanRuzsa LargeSumsetsFromSubsets SumOfSetsInSeveralDimensions
open scoped Pointwise

noncomputable section

lemma one_le_sumset_card_coefficient_of_threshold_pair_sumset
    {G : Type*} [DecidableEq G] [Add G]
    [IsRightCancelAdd G] {γ C : ℝ} {n : ℕ} {δ : unitInterval} {A B : Finset G}
    (hγ_pos : 0 < γ) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hAcard : #A = pairCardThreshold (3 + γ) n δ)
    (hBcard : #B = pairCardThreshold (3 + γ) n δ)
    (hAB : #(A + B) ≤ C * pairCardThreshold (3 + γ) n δ) :
    1 ≤ C :=
  one_le_sumset_card_coefficient_of_small_pair_sumset
    (pairCardThreshold_pos_of_lower_density hγ_pos hn hδ_lower hδ_upper) hAcard hBcard hAB

private lemma card_image_eq_of_subset_interval {q n : ℕ} {ψ : ℕ → ZMod q} {S : Finset ℕ}
    (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ) (hS : S ⊆ interval n) :
    #(S.image ψ) = #S :=
  card_image_of_injOn (hψ.bijOn.injOn.mono (coe_subset.2 hS))

private lemma half_le_card_image_union {γ : ℝ} {q n k : ℕ} {ψ : ℕ → ZMod q}
    {A₀ B₀ : Finset ℕ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1)
    (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ) (hA₀int : A₀ ⊆ interval n)
    (hA₀large : (1 - ε γ) * k ≤ #A₀) :
    (k : ℝ) / 2 ≤ #(A₀.image ψ ∪ B₀.image ψ) := by
  have h : #(A₀.image ψ) ≤ #(A₀.image ψ ∪ B₀.image ψ) := card_le_card subset_union_left
  rw [card_image_eq_of_subset_interval hψ hA₀int, ← Nat.cast_le (α := ℝ)] at h
  linarith [mul_le_mul_of_nonneg_right (half_le_one_sub_ε hγ_pos hγ_le)
    (Nat.cast_nonneg (α := ℝ) k)]

private lemma card_image_union_le_two_mul {q k : ℕ} {ψ : ℕ → ZMod q} {A B A₀ B₀ : Finset ℕ}
    (hAcard : #A = k) (hBcard : #B = k) (hA₀A : A₀ ⊆ A) (hB₀B : B₀ ⊆ B) :
    #(A₀.image ψ ∪ B₀.image ψ) ≤ 2 * k := by
  grind [card_union_le (A₀.image ψ) (B₀.image ψ), card_image_le (s := A₀) (f := ψ),
    card_image_le (s := B₀) (f := ψ), card_le_card hA₀A, card_le_card hB₀B]

private lemma exp_mul_card_image_union_le {γ C c : ℝ} {n q : ℕ} {δ : unitInterval}
    {ψ : ℕ → ZMod q} {A B A₀ B₀ : Finset ℕ} (hγ_pos : 0 < γ) (hc_pos : 0 < c) (hc_lt : c < 1)
    (hn : lowerGapThreshold C γ c < n) (hq_lower : 2 * n ≤ q)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) ≤ 1 - c)
    (hAcard : #A = pairCardThreshold (3 + γ) n δ) (hBcard : #B = pairCardThreshold (3 + γ) n δ)
    (hA₀A : A₀ ⊆ A) (hB₀B : B₀ ⊆ B) :
    Real.exp (changFreimanDimExponent (κ C)) * #(A₀.image ψ ∪ B₀.image ψ) ≤ q := by
  have hX : (#(A₀.image ψ ∪ B₀.image ψ) : ℝ) ≤ 2 * pairCardThreshold (3 + γ) n δ :=
    mod_cast card_image_union_le_two_mul hAcard hBcard hA₀A hB₀B
  have hq := density_coeff_log_lt_exp_neg_mul_q hγ_pos hc_pos hc_lt hn hq_lower
  rw [changExponent, Real.exp_neg, ← div_eq_inv_mul, lt_div_iff₀' (Real.exp_pos _)] at hq
  refine (mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)).trans hq.le
  linarith [pairCardThreshold_le_density_log_of_lower_density hγ_pos hc_pos
    ((lowerSizeThreshold_le_lowerGapThreshold C γ c).trans_lt hn) hδ_lower hδ_upper]

private lemma card_image_union_add_le_κ_mul {γ C : ℝ} {n q k : ℕ} {ψ : ℕ → ZMod q}
    {A B A₀ B₀ : Finset ℕ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C)
    (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ)
    (hAint : A ⊆ interval n) (hBint : B ⊆ interval n) (hAcard : #A = k) (hBcard : #B = k)
    (hA₀A : A₀ ⊆ A) (hB₀B : B₀ ⊆ B) (hA₀large : (1 - ε γ) * k ≤ #A₀) (hAB : #(A + B) ≤ C * k) :
    (#((A₀.image ψ ∪ B₀.image ψ) + (A₀.image ψ ∪ B₀.image ψ)) : ℝ) ≤
      κ C * #(A₀.image ψ ∪ B₀.image ψ) := by
  refine card_large_subset_union_add_union_le_κ_mul_card (image_subset_image hA₀A)
    (image_subset_image hB₀B) ((card_image_eq_of_subset_interval hψ hAint).trans hAcard)
    ((card_image_eq_of_subset_interval hψ hBint).trans hBcard) ?_
    (half_le_card_image_union hγ_pos hγ_le hψ (hA₀A.trans hAint) hA₀large) hC_one
  rwa [freiman_image_sum_card hψ hAint hBint]

private lemma exp_lt_card_image_union {γ C : ℝ} {n q : ℕ} {δ : unitInterval} {ψ : ℕ → ZMod q}
    {A₀ B₀ : Finset ℕ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C)
    (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ) (hA₀int : A₀ ⊆ interval n)
    (hA₀large : (1 - ε γ) * pairCardThreshold (3 + γ) n δ ≤ #A₀) :
    Real.exp (changContainerExponent (κ C)) < #(A₀.image ψ ∪ B₀.image ψ) := by
  linarith [two_mul_chang_size_threshold_lt_pairCardThreshold hγ_pos hC_one
    (one_lt_nat_of_lowerSizeThreshold_lt hn) hδ_lower hδ_upper,
    half_le_card_image_union (B₀ := B₀) hγ_pos hγ_le hψ hA₀int hA₀large]

private lemma freimanDim_le_two_mul_ceil_sub_one {q : ℕ} {K : ℝ} {X : Finset (ZMod q)}
    (hX : X.Nonempty) (hXX : (#(X + X) : ℝ) ≤ K * #X) : freimanDim X ≤ 2 * ⌈K⌉₊ - 1 := by
  refine Nat.le_sub_one_of_lt ((Nat.cast_lt (α := ℝ)).1 ?_)
  push_cast
  linarith [freimanDim_le_two_mul_sub_one_of_card_add_le hX hXX, Nat.le_ceil K]

private lemma card_carrier_le_ceil_changCarrierBound {C : ℝ} {q k : ℕ} {X : Finset (ZMod q)}
    {P : GAP (ZMod q)} (hXcard : #X ≤ 2 * k)
    (hPcard : (#P.carrier : ℝ) ≤ changCarrierBound #X (κ C)) :
    #P.carrier ≤ ⌈changCarrierBound (2 * k) (κ C)⌉₊ := by
  refine (Nat.cast_le (α := ℝ)).1 ((hPcard.trans ?_).trans (Nat.le_ceil _))
  unfold changCarrierBound
  gcongr

private lemma nonempty_of_one_sub_ε_mul_le_card {γ : ℝ} {S : Finset ℕ} {k : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hk : 0 < k) (hS : (1 - ε γ) * k ≤ #S) :
    S.Nonempty := by
  rw [← card_pos, ← Nat.cast_pos (α := ℝ)]
  exact (mul_pos (by linarith [half_le_one_sub_ε hγ_pos hγ_le]) (Nat.cast_pos.2 hk)).trans_le hS

private lemma one_sub_two_mul_ε_mul_freimanDim_mul_le_card_add {γ C : ℝ} {n q : ℕ}
    {δ : unitInterval} {ψ : ℕ → ZMod q} {A₀ B₀ : Finset ℕ} {k : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn_one : 1 < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ)
    (hA₀int : A₀ ⊆ interval n) (hB₀int : B₀ ⊆ interval n)
    (hkdef : k = pairCardThreshold (3 + γ) n δ) (hkpos : 0 < k)
    (hA₀large : (1 - ε γ) * k ≤ #A₀) (hB₀large : (1 - ε γ) * k ≤ #B₀)
    (hdim_bound : freimanDim (A₀.image ψ ∪ B₀.image ψ) ≤ 2 * ⌈κ C⌉₊ - 1) :
    (1 - 2 * ε γ) * freimanDim (A₀.image ψ ∪ B₀.image ψ) * k ≤ #(A₀.image ψ + B₀.image ψ) := by
  subst hkdef
  obtain hr | hr := Nat.eq_zero_or_pos (freimanDim (A₀.image ψ ∪ B₀.image ψ))
  · simp [hr]
  have hA := (nonempty_of_one_sub_ε_mul_le_card hγ_pos hγ_le hkpos hA₀large).image ψ
  have hB := (nonempty_of_one_sub_ε_mul_le_card hγ_pos hγ_le hkpos hB₀large).image ψ
  have hdim := ((Nat.cast_le (α := ℝ)).2 hdim_bound).trans
    (two_mul_ceil_κ_sub_one_le_ε_mul_pairCardThreshold hγ_pos hC_one hn_one hδ_lower hδ_upper)
  rw [← card_image_eq_of_subset_interval hψ hA₀int] at hA₀large
  rw [← card_image_eq_of_subset_interval hψ hB₀int] at hB₀large
  obtain hBA | hAB := le_total #(B₀.image ψ) #(A₀.image ψ)
  · exact asym_large_subsets_sum_lower hr hB hBA rfl hdim hA₀large hB₀large
  · rw [add_comm (A₀.image ψ)]
    exact asym_large_subsets_sum_lower hr hA hAB (by rw [union_comm]) hdim hB₀large hA₀large

/-- Let `A, B ⊆ [n]` have size `k = pairCardThreshold (3 + γ) n δ` and satisfy `|A + B| ≤ C * k`,
and let `A₀ ⊆ A`, `B₀ ⊆ B` have size at least `(1 - ε γ) * k`. Let `X` be the image of `A₀ ∪ B₀`
in `ZMod q`. Then there is a proper progression `P` of dimension at most
`min k (freimanDim X)` with at most `changCarrierBound (2 * k) (κ C)` points whose preimage in
`[n]` contains `A₀` and `B₀`. Moreover `freimanDim X ≤ 2 * ⌈κ C⌉₊ - 1`. -/
theorem largeSubsets_exists_zmodGAPPreimageContainer {γ C c : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (C_pos : 0 < C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c) :
    ∀ {A B A₀ B₀ : Finset ℕ}, A ⊆ interval n → B ⊆ interval n →
      #A = pairCardThreshold (3 + γ) n δ → #B = pairCardThreshold (3 + γ) n δ →
      A₀ ⊆ A → B₀ ⊆ B →
      (1 - ε γ) * (pairCardThreshold (3 + γ) n δ : ℝ) ≤ (#A₀ : ℝ) →
      (1 - ε γ) * (pairCardThreshold (3 + γ) n δ : ℝ) ≤ (#B₀ : ℝ) →
      #(A + B) ≤ C * pairCardThreshold (3 + γ) n δ →
      ∃ P ∈ properGAPsZModUpToDim (pairCardThreshold (3 + γ) n δ)
          ⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊
          (zmodModelQ_prime hγ_pos C_pos hn).pos,
        A₀ ⊆ zmodGAPPreimageContainer n (zmodModelEmbedding hγ_pos C_pos hn) P ∧
          B₀ ⊆ zmodGAPPreimageContainer n (zmodModelEmbedding hγ_pos C_pos hn) P ∧
            P.dim ≤ freimanDim
                (A₀.image (zmodModelEmbedding hγ_pos C_pos hn) ∪
                  B₀.image (zmodModelEmbedding hγ_pos C_pos hn)) ∧
              freimanDim
                  (A₀.image (zmodModelEmbedding hγ_pos C_pos hn) ∪
                    B₀.image (zmodModelEmbedding hγ_pos C_pos hn))
                ≤ 2 * ⌈κ C⌉₊ - 1 := by
  intro A B A₀ B₀ hAint hBint hAcard hBcard hA₀A hB₀B hA₀large _ hAB
  have hC := one_le_sumset_card_coefficient_of_threshold_pair_sumset hγ_pos hn hδ_lower hδ_upper
    hAcard hBcard hAB
  have hq := zmodModelQ_prime hγ_pos C_pos hn
  have hψ := zmodModelEmbedding_iso hγ_pos C_pos hn
  have hXX := card_image_union_add_le_κ_mul hγ_pos hγ_le hC hψ hAint hBint hAcard hBcard hA₀A
    hB₀B hA₀large hAB
  have hXlower := exp_lt_card_image_union (B₀ := B₀) hγ_pos hγ_le hC hn hδ_lower hδ_upper hψ
    (hA₀A.trans hAint) hA₀large
  have hXupper := exp_mul_card_image_union_le (ψ := zmodModelEmbedding hγ_pos C_pos hn) hγ_pos
    hc_pos hc_lt hn_gap (zmodModelQ_lower hγ_pos C_pos hn) hδ_lower hδ_upper_c hAcard hBcard
    hA₀A hB₀B
  obtain ⟨P, hP, hXP, -, hPdim, hPcard⟩ :=
    exists_twoProperGAP_zmod_dim_le_freimanDim _ hq (two_le_κ_of_one_le hC) hXX hXlower hXupper
  have hdim := freimanDim_le_two_mul_ceil_sub_one
    (card_pos.1 (mod_cast (Real.exp_pos _).trans hXlower)) hXX
  refine ⟨P, (mem_properGAPsZModUpToDim hq.pos).2 ⟨P.twoProper_proper hP, ?_, ?_⟩,
    ?_, ?_, hPdim, hdim⟩
  · exact (hPdim.trans hdim).trans (two_mul_ceil_κ_sub_one_le_pairCardThreshold hγ_pos hC
      (one_lt_nat_of_lowerSizeThreshold_lt hn) hδ_lower hδ_upper)
  · exact card_carrier_le_ceil_changCarrierBound
      (card_image_union_le_two_mul hAcard hBcard hA₀A hB₀B) hPcard
  · intro a ha
    exact mem_filter.2 ⟨hA₀A.trans hAint ha, hXP (mem_union_left _ (mem_image_of_mem _ ha))⟩
  · intro b hb
    exact mem_filter.2 ⟨hB₀B.trans hBint hb, hXP (mem_union_right _ (mem_image_of_mem _ hb))⟩

private lemma one_sub_three_mul_mul_mul_le {e D r k N : ℝ} (he : e ≤ 1 / 3) (hD : D ≤ r)
    (hr : 0 ≤ r) (hk : 0 ≤ k) (h : (1 - 2 * e) * r * k ≤ N) :
    (1 - 3 * e) * D * k ≤ (1 - e) * N := by
  nlinarith [mul_le_mul_of_nonneg_left h (by linarith : 0 ≤ 1 - e),
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD (by linarith : 0 ≤ 1 - 3 * e)) hk,
    mul_nonneg (mul_nonneg (sq_nonneg e) hr) hk]

/-- Let `A₀, B₀ ⊆ [n]` have size at least `(1 - ε γ) * k`, where
`k = pairCardThreshold (3 + γ) n δ`, and let `X` be the image of `A₀ ∪ B₀` in `ZMod q`. If
`D ≤ freimanDim X ≤ 2 * ⌈κ C⌉₊ - 1`, then `(1 - 3 * ε γ) * D * k ≤ (1 - ε γ) * |A₀ + B₀|`. -/
lemma large_subsets_first_term_lower_by_dim {γ C : ℝ} {n q : ℕ}
    {δ : unitInterval} {ψ : ℕ → ZMod q} {A₀ B₀ : Finset ℕ} {D k : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn_one : 1 < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ)
    (hA₀int : A₀ ⊆ interval n) (hB₀int : B₀ ⊆ interval n)
    (hkdef : k = pairCardThreshold (3 + γ) n δ) (hkpos : 0 < k)
    (hA₀large : (1 - ε γ) * (k : ℝ) ≤ (#A₀ : ℝ))
    (hB₀large : (1 - ε γ) * (k : ℝ) ≤ (#B₀ : ℝ))
    (hDdim : D ≤ freimanDim (A₀.image ψ ∪ B₀.image ψ))
    (hdim_bound : freimanDim (A₀.image ψ ∪ B₀.image ψ) ≤ 2 * ⌈κ C⌉₊ - 1) :
    (1 - 3 * ε γ) * (D : ℝ) * (k : ℝ) ≤
      (1 - ε γ) * (#(natCastImage A₀ + natCastImage B₀) : ℝ) := by
  have h := one_sub_two_mul_ε_mul_freimanDim_mul_le_card_add hγ_pos hγ_le hC_one hn_one hδ_lower
    hδ_upper hψ hA₀int hB₀int hkdef hkpos hA₀large hB₀large hdim_bound
  rw [freiman_image_sum_card hψ hA₀int hB₀int, ← natCastImage_sum_card] at h
  exact one_sub_three_mul_mul_mul_le (by linarith [ε_le_one_twelfth hγ_pos hγ_le])
    (mod_cast hDdim) (Nat.cast_nonneg _) (Nat.cast_nonneg _) h

end

end DenseSetsWithoutLargeSumsets
