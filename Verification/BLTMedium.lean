/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import Verification.ExtraAxioms

/-!
The symmetric medium-sized-subset consequence of the original Bollobás--Leader--Tiba theorem.
-/

namespace Verification

open scoped BigOperators Pointwise

noncomputable section

/-- An inflated BLT constant convenient for the symmetric square-root corollary. -/
def bltConstant (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) : ℝ :=
  8 * (max 1 (originalBltConstant σ ε hσ hε) + σ + 1) ^ 2

private def bltSampleSize (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) (M : ℕ) : ℕ :=
  ⌈Real.sqrt (max 1 (originalBltConstant σ ε hσ hε) * M)⌉₊ + 1

lemma one_le_bltConstant {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    1 ≤ bltConstant σ ε hσ hε := by
  unfold bltConstant
  nlinarith [le_max_left (1 : ℝ) (originalBltConstant σ ε hσ hε)]

private lemma bltSample_subset {G : Type*} [DecidableEq G] (A : Finset G) {r : ℕ}
    (a : Fin r → ↥A) : bltSample A a ⊆ A := by
  intro x hx
  rw [bltSample, Finset.mem_image] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact (a i).property

private lemma bltSample_card_le {G : Type*} [DecidableEq G] (A : Finset G) {r : ℕ}
    (a : Fin r → ↥A) : (bltSample A a).card ≤ r := by
  refine Finset.card_image_le.trans ?_
  simp

private lemma exists_blt_sample_deterministic {G : Type*} [DecidableEq G] [AddCommGroup G]
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) {A B : Finset G} (hA : A.Nonempty)
    (hB : B.Nonempty) (c₁ c₂ : ℕ) (hc₁pos : 1 ≤ c₁) (hc₁A : c₁ ≤ A.card)
    (hc₂pos : 1 ≤ c₂) (hc₂B : c₂ ≤ B.card)
    (hcprod : originalBltConstant σ ε hσ hε * (max A.card B.card : ℝ) < c₁ * c₂) :
    ∃ A' A₀ B' B₀ : Finset G, A' ⊆ A₀ ∧ A₀ ⊆ A ∧ B' ⊆ B₀ ∧ B₀ ⊆ B ∧
      (1 - ε) * (A.card : ℝ) ≤ (A₀.card : ℝ) ∧
      (1 - ε) * (B.card : ℝ) ≤ (B₀.card : ℝ) ∧ A'.card ≤ c₁ ∧ B'.card ≤ c₂ ∧
      min (min ((1 - ε) * ((A₀ + B₀).card : ℝ)) (σ * (A₀.card : ℝ)))
          (σ * (B₀.card : ℝ)) ≤ ((A' + B').card : ℝ) := by
  obtain ⟨A₀, B₀, hA₀, hB₀, hA₀A, hB₀B, hA₀card, hB₀card, hexpect⟩ :=
    exists_blt_sample hσ hε hA hB c₁ c₂ hc₁pos hc₁A hc₂pos hc₂B hcprod
  letI : Nonempty ↥A₀ := hA₀.to_subtype
  letI : Nonempty ↥B₀ := hB₀.to_subtype
  obtain ⟨⟨a, b⟩, _, hab⟩ := Finset.exists_lt_of_lt_expect Finset.univ_nonempty hexpect
  exact ⟨bltSample A₀ a, A₀, bltSample B₀ b, B₀,
    bltSample_subset A₀ a, hA₀A, bltSample_subset B₀ b, hB₀B,
    hA₀card.le, hB₀card.le, bltSample_card_le A₀ a, bltSample_card_le B₀ b, hab.le⟩

private lemma bltSampleSize_pos {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) (M : ℕ) :
    1 ≤ bltSampleSize σ ε hσ hε M := by
  simp [bltSampleSize]

private lemma bltSampleSize_product {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) (M : ℕ) :
    originalBltConstant σ ε hσ hε * (M : ℝ) <
      (bltSampleSize σ ε hσ hε M : ℝ) ^ 2 := by
  unfold bltSampleSize
  push_cast
  refine (mul_le_mul_of_nonneg_right
    (le_max_right (1 : ℝ) (originalBltConstant σ ε hσ hε)) ?_).trans_lt ?_
  · positivity
  · nth_rewrite 1 [← Real.sq_sqrt (mul_nonneg
      ((zero_le_one' ℝ).trans (le_max_left 1 (originalBltConstant σ ε hσ hε)))
      (by positivity))]
    nlinarith [Nat.le_ceil (Real.sqrt
      (max 1 (originalBltConstant σ ε hσ hε) * (M : ℝ))),
      Real.sqrt_nonneg (max 1 (originalBltConstant σ ε hσ hε) * (M : ℝ))]

private lemma bltSampleSize_le_base {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) {M : ℕ}
    (hM : 1 ≤ M) :
    (bltSampleSize σ ε hσ hε M : ℝ) ≤
      (max 1 (originalBltConstant σ ε hσ hε) + 2) * Real.sqrt (M : ℝ) := by
  unfold bltSampleSize
  push_cast
  rw [Real.sqrt_mul
    ((zero_le_one' ℝ).trans (le_max_left 1 (originalBltConstant σ ε hσ hε)))]
  refine le_trans (b := Real.sqrt (max 1 (originalBltConstant σ ε hσ hε)) *
    Real.sqrt (M : ℝ) + 2) ?_ ?_
  · nlinarith [Nat.ceil_lt_add_one (mul_nonneg
      (Real.sqrt_nonneg (max 1 (originalBltConstant σ ε hσ hε)))
      (Real.sqrt_nonneg (M : ℝ)))]
  · rw [add_mul]
    refine add_le_add (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)) ?_
    · rw [Real.sqrt_le_left
        ((zero_le_one' ℝ).trans (le_max_left 1 (originalBltConstant σ ε hσ hε)))]
      nlinarith [le_max_left (1 : ℝ) (originalBltConstant σ ε hσ hε)]
    · nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (M : ℝ)),
        Real.sqrt_nonneg (M : ℝ), (by exact_mod_cast hM : (1 : ℝ) ≤ M)]

private lemma bltSampleSize_le {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) {M : ℕ}
    (hM : 1 ≤ M) :
    (bltSampleSize σ ε hσ hε M : ℝ) ≤
      bltConstant σ ε hσ hε * Real.sqrt (M : ℝ) := by
  refine (bltSampleSize_le_base hσ hε hM).trans
    (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  unfold bltConstant
  nlinarith [le_max_left (1 : ℝ) (originalBltConstant σ ε hσ hε),
    sq_nonneg (max 1 (originalBltConstant σ ε hσ hε) + σ)]

private lemma blt_ceil_target_le {x K : ℝ} (hxK : x ≤ K) (hK : 0 ≤ K) :
    (⌈x⌉₊ : ℝ) ≤ K + 1 := by
  by_cases hx : 0 ≤ x
  · refine (Nat.ceil_lt_add_one hx).le.trans ?_
    linarith
  · rw [Nat.ceil_eq_zero.mpr (le_of_not_ge hx)]
    norm_num
    linarith

private lemma blt_small_bound {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) {N M : ℕ}
    (hM : 1 ≤ M) (hN : N < bltSampleSize σ ε hσ hε M) :
    σ * (N : ℝ) + 1 ≤ bltConstant σ ε hσ hε * Real.sqrt (M : ℝ) := by
  replace hN : (N : ℝ) < (bltSampleSize σ ε hσ hε M : ℝ) := by
    exact_mod_cast hN
  unfold bltConstant
  refine le_trans (b :=
    (σ * (max 1 (originalBltConstant σ ε hσ hε) + 2) + 1) * Real.sqrt (M : ℝ))
    ?_ (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  · refine le_trans (b := σ * (max 1 (originalBltConstant σ ε hσ hε) + 2) *
      Real.sqrt (M : ℝ) + 1) ?_ ?_
    · nlinarith [bltSampleSize_le_base hσ hε hM]
    · nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (M : ℝ)), Real.sqrt_nonneg (M : ℝ),
        (by exact_mod_cast hM : (1 : ℝ) ≤ M)]
  · nlinarith [le_max_left (1 : ℝ) (originalBltConstant σ ε hσ hε),
      sq_nonneg (max 1 (originalBltConstant σ ε hσ hε) + σ)]

private lemma blt_unbalanced_left {G : Type*} [DecidableEq G] [AddCommGroup G]
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) {A B : Finset G} (hA : A.Nonempty)
    (hsmall : A.card < bltSampleSize σ ε hσ hε (max A.card B.card)) :
    ∃ B' : Finset G, B' ⊆ B ∧
      (B'.card : ℝ) ≤
        bltConstant σ ε hσ hε * Real.sqrt (max A.card B.card : ℝ) ∧
      min (min ((1 - ε) * ((A + B).card : ℝ)) (σ * (A.card : ℝ)))
          (σ * (B.card : ℝ)) ≤ ((A + B').card : ℝ) := by
  let T := min (min ((1 - ε) * ((A + B).card : ℝ)) (σ * (A.card : ℝ)))
    (σ * (B.card : ℝ))
  have hceil : (⌈T⌉₊ : ℝ) ≤ σ * (A.card : ℝ) + 1 := by
    refine blt_ceil_target_le ?_ ?_
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · positivity
  have hbound : σ * (A.card : ℝ) + 1 ≤
      bltConstant σ ε hσ hε * Real.sqrt (max A.card B.card : ℝ) := by
    rw [← Nat.cast_max]
    refine blt_small_bound hσ hε ?_ hsmall
    exact (Nat.one_le_iff_ne_zero.mpr hA.card_ne_zero).trans (le_max_left _ _)
  by_cases hcard : ⌈T⌉₊ ≤ B.card
  · obtain ⟨B', hB'B, hB'card⟩ := Finset.exists_subset_card_eq hcard
    refine ⟨B', hB'B, ?_, ?_⟩
    · rw [hB'card]
      exact hceil.trans hbound
    · change T ≤ ((A + B').card : ℝ)
      refine (Nat.le_ceil T).trans ?_
      rw [← hB'card]
      exact_mod_cast Finset.card_le_card_add_left hA
  · refine ⟨B, Finset.Subset.refl B, ?_, ?_⟩
    · refine le_trans ?_ (hceil.trans hbound)
      exact_mod_cast Nat.le_of_lt (lt_of_not_ge hcard)
    · change T ≤ ((A + B).card : ℝ)
      refine (min_le_left _ _).trans ((min_le_left _ _).trans ?_)
      nlinarith

/--
The symmetric square-root form used in the rest of the verification, derived from the original
expected-value theorem above.
-/
theorem exists_blt_subsets {G : Type*} [DecidableEq G] [AddCommGroup G] {σ ε : ℝ} {A B : Finset G}
    (hσ : 0 < σ) (hε : 0 < ε) (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ A' A'' B' B'' : Finset G, A' ⊆ A'' ∧ A'' ⊆ A ∧ B' ⊆ B'' ∧ B'' ⊆ B ∧
      (1 - ε) * (A.card : ℝ) ≤ (A''.card : ℝ) ∧ (1 - ε) * (B.card : ℝ) ≤ (B''.card : ℝ) ∧
      (A'.card : ℝ) ≤ bltConstant σ ε hσ hε * Real.sqrt (max A.card B.card : ℝ) ∧
      (B'.card : ℝ) ≤ bltConstant σ ε hσ hε * Real.sqrt (max A.card B.card : ℝ) ∧
      min (min ((1 - ε) * ((A'' + B'').card : ℝ)) (σ * (A''.card : ℝ)))
          (σ * (B''.card : ℝ)) ≤ ((A' + B').card : ℝ) := by
  let r := bltSampleSize σ ε hσ hε (max A.card B.card)
  have hrbound : (r : ℝ) ≤
      bltConstant σ ε hσ hε * Real.sqrt (max A.card B.card : ℝ) := by
    rw [← Nat.cast_max]
    refine bltSampleSize_le hσ hε ?_
    exact (Nat.one_le_iff_ne_zero.mpr hA.card_ne_zero).trans (le_max_left _ _)
  by_cases hrA : r ≤ A.card
  · by_cases hrB : r ≤ B.card
    · have hproduct : originalBltConstant σ ε hσ hε * (max A.card B.card : ℝ) < r * r := by
        simpa [r, pow_two] using bltSampleSize_product hσ hε (max A.card B.card)
      obtain ⟨A', A₀, B', B₀, hA'A₀, hA₀A, hB'B₀, hB₀B, hA₀card, hB₀card,
          hA'card, hB'card, hsum⟩ := exists_blt_sample_deterministic hσ hε hA hB r r
        (bltSampleSize_pos hσ hε _) hrA (bltSampleSize_pos hσ hε _) hrB hproduct
      refine ⟨A', A₀, B', B₀, hA'A₀, hA₀A, hB'B₀, hB₀B, hA₀card, hB₀card,
        ?_, ?_, hsum⟩
      · refine le_trans ?_ hrbound
        exact_mod_cast hA'card
      · refine le_trans ?_ hrbound
        exact_mod_cast hB'card
    · have hBsmall : B.card <
          bltSampleSize σ ε hσ hε (max B.card A.card) := by
        rw [max_comm]
        change B.card < r
        exact lt_of_not_ge hrB
      obtain ⟨A', hA'A, hA'bound, hsum⟩ :=
        blt_unbalanced_left hσ hε hB hBsmall
      refine ⟨A', A, B, B, hA'A, Finset.Subset.refl A, Finset.Subset.refl B,
        Finset.Subset.refl B, ?_, ?_, ?_, ?_, ?_⟩
      · nlinarith
      · nlinarith
      · simpa only [Nat.cast_max, max_comm] using hA'bound
      · refine le_trans ?_ hrbound
        exact_mod_cast Nat.le_of_lt (lt_of_not_ge hrB)
      · simpa [add_comm, min_comm, min_left_comm, min_assoc] using hsum
  · obtain ⟨B', hB'B, hB'bound, hsum⟩ :=
      blt_unbalanced_left hσ hε hA (lt_of_not_ge hrA)
    refine ⟨A, A, B', B, Finset.Subset.refl A, Finset.Subset.refl A, hB'B,
      Finset.Subset.refl B, ?_, ?_, ?_, hB'bound, hsum⟩
    · nlinarith
    · nlinarith
    · refine le_trans ?_ hrbound
      exact_mod_cast Nat.le_of_lt (lt_of_not_ge hrA)

end

end Verification
