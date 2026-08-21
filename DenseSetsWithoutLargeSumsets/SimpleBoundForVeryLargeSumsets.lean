/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.Probability
import Mathlib.Combinatorics.Additive.RuzsaCovering

/-!
Bounds effective for very large sumsets.
-/

namespace DenseSetsWithoutLargeSumsets

open scoped Pointwise

noncomputable section

private def integerInterval (n : ℕ) : Finset ℤ :=
  natCastImage (interval n)

private lemma integerInterval_card (n : ℕ) : (integerInterval n).card = n := by
  rw [integerInterval, natCastImage_card]
  simp [interval, Nat.card_Icc]

private def castPair (p : Finset ℕ × Finset ℕ) : Finset ℤ × Finset ℤ :=
  (natCastImage p.1, natCastImage p.2)

private lemma castPair_injective : Function.Injective castPair := by
  intro p q h
  exact Prod.ext
    (Finset.image_injective Int.ofNat_injective (congr_arg Prod.fst h))
    (Finset.image_injective Int.ofNat_injective (congr_arg Prod.snd h))

/-- Ruzsa covering with the quotient converted to natural division. -/
lemma ruzsa_covering_int {A B : Finset ℤ} {m : ℕ} (hB : B.Nonempty)
    (hAB : (A + B).card ≤ m) :
    ∃ F ⊆ A, F.card ≤ m / B.card ∧ A ⊆ F + (B - B) := by
  classical
  obtain ⟨F, hFA, hFreal, hcover⟩ :=
    Finset.ruzsa_covering_add (A := A) (B := B)
      (K := (m : ℝ) / (B.card : ℝ)) hB (by
        rw [div_mul_cancel₀]
        · exact_mod_cast hAB
        · exact_mod_cast ne_of_gt (Finset.card_pos.mpr hB))
  refine ⟨F, hFA, ?_, hcover⟩
  apply (Nat.le_div_iff_mul_le (Finset.card_pos.mpr hB)).2
  exact_mod_cast
    ((mul_le_mul_of_nonneg_right hFreal
      (by positivity : (0 : ℝ) ≤ B.card)).trans_eq
      (by field_simp [ne_of_gt (by exact_mod_cast (Finset.card_pos.mpr hB) : (0 : ℝ) < B.card)]) :
        (F.card : ℝ) * (B.card : ℝ) ≤ (m : ℝ))

/-- The Ruzsa container `F + B - B` has size at most `k ^ 3` when
`#F ≤ k` and `#B = k`. -/
lemma ruzsa_container_card_le_cube {F B : Finset ℤ} {k : ℕ} (hF : F.card ≤ k)
    (hB : B.card = k) :
    (F + B - B).card ≤ k ^ 3 := by
  apply (Finset.card_sub_le).trans
  apply (Nat.mul_le_mul_right B.card Finset.card_add_le).trans
  apply (Nat.mul_le_mul (Nat.mul_le_mul hF (le_of_eq hB)) (le_of_eq hB)).trans
  norm_num [pow_succ]

/-- Every pair counted by the trivial counting lemma is represented by choosing a
`k`-set `B`, a Ruzsa encoding `F`, and then a `k`-subset of `F + B - B`. -/
lemma pair_small_sumset_family_subset_ruzsa_encoding (n k m : ℕ) :
    {p : Finset ℤ × Finset ℤ |
      p.1 ⊆ integerInterval n ∧ p.2 ⊆ integerInterval n ∧
        p.1.card = k ∧ p.2.card = k ∧ (p.1 + p.2).card ≤ m} ⊆
    {p : Finset ℤ × Finset ℤ |
      ∃ F : Finset ℤ,
        F ⊆ integerInterval n ∧ F.card ≤ m / k ∧
          p.2 ∈ (integerInterval n).powersetCard k ∧
            p.1 ∈ (F + p.2 - p.2).powersetCard k} := by
  classical
  intro p hp
  by_cases hk : k = 0
  · refine ⟨∅, by simp, by simp, ?_, ?_⟩
    · exact Finset.mem_powersetCard.mpr ⟨hp.2.1, hp.2.2.2.1⟩
    · apply Finset.mem_powersetCard.mpr
      constructor
      · simp [Finset.card_eq_zero.mp (by simpa [hk] using hp.2.2.1)]
      · exact hp.2.2.1
  · obtain ⟨F, hFA, hFcard, hcover⟩ :=
      ruzsa_covering_int (A := p.1) (B := p.2)
        (Finset.card_pos.mp (by simpa [hp.2.2.2.1] using Nat.pos_of_ne_zero hk)) hp.2.2.2.2
    refine ⟨F, hFA.trans hp.1, ?_, ?_, ?_⟩
    · simpa [hp.2.2.2.1] using hFcard
    · exact Finset.mem_powersetCard.mpr ⟨hp.2.1, hp.2.2.2.1⟩
    · exact Finset.mem_powersetCard.mpr
        ⟨by simpa [sub_eq_add_neg, add_assoc] using hcover, hp.2.2.1⟩

private def coverFinset (n k r : ℕ) : Finset (Finset ℤ × Finset ℤ) :=
  ((integerInterval n).powersetCard k).biUnion fun B =>
    ((integerInterval n).powersetCard r).biUnion fun F =>
      ((F + B - B).powersetCard k).image fun A => (A, B)

private lemma coverFinset_card_le (n k r : ℕ) (hrk : r ≤ k) :
    (coverFinset n k r).card ≤ Nat.choose n k * Nat.choose n r * Nat.choose (k ^ 3) k := by
  classical
  apply Finset.card_biUnion_le.trans
  refine (Finset.sum_le_sum
    (f := fun B => ((Finset.powersetCard r (integerInterval n)).biUnion fun F =>
      ((F + B - B).powersetCard k).image fun A => (A, B)).card)
    (g := fun B => ∑ F ∈ (integerInterval n).powersetCard r,
      (((F + B - B).powersetCard k).image fun A => (A, B)).card) ?_).trans ?_
  · intro B _hB
    exact Finset.card_biUnion_le
  · refine (Finset.sum_le_sum
      (f := fun B => ∑ F ∈ (integerInterval n).powersetCard r,
        (((F + B - B).powersetCard k).image fun A => (A, B)).card)
      (g := fun _ => ∑ F ∈ (integerInterval n).powersetCard r, Nat.choose (k ^ 3) k) ?_).trans ?_
    · intro B hB
      apply Finset.sum_le_sum
      intro F hF
      apply (Finset.card_image_le.trans_eq (Finset.card_powersetCard k (F + B - B))).trans
      apply Nat.choose_le_choose k
      apply ruzsa_container_card_le_cube (by
        rw [(Finset.mem_powersetCard.mp hF).2]
        exact hrk) (Finset.mem_powersetCard.mp hB).2
    · simp [Finset.card_powersetCard, integerInterval_card, Nat.mul_assoc]

private lemma castPair_mem_coverFinset {n k m : ℕ} (hrn : m / k ≤ n)
    {p : Finset ℕ × Finset ℕ}
    (hp : p ∈ {p : Finset ℕ × Finset ℕ |
      p.1 ⊆ interval n ∧ p.2 ⊆ interval n ∧
        p.1.card = k ∧ p.2.card = k ∧ (p.1 + p.2).card ≤ m}) :
    castPair p ∈ coverFinset n k (m / k) := by
  classical
  have hAint : (castPair p).1 ⊆ integerInterval n := by
    intro x hx
    change x ∈ p.1.image (Nat.castAddMonoidHom ℤ) at hx
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    exact Finset.mem_image.mpr ⟨a, hp.1 ha, rfl⟩
  have hBint : (castPair p).2 ⊆ integerInterval n := by
    intro x hx
    change x ∈ p.2.image (Nat.castAddMonoidHom ℤ) at hx
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    exact Finset.mem_image.mpr ⟨a, hp.2.1 ha, rfl⟩
  have hAcard : (castPair p).1.card = k := by
    change (p.1.image (Nat.castAddMonoidHom ℤ)).card = k
    exact (Finset.card_image_of_injective p.1 Int.ofNat_injective).trans hp.2.2.1
  have hBcard : (castPair p).2.card = k := by
    change (p.2.image (Nat.castAddMonoidHom ℤ)).card = k
    exact (Finset.card_image_of_injective p.2 Int.ofNat_injective).trans hp.2.2.2.1
  have hsum : ((castPair p).1 + (castPair p).2).card ≤ m := by
    have himg : ((p.1 + p.2).image (Nat.castAddMonoidHom ℤ)) =
        (castPair p).1 + (castPair p).2 := by
      change ((p.1 + p.2).image (Nat.castAddMonoidHom ℤ)) =
        p.1.image (Nat.castAddMonoidHom ℤ) + p.2.image (Nat.castAddMonoidHom ℤ)
      exact Finset.image_add (Nat.castAddMonoidHom ℤ)
    rw [← himg, Finset.card_image_of_injective]
    · exact hp.2.2.2.2
    · exact Int.ofNat_injective
  have hzmem : castPair p ∈ {p : Finset ℤ × Finset ℤ |
      p.1 ⊆ integerInterval n ∧ p.2 ⊆ integerInterval n ∧
        p.1.card = k ∧ p.2.card = k ∧ (p.1 + p.2).card ≤ m} :=
    ⟨hAint, hBint, hAcard, hBcard, hsum⟩
  obtain ⟨F₀, hF₀I, hF₀card, hBmem, hAmem₀⟩ :=
    pair_small_sumset_family_subset_ruzsa_encoding n k m hzmem
  have hrI : m / k ≤ (integerInterval n).card := by simpa [integerInterval_card] using hrn
  obtain ⟨F, hF₀F, hFI, hFcard⟩ := Finset.exists_subsuperset_card_eq hF₀I hF₀card hrI
  rw [coverFinset, Finset.mem_biUnion]
  refine ⟨(castPair p).2, hBmem, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨F, Finset.mem_powersetCard.mpr ⟨hFI, hFcard⟩, ?_⟩
  rw [Finset.mem_image]
  refine ⟨(castPair p).1, ?_, rfl⟩
  obtain ⟨hAcontainer, hAcard2⟩ := Finset.mem_powersetCard.mp hAmem₀
  exact Finset.mem_powersetCard.mpr ⟨hAcontainer.trans (by gcongr), hAcard2⟩

private lemma pair_small_sumset_family_card_le_of_large_quotient (n k m : ℕ) (hkm : k ≤ m / k) :
    {p : Finset ℕ × Finset ℕ |
      p.1 ⊆ interval n ∧ p.2 ⊆ interval n ∧
        p.1.card = k ∧ p.2.card = k ∧ (p.1 + p.2).card ≤ m}.ncard ≤
      n ^ (k + m / k) * Nat.choose (k ^ 3) k := by
  classical
  generalize hTdef : ({p : Finset ℕ × Finset ℕ |
    p.1 ⊆ interval n ∧ p.2 ⊆ interval n ∧
      p.1.card = k ∧ p.2.card = k ∧ (p.1 + p.2).card ≤ m}) = T
  generalize hUdef : ((interval n).powersetCard k ×ˢ (interval n).powersetCard k) = U
  have hsub : T ⊆ (U : Set (Finset ℕ × Finset ℕ)) := by
    intro p hp
    rw [← hTdef] at hp
    rw [← hUdef] at ⊢
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard] at hp ⊢
    exact ⟨⟨hp.1, hp.2.2.1⟩, ⟨hp.2.1, hp.2.2.2.1⟩⟩
  have hleU : T.ncard ≤ U.card := by
    apply (Set.ncard_le_ncard hsub).trans
    simp
  have hUcard : U.card = Nat.choose n k * Nat.choose n k := by
    rw [← hUdef]
    simp [Finset.card_product, Finset.card_powersetCard, interval, Nat.card_Icc]
  have hchoosepos : 0 < Nat.choose (k ^ 3) k := by
    apply Nat.choose_pos
    by_cases hk : k = 0
    · simp [hk]
    · have hkpos : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk)
      nlinarith [Nat.mul_le_mul hkpos hkpos, Nat.mul_le_mul (Nat.mul_le_mul hkpos hkpos) hkpos]
  apply hleU.trans
  rw [hUcard]
  apply (Nat.mul_le_mul (Nat.choose_le_pow n k) (Nat.choose_le_pow n k)).trans
  rw [← pow_add]
  refine le_trans ?_ (Nat.le_mul_of_pos_right _ hchoosepos)
  by_cases hn : n = 0
  · subst n
    by_cases hk : k = 0
    · simp [hk]
    · have hkk : k + k ≠ 0 := by omega
      have hkexp : k + m / k ≠ 0 := by omega
      rw [zero_pow hkk, zero_pow hkexp]
  · apply Nat.pow_le_pow_right (Nat.pos_of_ne_zero hn)
    exact Nat.add_le_add_left hkm k

/-- Trivial counting bound using Ruzsa covering, Corollary `stmt:trivialCountOfSets`. -/
lemma pair_small_sumset_family_card_le (n k m : ℕ) :
    {p : Finset ℕ × Finset ℕ |
      p.1 ⊆ interval n ∧ p.2 ⊆ interval n ∧
        p.1.card = k ∧ p.2.card = k ∧ (p.1 + p.2).card ≤ m}.ncard ≤
      n ^ (k + m / k) * Nat.choose (k ^ 3) k := by
  classical
  by_cases hkm : k ≤ m / k
  · exact pair_small_sumset_family_card_le_of_large_quotient n k m hkm
  · have hrk : m / k ≤ k := by omega
    by_cases hkn : k ≤ n
    · have hrn : m / k ≤ n := le_trans hrk hkn
      generalize hTdef : ({p : Finset ℕ × Finset ℕ |
        p.1 ⊆ interval n ∧ p.2 ⊆ interval n ∧
          p.1.card = k ∧ p.2.card = k ∧ (p.1 + p.2).card ≤ m}) = T
      have himage_subset :
          Set.image castPair T ⊆
            (coverFinset n k (m / k) : Set (Finset ℤ × Finset ℤ)) := by
        rintro q ⟨p, hp, rfl⟩
        rw [← hTdef] at hp
        exact castPair_mem_coverFinset hrn hp
      rw [← Set.ncard_image_of_injective T castPair_injective]
      apply (Set.ncard_le_ncard himage_subset).trans
      simp only [Set.ncard_coe_finset]
      apply (coverFinset_card_le n k (m / k) hrk).trans
      apply (Nat.mul_le_mul_right (Nat.choose (k ^ 3) k)
        (Nat.mul_le_mul (Nat.choose_le_pow n k) (Nat.choose_le_pow n (m / k)))).trans
      rw [← pow_add]
    · generalize hTdef : ({p : Finset ℕ × Finset ℕ |
        p.1 ⊆ interval n ∧ p.2 ⊆ interval n ∧
          p.1.card = k ∧ p.2.card = k ∧ (p.1 + p.2).card ≤ m}) = T
      have hTempty : T = ∅ := by
        ext p
        constructor
        · intro hp
          rw [← hTdef] at hp
          have hcardle : p.1.card ≤ n := by
            have hcardle' := Finset.card_le_card hp.1
            simpa [interval, Nat.card_Icc] using hcardle'
          have : k ≤ n := by
            rw [← hp.2.2.1]
            exact hcardle
          omega
        · intro hp
          simp at hp
      rw [hTempty]
      simp

/-- The purely analytic estimate left after the very-large-sumset union bound. -/
def veryLargeSumsetAnalyticBound (γ : ℝ) (n : ℕ) (δ : unitInterval) : Prop :=
  ∑ m ∈ Finset.Icc ((pairCardThreshold (3 + γ) n δ + 1) * pairCardThreshold (3 + γ) n δ / 2)
      (pairCardThreshold (3 + γ) n δ * pairCardThreshold (3 + γ) n δ),
      (n ^ (pairCardThreshold (3 + γ) n δ + m / pairCardThreshold (3 + γ) n δ) *
        Nat.choose (pairCardThreshold (3 + γ) n δ ^ 3) (pairCardThreshold (3 + γ) n δ) : ℝ) *
        (δ : ℝ) ^ m
    ≤ (pairCardThreshold (3 + γ) n δ : ℝ) ^ 2 /
      (n : ℝ) ^ (γ * (pairCardThreshold (3 + γ) n δ : ℝ) / 3)

/--
The explicit threshold from the very-large-sumset estimate.
-/
def veryLargeSumsetThreshold (γ c : ℝ) : ℕ :=
  Nat.ceil (((18 * densityCoefficient (3 + γ) c) / γ) ^ ((36 : ℝ) / γ))

/--
Threshold used in the final analytic step of the very-large-sumset proof.

The surrounding statements use strict hypotheses of the form
`veryLargeSumsetStrictThreshold γ < n`. Subtracting one makes this equivalent to the non-strict
threshold `n ≥ veryLargeSumsetThreshold γ c` when `0 < γ`.
-/
def veryLargeSumsetStrictThreshold (γ c : ℝ) : ℕ :=
  veryLargeSumsetThreshold γ c - 1

private lemma veryLargeSumsetThreshold_pos {γ c : ℝ} (hγ_pos : 0 < γ)
    (hc_pos : 0 < c) (hc_lt : c < 1) :
    0 < veryLargeSumsetThreshold γ c := by
  rw [veryLargeSumsetThreshold, Nat.ceil_pos]
  have hq_pos : 0 < densityCoefficient (3 + γ) c :=
    lt_trans zero_lt_one
      (densityCoefficient_gt_one (by linarith : 0 < 3 + γ) hc_pos hc_lt)
  exact Real.rpow_pos_of_pos
    (div_pos (mul_pos (by norm_num) hq_pos) hγ_pos) _

private lemma two_le_veryLargeSumsetThreshold {γ c : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1)
    (hc_pos : 0 < c) (hc_lt : c < 1) :
    2 ≤ veryLargeSumsetThreshold γ c := by
  rw [veryLargeSumsetThreshold]
  norm_num [Nat.add_one_le_ceil_iff]
  have hbase : 1 < (18 * densityCoefficient (3 + γ) c) / γ := by
    rw [one_lt_div hγ_pos]
    nlinarith [densityCoefficient_gt_one (by linarith : 0 < 3 + γ) hc_pos hc_lt]
  simpa using Real.one_lt_rpow hbase (by positivity : 0 < (36 : ℝ) / γ)

private lemma veryLargeSumsetThreshold_le_of_veryLargeSumsetStrictThreshold_lt {γ c : ℝ} (hγ_pos : 0
  < γ)
    (hc_pos : 0 < c) (hc_lt : c < 1) {n : ℕ} (hn : veryLargeSumsetStrictThreshold γ c < n) :
    veryLargeSumsetThreshold γ c ≤ n := by
  have hpos : 0 < veryLargeSumsetThreshold γ c :=
    veryLargeSumsetThreshold_pos hγ_pos hc_pos hc_lt
  rw [veryLargeSumsetStrictThreshold] at hn
  omega

private lemma veryLargeSumset_log_log_bound {γ c : ℝ} (hγ_pos : 0 < γ)
    (hγ_le : γ ≤ 1) (hc_pos : 0 < c) (hc_lt : c < 1)
    {n : ℕ} (hn : veryLargeSumsetStrictThreshold γ c < n) :
    18 * Real.log (densityCoefficient (3 + γ) c * Real.log (n : ℝ)) ≤
      γ * Real.log (n : ℝ) := by
  let q := densityCoefficient (3 + γ) c
  generalize hx : Real.log (n : ℝ) = x
  generalize hy : γ * x / 18 = y
  generalize hL : Real.log ((18 * q) / γ) = L
  have hNle : veryLargeSumsetThreshold γ c ≤ n :=
    veryLargeSumsetThreshold_le_of_veryLargeSumsetStrictThreshold_lt hγ_pos hc_pos hc_lt hn
  have hNtwo : 2 ≤ veryLargeSumsetThreshold γ c :=
    two_le_veryLargeSumsetThreshold hγ_pos hγ_le hc_pos hc_lt
  have hn_two : 2 ≤ n := le_trans hNtwo hNle
  have hx_pos : 0 < x := by
    rw [← hx]
    exact Real.log_pos (by exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 2) hn_two)
  have hq_gt_one : 1 < q :=
    densityCoefficient_gt_one (by linarith : 0 < 3 + γ) hc_pos hc_lt
  have hbase_pos : 0 < (18 * q) / γ := by positivity
  have hbase_gt_one : 1 < (18 * q) / γ := by
    rw [one_lt_div hγ_pos]
    nlinarith
  have hL_pos : 0 < L := by
    rw [← hL]
    exact Real.log_pos hbase_gt_one
  have hvalue_le_n : ((18 * q) / γ) ^ ((36 : ℝ) / γ) ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hNle)
  have hlog_value_le :
      Real.log (((18 * q) / γ) ^ ((36 : ℝ) / γ)) ≤ x := by
    rw [← hx]
    exact Real.log_le_log (Real.rpow_pos_of_pos hbase_pos _) hvalue_le_n
  have hlog_value_eq :
      Real.log (((18 * q) / γ) ^ ((36 : ℝ) / γ)) = ((36 : ℝ) / γ) * L := by
    rw [← hL, Real.log_rpow hbase_pos]
  have hy_bound : 2 * L ≤ y := by
    have hmul := mul_le_mul_of_nonneg_left hlog_value_le (by positivity : 0 ≤ γ / 18)
    rw [hlog_value_eq] at hmul
    have hleft : (γ / 18) * ((36 / γ) * L) = 2 * L := by
      field_simp [hγ_pos.ne']
      ring
    have hright : (γ / 18) * x = y := by rw [← hy]; ring
    rwa [hleft, hright] at hmul
  have hy_pos : 0 < y := lt_of_lt_of_le (by linarith : 0 < 2 * L) hy_bound
  have hlogqx_eq : Real.log (q * x) = L + Real.log y := by
    have hprod : q * x = ((18 * q) / γ) * y := by
      rw [← hy]
      field_simp [hγ_pos.ne']
    rw [hprod, Real.log_mul (ne_of_gt hbase_pos) (ne_of_gt hy_pos), hL]
  have hlogqx_le : Real.log (q * x) ≤ y := by
    rw [hlogqx_eq]
    linarith [log_le_half_self hy_pos]
  apply (mul_le_mul_of_nonneg_left hlogqx_le (by norm_num)).trans_eq
  rw [← hy, ← hx]
  ring

private lemma pairCardThreshold_pos (n : ℕ) (τ : ℝ) (δ : unitInterval)
    (hτ : 0 < τ) (hδ : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) (hn : 1 < n) :
    0 < pairCardThreshold τ n δ := by
  rw [pairCardThreshold, Nat.ceil_pos]
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hlog_inv_pos : 0 < Real.log (1 / δ) := by
    apply Real.log_pos
    rw [one_lt_div hδ]
    exact hδ_lt
  positivity

private lemma pairCardThreshold_log_le_gamma_log {γ c : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1)
    (hc_pos : 0 < c) {n : ℕ} (hn : veryLargeSumsetStrictThreshold γ c < n) {δ : unitInterval}
    (hδ_pos : 0 < (δ : ℝ)) (hδ_upper : (δ : ℝ) ≤ 1 - c)
    (hkpos : 0 < pairCardThreshold (3 + γ) n δ) :
    18 * Real.log (pairCardThreshold (3 + γ) n δ : ℝ) ≤ γ * Real.log (n : ℝ) := by
  have hc_lt : c < 1 := by linarith
  have hNle : veryLargeSumsetThreshold γ c ≤ n :=
    veryLargeSumsetThreshold_le_of_veryLargeSumsetStrictThreshold_lt hγ_pos hc_pos hc_lt hn
  have hNtwo : 2 ≤ veryLargeSumsetThreshold γ c :=
    two_le_veryLargeSumsetThreshold hγ_pos hγ_le hc_pos hc_lt
  have hn_two : 2 ≤ n := le_trans hNtwo hNle
  have hk_le : (pairCardThreshold (3 + γ) n δ : ℝ) ≤
      densityCoefficient (3 + γ) c * Real.log (n : ℝ) :=
    pairCardThreshold_le_densityCoefficient_mul_log (by linarith) hc_pos hn_two hδ_pos hδ_upper
  have hlog_le :
      Real.log (pairCardThreshold (3 + γ) n δ : ℝ) ≤
        Real.log (densityCoefficient (3 + γ) c * Real.log (n : ℝ)) :=
    Real.log_le_log (by exact_mod_cast hkpos) hk_le
  have hmul18 : 18 * Real.log (pairCardThreshold (3 + γ) n δ : ℝ) ≤
      18 * Real.log (densityCoefficient (3 + γ) c * Real.log (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hlog_le (by norm_num)
  exact hmul18.trans (veryLargeSumset_log_log_bound hγ_pos hγ_le hc_pos hc_lt hn)

private def veryLargeSumsetPairSlice (n k m : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((interval n).powersetCard k ×ˢ (interval n).powersetCard k).filter fun p =>
    (p.1 + p.2).card = m

private lemma mem_veryLargeSumsetPairSlice {n k m : ℕ} {p : Finset ℕ × Finset ℕ} :
    p ∈ veryLargeSumsetPairSlice n k m ↔
      p.1 ⊆ interval n ∧ p.2 ⊆ interval n ∧
        p.1.card = k ∧ p.2.card = k ∧ (p.1 + p.2).card = m := by
  rw [veryLargeSumsetPairSlice, Finset.mem_filter, Finset.mem_product]
  simp only [Finset.mem_powersetCard, and_assoc]
  tauto

/--
The trivial counting corollary bounds the number of fixed-sumset-cardinality witness pairs used
in the very-large-sumset union bound.
-/
lemma veryLargeSumsetPairSlice_card_le (n k m : ℕ) :
    (veryLargeSumsetPairSlice n k m).card ≤
      n ^ (k + m / k) * Nat.choose (k ^ 3) k := by
  classical
  generalize hTdef : ({p : Finset ℕ × Finset ℕ |
    p.1 ⊆ interval n ∧ p.2 ⊆ interval n ∧
      p.1.card = k ∧ p.2.card = k ∧ (p.1 + p.2).card ≤ m}) = T
  generalize hUdef : ((interval n).powersetCard k ×ˢ (interval n).powersetCard k) = U
  have hTfinite : T.Finite := by
    apply Set.Finite.subset (s := (U : Set (Finset ℕ × Finset ℕ)))
      (by rw [← hUdef]; exact (Finset.powersetCard k (interval n) ×ˢ
        Finset.powersetCard k (interval n)).finite_toSet)
    intro p hp
    rw [← hTdef] at hp
    rw [← hUdef] at ⊢
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard] at hp ⊢
    exact ⟨⟨hp.1, hp.2.2.1⟩, ⟨hp.2.1, hp.2.2.2.1⟩⟩
  have hsubset : (veryLargeSumsetPairSlice n k m : Set (Finset ℕ × Finset ℕ)) ⊆ T := by
    intro p hp
    have hp := mem_veryLargeSumsetPairSlice.mp hp
    rw [← hTdef]
    exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, le_of_eq hp.2.2.2.2⟩
  rw [← Set.ncard_coe_finset]
  apply (Set.ncard_le_ncard hsubset hTfinite).trans
  rw [← hTdef]
  apply pair_small_sumset_family_card_le

def veryLargeSumsetEvent (n k : ℕ) (S : Finset ℕ) : Prop :=
  ∃ A B : Finset ℕ,
    A ⊆ interval n ∧ B ⊆ interval n ∧ A.card = k ∧ B.card = k ∧
      (k + 1) * k / 2 ≤ (A + B).card ∧ A + B ⊆ S

/--
Union bound for the very-large-sumset event after replacing the existential witnesses by the
`pair_small_sumset_family_card_le` upper bound, slice by slice in `m = #(A + B)`.
-/
lemma veryLargeSumsetEvent_measure_le_sum
    (n k : ℕ) {δ : unitInterval}
    (prob : ℕ → ℝ)
    (hprob_nonneg : ∀ m, 0 ≤ prob m)
    (hpair :
      ∀ m (p : Finset ℕ × Finset ℕ), p ∈ veryLargeSumsetPairSlice n k m →
        (binomialFinsetSubset (Set.Icc 1 n) δ).real
          {S : Finset ℕ | p.1 + p.2 ⊆ S} ≤ prob m) :
    (binomialFinsetSubset (Set.Icc 1 n) δ).real {S : Finset ℕ | veryLargeSumsetEvent n k S} ≤
      ∑ m ∈ Finset.Icc ((k + 1) * k / 2) (k * k),
        (n ^ (k + m / k) * Nat.choose (k ^ 3) k : ℝ) * prob m := by
  classical
  have hevent_subset : {S : Finset ℕ | veryLargeSumsetEvent n k S} ⊆
      ⋃ m ∈ Finset.Icc ((k + 1) * k / 2) (k * k),
        ⋃ p ∈ veryLargeSumsetPairSlice n k m, {S : Finset ℕ | p.1 + p.2 ⊆ S} := by
    intro S hS
    rcases hS with ⟨A, B, hA, hB, hAcard, hBcard, hlarge, hsumS⟩
    have hm_upper : (A + B).card ≤ k * k := by
      apply Finset.card_add_le.trans
      rw [hAcard, hBcard]
    refine Set.mem_iUnion₂.mpr ⟨(A + B).card,
      Finset.mem_Icc.mpr ⟨hlarge, hm_upper⟩, ?_⟩
    refine Set.mem_iUnion₂.mpr ⟨(A, B), ?_, hsumS⟩
    rw [mem_veryLargeSumsetPairSlice]
    exact ⟨hA, hB, hAcard, hBcard, rfl⟩
  refine le_trans ?_
      ((MeasureTheory.measureReal_biUnion_finset_le
        (μ := binomialFinsetSubset (Set.Icc 1 n) δ)
        (Finset.Icc ((k + 1) * k / 2) (k * k))
        (fun m => ⋃ p ∈ veryLargeSumsetPairSlice n k m,
          {S : Finset ℕ | p.1 + p.2 ⊆ S})).trans ?_)
  · rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def]
    exact ENNReal.toReal_mono
      (MeasureTheory.measure_ne_top (binomialFinsetSubset (Set.Icc 1 n) δ) _)
      (MeasureTheory.measure_mono hevent_subset)
  · refine le_trans (b := ∑ m ∈ Finset.Icc ((k + 1) * k / 2) (k * k),
      (veryLargeSumsetPairSlice n k m).card * prob m) ?_ ?_
    · refine Finset.sum_le_sum ?_
      intro m hm
      apply le_trans
        (MeasureTheory.measureReal_biUnion_finset_le
          (μ := binomialFinsetSubset (Set.Icc 1 n) δ) (veryLargeSumsetPairSlice n k m)
          fun p => {S : Finset ℕ | p.1 + p.2 ⊆ S})
      refine (Finset.sum_le_sum
        (g := fun _ => prob m) ?_).trans ?_
      · intro p hp
        exact hpair m p hp
      · simp [mul_comm]
    · refine Finset.sum_le_sum ?_
      intro m hm
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast veryLargeSumsetPairSlice_card_le n k m)
        (hprob_nonneg m)

/--
For fixed `A` and `B`, the probability that the binomial random finset contains `A + B` is at
most `δ ^ #(A + B)`. If `A + B` is not contained in the ambient interval, the event has
probability zero.
-/
lemma fixed_pair_sumset_probability_le
    (n : ℕ) (δ : unitInterval) (A B : Finset ℕ) :
    (binomialFinsetSubset (Set.Icc 1 n) δ).real {S : Finset ℕ | A + B ⊆ S} ≤
      (δ : ℝ) ^ (A + B).card := by
  classical
  have hΩ : (Set.Icc 1 n : Set ℕ).Finite := Set.finite_Icc 1 n
  simpa [interval] using
    (binomialFinsetSubset_real_superset_nat
      (Ω := Set.Icc 1 n) (p := δ) hΩ (T := A + B))

lemma unitInterval_pow_le_exp_div_mul_log (n m : ℕ) (τ : ℝ) (δ : unitInterval)
    (_hτ_nonneg : 0 ≤ τ) (hδ : 0 < δ) (hδ_lt : δ < 1) (hn : 1 < n)
    (hkpos : 0 < pairCardThreshold τ n δ) :
    (δ : ℝ) ^ m ≤ (n : ℝ) ^ (-τ * (m : ℝ) / pairCardThreshold τ n δ : ℝ) := by
  generalize hkdef : pairCardThreshold τ n δ = k at *
  have hδ_pos : 0 < (δ : ℝ) := by exact hδ
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hn_log_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hlog_inv_pos : 0 < Real.log (1 / δ) := by
    apply Real.log_pos
    rw [one_lt_div hδ]
    exact hδ_lt
  have harg_nonneg : 0 ≤ τ * Real.log (n : ℝ) / Real.log (1 / δ) := by
    positivity
  have hceil :
      τ * Real.log (n : ℝ) / Real.log (1 / δ) ≤ (k : ℝ) := by
    rw [← hkdef]
    simpa [pairCardThreshold] using
      (Nat.le_ceil (τ * Real.log (n : ℝ) / Real.log (1 / δ)))
  have hkpos_real : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hlog_inv_ge : τ * Real.log (n : ℝ) / (k : ℝ) ≤ Real.log (1 / δ) := by
    have hmul : τ * Real.log (n : ℝ) / Real.log (1 / δ) * Real.log (1 / δ) ≤
        (k : ℝ) * Real.log (1 / δ) :=
      mul_le_mul_of_nonneg_right hceil (le_of_lt hlog_inv_pos)
    have hmul' : τ * Real.log (n : ℝ) ≤ (k : ℝ) * Real.log (1 / δ) := by
      rw [div_mul_cancel₀ _ (ne_of_gt hlog_inv_pos)] at hmul
      exact hmul
    exact (div_le_iff₀ hkpos_real).2 (by simpa [mul_comm] using hmul')
  have hlog_eq : Real.log (1 / δ) = -Real.log δ := by
    rw [Real.log_div one_ne_zero (Ne.symm (ne_of_lt hδ)), Real.log_one, zero_sub]
  have h2 : Real.log δ ≤ -τ * Real.log (n : ℝ) / (k : ℝ) := by
    have hneg := neg_le_neg hlog_inv_ge
    simpa [hlog_eq, neg_div] using hneg
  by_cases hm : m = 0
  · simp [hm]
  · have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
    have h3 : Real.log δ * m ≤ Real.log (n : ℝ) * (-τ * (m : ℝ) / (k : ℝ)) := by
      have h := mul_le_mul_of_nonneg_right h2 (le_of_lt hm_pos)
      ring_nf at h
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
    rw [← Real.exp_log (pow_pos hδ_pos m), Real.log_pow, mul_comm]
    apply (Real.exp_le_exp.mpr h3).trans_eq
    rw [Real.rpow_def_of_pos hn_pos]

private lemma veryLargeSumset_nat_div_lower {k m : ℕ} (hk : 0 < k)
    (hm : (k + 1) * k / 2 ≤ m) :
    k ≤ 2 * (m / k) := by
  by_contra h
  have hlt : 2 * (m / k) < k := Nat.lt_of_not_ge h
  have hq1 : 2 * (m / k + 1) ≤ k + 1 := by omega
  have hm_lt : m < (m / k + 1) * k := by
    have hmod := Nat.mod_lt m hk
    conv_lhs => rw [(Nat.div_add_mod m k).symm]
    apply (Nat.add_lt_add_left hmod _).trans_eq
    ring
  have hA : (m / k + 1) * k ≤ ((k + 1) * k) / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    nlinarith
  omega

private lemma veryLargeSumset_summand_le {γ : ℝ} (hγ_pos : 0 < γ) {n k m : ℕ}
    (hn : 1 < n) (hk : 0 < k) {δ : unitInterval}
    (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1)
    (hm_lower : (k + 1) * k / 2 ≤ m)
    (hlogk : 18 * Real.log (k : ℝ) ≤ γ * Real.log (n : ℝ))
    (hkdef : k = pairCardThreshold (3 + γ) n δ) :
    ((n ^ (k + m / k) * Nat.choose (k ^ 3) k : ℕ) : ℝ) * (δ : ℝ) ^ m
      ≤ (n : ℝ) ^ (-γ * (k : ℝ) / 3) := by
  generalize hτ : 3 + γ = τ
  generalize hr : m / k = r
  generalize he : k + r = e
  have hτ_nonneg : 0 ≤ τ := by rw [← hτ]; linarith
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hkR_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hδpow : (δ : ℝ) ^ m ≤ (n : ℝ) ^ (-τ * (m : ℝ) / (k : ℝ)) := by
    rw [hkdef, ← hτ]
    exact unitInterval_pow_le_exp_div_mul_log n m (3 + γ) δ (by linarith) hδ_pos hδ_lt hn
      (pairCardThreshold_pos n (3 + γ) δ (by linarith) hδ_pos hδ_lt hn)
  have hchoose : (Nat.choose (k ^ 3) k : ℝ) ≤ (k : ℝ) ^ (3 * k) := by
    apply le_trans (b := (((k ^ 3) ^ k : ℕ) : ℝ))
    · exact_mod_cast Nat.choose_le_pow (k ^ 3) k
    · rw [Nat.cast_pow, Nat.cast_pow, pow_mul]
  have hfirst :
      ((n ^ e * Nat.choose (k ^ 3) k : ℕ) : ℝ) * (δ : ℝ) ^ m
        ≤ ((n : ℝ) ^ e * (k : ℝ) ^ (3 * k)) *
          (n : ℝ) ^ (-τ * (m : ℝ) / (k : ℝ)) := by
    have hnchoose :
        ((n ^ e * Nat.choose (k ^ 3) k : ℕ) : ℝ) ≤
          (n : ℝ) ^ e * (k : ℝ) ^ (3 * k) := by
      refine le_trans ?_ (mul_le_mul_of_nonneg_left hchoose (by positivity))
      rw [← he]
      rw [Nat.cast_mul, Nat.cast_pow]
    exact mul_le_mul hnchoose hδpow (pow_nonneg hδ_pos.le m) (by positivity)
  have he_le : (e : ℝ) ≤ 3 * (r : ℝ) := by
    rw [← he, ← hr]
    have hkr : k ≤ 2 * (m / k) := veryLargeSumset_nat_div_lower hk hm_lower
    exact_mod_cast (by omega : k + m / k ≤ 3 * (m / k))
  have hr_le_mdiv : (r : ℝ) ≤ (m : ℝ) / (k : ℝ) := by
    rw [← hr]
    rw [le_div_iff₀ hkR_pos]
    exact_mod_cast (Nat.div_mul_le_self m k)
  have hr_ge_half : (k : ℝ) / 2 ≤ (r : ℝ) := by
    rw [← hr]
    have hkr : k ≤ 2 * (m / k) := veryLargeSumset_nat_div_lower hk hm_lower
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    rw [mul_comm]
    exact_mod_cast hkr
  have hcount_exp :
      ((e : ℝ) - τ * ((m : ℝ) / (k : ℝ))) * Real.log (n : ℝ) ≤
        (-γ * (k : ℝ) / 2) * Real.log (n : ℝ) := by
    have hτr_le : τ * (r : ℝ) ≤ τ * ((m : ℝ) / (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hr_le_mdiv hτ_nonneg
    have hcoef : (e : ℝ) - τ * ((m : ℝ) / (k : ℝ)) ≤ -γ * (r : ℝ) := by
      rw [← hτ] at hτr_le
      nlinarith
    have hcoef2 : (e : ℝ) - τ * ((m : ℝ) / (k : ℝ)) ≤
        -γ * (k : ℝ) / 2 := by
      nlinarith [hcoef, mul_le_mul_of_nonneg_left hr_ge_half hγ_pos.le]
    exact mul_le_mul_of_nonneg_right hcoef2
      (Real.log_nonneg (by exact_mod_cast (le_of_lt hn)))
  have hchoose_exp :
      (3 * (k : ℝ)) * Real.log (k : ℝ) ≤
        γ * (k : ℝ) * Real.log (n : ℝ) / 6 := by
    have hmul := mul_le_mul_of_nonneg_left hlogk (by positivity : 0 ≤ (k : ℝ) / 6)
    nlinarith
  have hexp :
      ((n : ℝ) ^ e * (k : ℝ) ^ (3 * k)) *
          (n : ℝ) ^ (-τ * (m : ℝ) / (k : ℝ)) ≤
        (n : ℝ) ^ (-γ * (k : ℝ) / 3) := by
    rw [← Real.rpow_natCast (n : ℝ) e, ← Real.rpow_natCast (k : ℝ) (3 * k)]
    rw [Real.rpow_def_of_pos hn_pos, Real.rpow_def_of_pos hkR_pos,
      Real.rpow_def_of_pos hn_pos, Real.rpow_def_of_pos hn_pos]
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have htarget :
        Real.log (n : ℝ) * (e : ℝ) + Real.log (k : ℝ) * ((3 * k : ℕ) : ℝ) +
            Real.log (n : ℝ) * (-τ * (m : ℝ) / (k : ℝ)) =
          ((e : ℝ) - τ * ((m : ℝ) / (k : ℝ))) * Real.log (n : ℝ) +
            (3 * (k : ℝ)) * Real.log (k : ℝ) := by
      rw [← he, ← hr, ← hτ]
      norm_num [Nat.cast_mul]
      ring
    rw [htarget]
    nlinarith
  exact hfirst.trans hexp

private lemma veryLargeSumset_lowerEndpoint_pos (k : ℕ) (hk : 0 < k) :
    1 ≤ ((k + 1) * k) / 2 := by
  have hkk : 2 ≤ (k + 1) * k := by
    nlinarith [Nat.succ_le_iff.mpr hk]
  exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 (by simpa using hkk)

private lemma veryLargeSumset_mRange_card_le (k : ℕ) (hk : 0 < k) :
    (Finset.Icc ((k + 1) * k / 2) (k * k)).card ≤ k * k := by
  have hsub : Finset.Icc ((k + 1) * k / 2) (k * k) ⊆ Finset.Icc 1 (k * k) := by
    intro m hm
    rw [Finset.mem_Icc] at hm ⊢
    exact ⟨le_trans (veryLargeSumset_lowerEndpoint_pos k hk) hm.1, hm.2⟩
  apply (Finset.card_le_card hsub).trans
  simp [Nat.card_Icc]

private lemma veryLargeSumsetAnalyticBound_of_density_bounds
    {γ c : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hc_pos : 0 < c)
    {n : ℕ} (hn : veryLargeSumsetStrictThreshold γ c < n) {δ : unitInterval}
    (hδ_lower : (n : ℝ) ^ (-(1 / 2 : ℝ)) < (δ : ℝ))
    (hδ_upper : (δ : ℝ) ≤ 1 - c) :
    veryLargeSumsetAnalyticBound γ n δ := by
  generalize hkdef : pairCardThreshold (3 + γ) n δ = k
  generalize hMdef : Finset.Icc ((k + 1) * k / 2) (k * k) = M
  have hc_lt : c < 1 := by
    have hδ_pos : 0 < (δ : ℝ) :=
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) _).trans_lt hδ_lower
    linarith
  have hNle : veryLargeSumsetThreshold γ c ≤ n :=
    veryLargeSumsetThreshold_le_of_veryLargeSumsetStrictThreshold_lt hγ_pos hc_pos hc_lt hn
  have hNtwo : 2 ≤ veryLargeSumsetThreshold γ c :=
    two_le_veryLargeSumsetThreshold hγ_pos hγ_le hc_pos hc_lt
  have hn_two : 2 ≤ n := le_trans hNtwo hNle
  have hn_one : 1 < n := lt_of_lt_of_le (by norm_num : 1 < 2) hn_two
  have hn_pos_real : 0 < (n : ℝ) := by positivity
  have hδ_pos : 0 < (δ : ℝ) :=
    (Real.rpow_pos_of_pos hn_pos_real (-(1 / 2 : ℝ))).trans hδ_lower
  have hδ_lt_one : (δ : ℝ) < 1 := by linarith
  have hkpos : 0 < k :=
    by
      rw [← hkdef]
      apply pairCardThreshold_pos n (3 + γ) δ (by linarith) hδ_pos hδ_lt_one hn_one
  have hlogk : 18 * Real.log (k : ℝ) ≤ γ * Real.log (n : ℝ) := by
    rw [← hkdef]
    apply pairCardThreshold_log_le_gamma_log hγ_pos hγ_le hc_pos hn hδ_pos hδ_upper
    simpa [hkdef] using hkpos
  have hterm :
      ∀ m ∈ M,
        ((n ^ (k + m / k) * Nat.choose (k ^ 3) k : ℕ) : ℝ) * (δ : ℝ) ^ m
          ≤ (n : ℝ) ^ (-γ * (k : ℝ) / 3) := by
    intro m hm
    rw [← hMdef] at hm
    have hm_lower : (k + 1) * k / 2 ≤ m := (Finset.mem_Icc.mp hm).1
    exact veryLargeSumset_summand_le hγ_pos hn_one hkpos hδ_pos hδ_lt_one hm_lower hlogk hkdef.symm
  have hbound_nonneg : 0 ≤ (n : ℝ) ^ (-γ * (k : ℝ) / 3) := by positivity
  rw [veryLargeSumsetAnalyticBound, hkdef]
  change (∑ m ∈ Finset.Icc ((k + 1) * k / 2) (k * k),
      (n ^ (k + m / k) * Nat.choose (k ^ 3) k : ℝ) * (δ : ℝ) ^ m) ≤
    (k : ℝ) ^ 2 / (n : ℝ) ^ (γ * (k : ℝ) / 3)
  apply le_trans
    (b := ∑ m ∈ Finset.Icc ((k + 1) * k / 2) (k * k),
      (n : ℝ) ^ (-γ * (k : ℝ) / 3))
  · refine Finset.sum_le_sum
      (s := Finset.Icc ((k + 1) * k / 2) (k * k))
      (f := fun m =>
        (n ^ (k + m / k) * Nat.choose (k ^ 3) k : ℝ) * (δ : ℝ) ^ m)
      (g := fun _ => (n : ℝ) ^ (-γ * (k : ℝ) / 3)) ?_
    intro m hm
    simpa [Nat.cast_mul] using hterm m (by rw [← hMdef]; exact hm)
  · refine le_trans
      (b := ((Finset.Icc ((k + 1) * k / 2) (k * k)).card : ℝ) *
        (n : ℝ) ^ (-γ * (k : ℝ) / 3)) ?_ ?_
    · simp [mul_comm]
    · have hcard : ((Finset.Icc ((k + 1) * k / 2) (k * k)).card : ℝ) ≤
          (k : ℝ) ^ 2 := by
        have hcardNat := veryLargeSumset_mRange_card_le k hkpos
        apply le_trans (b := ((k * k : ℕ) : ℝ))
        · exact_mod_cast hcardNat
        · rw [Nat.cast_mul]
          ring_nf
          apply le_refl
      apply (mul_le_mul_of_nonneg_right hcard hbound_nonneg).trans_eq
      have hneg : -γ * (k : ℝ) / 3 = -(γ * (k : ℝ) / 3) := by ring
      rw [hneg, Real.rpow_neg hn_pos_real.le]
      ring

/--
Very-large-sumset probability estimate reduced to the final analytic sum estimate.
-/
lemma veryLargeSumsetEvent_measure_le
    (γ : ℝ) (n : ℕ) (δ : unitInterval)
    (hanalytic : veryLargeSumsetAnalyticBound γ n δ) :
    (binomialFinsetSubset (Set.Icc 1 n) δ).real
      {S : Finset ℕ | veryLargeSumsetEvent n (pairCardThreshold (3 + γ) n δ) S} ≤
      (pairCardThreshold (3 + γ) n δ : ℝ) ^ 2 /
        (n : ℝ) ^ (γ * (pairCardThreshold (3 + γ) n δ : ℝ) / 3) := by
  classical
  have hprob_nonneg : ∀ m : ℕ, 0 ≤ (δ : ℝ) ^ m := fun m => pow_nonneg δ.2.1 m
  have hpair :
      ∀ m (p : Finset ℕ × Finset ℕ),
        p ∈ veryLargeSumsetPairSlice n (pairCardThreshold (3 + γ) n δ) m →
        (binomialFinsetSubset (Set.Icc 1 n) δ).real
          {S : Finset ℕ | p.1 + p.2 ⊆ S} ≤ (δ : ℝ) ^ m := by
    intro m p hp
    have hcard : (p.1 + p.2).card = m := (mem_veryLargeSumsetPairSlice.mp hp).2.2.2.2
    simpa [hcard] using fixed_pair_sumset_probability_le n δ p.1 p.2
  exact (veryLargeSumsetEvent_measure_le_sum n (pairCardThreshold (3 + γ) n δ)
      (fun m => (δ : ℝ) ^ m) hprob_nonneg hpair).trans
    (by simpa [veryLargeSumsetAnalyticBound] using hanalytic)

/-- Probability estimate for the very-large-sumset range. -/
theorem very_large_sumset_probability_le
    {γ c : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hc_pos : 0 < c)
    {n : ℕ} (hn : veryLargeSumsetStrictThreshold γ c < n)
    {δ : unitInterval}
    (hδ_lower : (n : ℝ) ^ (-(1 / 2 : ℝ)) < (δ : ℝ))
    (hδ_upper : (δ : ℝ) ≤ 1 - c) :
    (binomialFinsetSubset (Set.Icc 1 n) δ).real
      {S : Finset ℕ | veryLargeSumsetEvent n (pairCardThreshold (3 + γ) n δ) S} ≤
      (pairCardThreshold (3 + γ) n δ : ℝ) ^ 2 /
        (n : ℝ) ^ (γ * (pairCardThreshold (3 + γ) n δ : ℝ) / 3) := by
  exact veryLargeSumsetEvent_measure_le γ n δ
    (veryLargeSumsetAnalyticBound_of_density_bounds
      hγ_pos hγ_le hc_pos hn hδ_lower hδ_upper)

end

end DenseSetsWithoutLargeSumsets
