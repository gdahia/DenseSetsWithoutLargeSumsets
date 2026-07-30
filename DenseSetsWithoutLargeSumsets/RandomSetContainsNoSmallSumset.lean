/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.FreimanDimension
import DenseSetsWithoutLargeSumsets.Probability
import DenseSetsWithoutLargeSumsets.Common
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.GeneralizedArithmeticProgression
import DenseSetsWithoutLargeSumsets.LargeSumsetsFromMediumSizedSubsets.MediumSizedSubsets
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.Chang.Reduction
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.NumberTheory.Bertrand

/-!
Probability estimates showing that a random set contains no small sumset.
-/

namespace DenseSetsWithoutLargeSumsets

open Nat hiding div_pos
open scoped Pointwise

noncomputable section

def changCarrierBound (k : ℕ) (κ : ℝ) : ℝ := Real.exp (changTheoremExponent κ) * k

lemma exists_zmod_model (n : ℕ) (hn : 0 < n) : ∃ q : ℕ, Nat.Prime q ∧ 2 * n ≤ q ∧ q ≤ 4 * n ∧
    ∃ ψ : ℕ → ZMod q, IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ := by
  obtain ⟨q, hq, hq_gt, hq_le⟩ :=
    exists_prime_lt_and_le_two_mul (2 * n) (Nat.mul_ne_zero (by norm_num) (Nat.ne_of_gt hn))
  refine ⟨q, hq, hq_gt.le, ?_, ?_⟩
  · omega
  · refine ⟨fun x ↦ (x : ZMod q), ?_⟩
    rw [isAddFreimanIso_two]
    constructor
    · apply Set.InjOn.bijOn_image
      intro a ha b hb hab
      rw [ZMod.natCast_eq_natCast_iff'] at hab
      unfold interval at ha hb
      norm_cast at ha hb
      simp only [Finset.mem_Icc] at ha hb
      rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] at hab
      · exact hab
      · omega
      · omega
    · intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂
      norm_cast at ha₁ hb₁ ha₂ hb₂
      unfold interval at ha₁ hb₁ ha₂ hb₂
      simp only [Finset.mem_Icc] at ha₁ hb₁ ha₂ hb₂
      norm_cast
      constructor
      · intro h_image_sum
        rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] at h_image_sum
        · exact h_image_sum
        · omega
        · omega
      · tauto

def ε (γ : ℝ) : ℝ := γ / (4 * (γ + 2))

def κ (C : ℝ) : ℝ := 6 * C ^ (2 : ℕ)

def changExponent (C : ℝ) : ℝ := changTheoremExponent (κ C)

def lowerBltConstant (C γ : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) : ℝ :=
  bltConstant (2 * C) (ε γ) hC hε

def lowerBltConstantDefault (C γ : ℝ) : ℝ :=
  if hC : 0 < 2 * C then
    if hε : 0 < ε γ then lowerBltConstant C γ hC hε else 1
  else 1

lemma lowerBltConstantDefault_eq (C γ : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) :
    lowerBltConstantDefault C γ = lowerBltConstant C γ hC hε := by
  simp [lowerBltConstantDefault, hC, hε]

def lowerConstant (C γ : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) : ℝ :=
  max (Real.exp (changExponent C)) (4 * lowerBltConstant C γ hC hε)

def lowerConstantDefault (C γ : ℝ) : ℝ :=
  max (Real.exp (changExponent C)) (4 * lowerBltConstantDefault C γ)

lemma lowerConstantDefault_eq (C γ : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) :
    lowerConstantDefault C γ = lowerConstant C γ hC hε := by
  simp [lowerConstantDefault, lowerConstant, lowerBltConstantDefault_eq C γ hC hε]

private lemma one_le_lowerBltConstant {C γ : ℝ} (hC : 0 < 2 * C)
    (hε : 0 < ε γ) :
    1 ≤ lowerBltConstant C γ hC hε := by
  simpa [lowerBltConstant] using one_le_bltConstant hC hε

private lemma lowerBltConstant_le_lowerConstant {C γ : ℝ} (hC : 0 < 2 * C)
    (hε : 0 < ε γ) :
    lowerBltConstant C γ hC hε ≤ lowerConstant C γ hC hε := by
  refine le_trans (b := 4 * lowerBltConstant C γ hC hε) ?_
    (le_max_right (Real.exp (changExponent C)) (4 * lowerBltConstant C γ hC hε))
  nlinarith [one_le_lowerBltConstant hC hε]

private lemma one_le_lowerConstant {C γ : ℝ} (hC : 0 < 2 * C) (hε : 0 < ε γ) :
    1 ≤ lowerConstant C γ hC hε := by
  exact (one_le_lowerBltConstant hC hε).trans
    (lowerBltConstant_le_lowerConstant hC hε)

private lemma lowerConstant_eq (C γ : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) :
    lowerConstant C γ hC hε =
      max (Real.exp (changTheoremExponent (κ C)))
        (4 * lowerBltConstant C γ hC hε) := by
  simp [lowerConstant, changExponent]

lemma lowerConstant_pos (C γ : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) : 0 < lowerConstant C γ hC hε :=
  (Real.exp_pos (changExponent C)).trans_le (le_max_left _ _)

def lowerLogScale (γ : ℝ) : ℝ := 8 / ε γ

def lowerSqrtScale (C γ : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) : ℝ :=
  8 * lowerBltConstant C γ hC hε * Real.sqrt 14 / ε γ

def lowerSqrtScaleDefault (C γ : ℝ) : ℝ :=
  8 * lowerBltConstantDefault C γ * Real.sqrt 14 / ε γ

def lowerGapSqrtScaleDefault (C γ c : ℝ) : ℝ :=
  8 * lowerBltConstantDefault C γ *
    Real.sqrt (densityCoefficient (3 + γ) c) / ε γ

private def lowerGapSqrtScale (C γ c : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) : ℝ :=
  8 * lowerBltConstant C γ hC hε *
    Real.sqrt (densityCoefficient (3 + γ) c) / ε γ

lemma lowerSqrtScaleDefault_eq (C γ : ℝ) (hC : 0 < 2 * C) (hε : 0 < ε γ) :
    lowerSqrtScaleDefault C γ = lowerSqrtScale C γ hC hε := by
  simp [lowerSqrtScaleDefault, lowerSqrtScale, lowerBltConstantDefault_eq C γ hC hε]

private lemma lowerGapSqrtScaleDefault_eq (C γ c : ℝ) (hC : 0 < 2 * C)
    (hε : 0 < ε γ) :
    lowerGapSqrtScaleDefault C γ c = lowerGapSqrtScale C γ c hC hε := by
  simp [lowerGapSqrtScaleDefault, lowerGapSqrtScale, lowerBltConstantDefault_eq C γ hC hε]

private lemma lowerLogScale_pos {γ : ℝ} (hε : 0 < ε γ) :
    0 < lowerLogScale γ := by
  rw [lowerLogScale]
  positivity

private lemma lowerGapSqrtScale_pos {C γ c : ℝ} (hC : 0 < 2 * C) (hε : 0 < ε γ)
    (hK : 0 < densityCoefficient (3 + γ) c) :
    0 < lowerGapSqrtScale C γ c hC hε := by
  rw [lowerGapSqrtScale]
  exact div_pos (mul_pos (mul_pos (by norm_num)
    (zero_lt_one.trans_le (one_le_lowerBltConstant hC hε))) (Real.sqrt_pos.2 hK)) hε

def lowerAnalyticThreshold (C γ : ℝ) : ℝ :=
  Real.exp <| max (4 * Real.log (56 : ℝ) + 1) <|
    max (2 * changExponent C) <|
      max (2 * lowerLogScale γ * Real.log (42 * lowerConstantDefault C γ * lowerLogScale γ))
        ((4 * lowerSqrtScaleDefault C γ * Real.log (84 * lowerConstantDefault C γ *
          lowerSqrtScaleDefault C γ)) ^
          (2 : ℕ))

def lowerDensityExponent (C γ : ℝ) : ℝ := min
    ((2 + γ) * ε γ / (12 * C ^ (2 : ℕ)))
    ((2 + γ) / (2 * Real.exp (changContainerExponent (κ C)))) / 2

lemma ε_pos {γ : ℝ} (hγ : 0 < γ) : 0 < ε γ := by
  unfold ε
  positivity

private lemma ε_le_one_twelfth {γ : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) :
    ε γ ≤ 1 / 12 := by
  unfold ε
  refine (div_le_iff₀ ?_).mpr ?_
  · positivity
  · nlinarith

private lemma ε_lt_one_half {γ : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) :
    ε γ < 1 / 2 := by
  refine (ε_le_one_twelfth hγ_pos hγ_le).trans_lt ?_
  norm_num

private lemma half_le_one_sub_ε {γ : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) :
    (1 / 2 : ℝ) ≤ 1 - ε γ := by
  linarith [ε_le_one_twelfth hγ_pos hγ_le]

private lemma one_sub_three_mul_ε_pos {γ : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) :
    0 < 1 - 3 * ε γ := by
  linarith [ε_le_one_twelfth hγ_pos hγ_le]

def lowerSizeThreshold (C γ : ℝ) : ℝ := max (lowerDensityExponent C γ)
    (max 2 (max ((36 * Real.exp (changExponent C)) ^ (2 : ℕ))
      (lowerAnalyticThreshold C γ)))

def lowerGapThreshold (C γ c : ℝ) : ℝ :=
  max (lowerSizeThreshold C γ) <| max
    ((2 * densityCoefficient (3 + γ) c * Real.exp (changExponent C)) ^ (2 : ℕ)) <|
    Real.exp <| max
      (2 * lowerLogScale γ * Real.log
        (max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstantDefault C γ * lowerLogScale γ))
      ((4 * lowerGapSqrtScaleDefault C γ c * Real.log
        (2 * max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstantDefault C γ *
          lowerGapSqrtScaleDefault C γ c)) ^ (2 : ℕ))

private lemma lowerSizeThreshold_le_lowerGapThreshold (C γ c : ℝ) :
    lowerSizeThreshold C γ ≤ lowerGapThreshold C γ c :=
  le_max_left _ _

private lemma two_le_lowerSizeThreshold (C γ : ℝ) : (2 : ℝ) ≤ lowerSizeThreshold C γ := by
  unfold lowerSizeThreshold
  exact (le_max_left (2 : ℝ)
      (max ((36 * Real.exp (changExponent C)) ^ (2 : ℕ)) (lowerAnalyticThreshold C γ))).trans
    (le_max_right (lowerDensityExponent C γ)
      (max 2 (max ((36 * Real.exp (changExponent C)) ^ (2 : ℕ))
        (lowerAnalyticThreshold C γ))))

private lemma old_model_threshold_le_lowerSizeThreshold (C γ : ℝ) :
    ((36 * Real.exp (changExponent C)) ^ (2 : ℕ)) ≤ lowerSizeThreshold C γ := by
  unfold lowerSizeThreshold
  exact (le_max_left ((36 * Real.exp (changExponent C)) ^ (2 : ℕ))
      (lowerAnalyticThreshold C γ)).trans
    ((le_max_right (2 : ℝ)
      (max ((36 * Real.exp (changExponent C)) ^ (2 : ℕ))
        (lowerAnalyticThreshold C γ))).trans
      (le_max_right (lowerDensityExponent C γ)
        (max 2 (max ((36 * Real.exp (changExponent C)) ^ (2 : ℕ))
          (lowerAnalyticThreshold C γ)))))

private lemma lowerAnalyticThreshold_le_lowerSizeThreshold (C γ : ℝ) :
    lowerAnalyticThreshold C γ ≤ lowerSizeThreshold C γ := by
  unfold lowerSizeThreshold
  exact (le_max_right ((36 * Real.exp (changExponent C)) ^ (2 : ℕ))
      (lowerAnalyticThreshold C γ)).trans
    ((le_max_right (2 : ℝ)
      (max ((36 * Real.exp (changExponent C)) ^ (2 : ℕ))
        (lowerAnalyticThreshold C γ))).trans
      (le_max_right (lowerDensityExponent C γ)
        (max 2 (max ((36 * Real.exp (changExponent C)) ^ (2 : ℕ))
          (lowerAnalyticThreshold C γ)))))

private lemma lowerSizeThreshold_lt_nat_pos {C γ : ℝ} {n : ℕ} (_hγ : 0 < γ) (_hC : 0 < C)
    (hn : lowerSizeThreshold C γ < n) : 0 < n := by
  have hnpos : (0 : ℝ) < n := by
    refine lt_of_le_of_lt ?_ hn
    apply le_trans (b := 2)
    · norm_num
    · exact two_le_lowerSizeThreshold C γ
  exact_mod_cast hnpos

def zmodGAPPreimageContainer {q : ℕ} (n : ℕ) (ψ : ℕ → ZMod q)
    (P : ProperGAP (ZMod q)) : Finset ℕ :=
  (interval n).filter fun x => ψ x ∈ (P : Finset (ZMod q))

lemma zmodGAPPreimageContainer_card_le_carrier {q n : ℕ} {ψ : ℕ → ZMod q}
    (P : ProperGAP (ZMod q)) (hψinj : Set.InjOn ψ (interval n : Set ℕ)) :
    (zmodGAPPreimageContainer n ψ P).card ≤ P.carrier.card := by
  rw [← Finset.card_image_of_injOn (f := ψ)]
  · apply Finset.card_le_card
    intro y hy
    rw [Finset.mem_image] at hy
    rcases hy with ⟨x, hx, rfl⟩
    exact (Finset.mem_filter.mp hx).2
  · apply hψinj.mono
    intro x hx
    exact (Finset.mem_filter.mp hx).1

private lemma properGAP_card_eq_one_of_dim_zero {G : Type*} [DecidableEq G] [AddCommMonoid G]
    (P : ProperGAP G) (hPdim : P.dim = 0) : P.carrier.card = 1 := by
  rcases P with ⟨dim, carrier, origin, step, length, length_one_lt, carrier_eq, proper⟩
  dsimp at hPdim ⊢
  subst dim
  rw [carrier_eq]
  simp [gapMap]

private lemma natCastImage_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    natCastImage A ⊆ natCastImage B := by
  intro z hz
  rw [natCastImage] at hz ⊢
  rcases Finset.mem_image.mp hz with ⟨a, ha, rfl⟩
  exact Finset.mem_image.mpr ⟨a, hAB ha, rfl⟩

private lemma natCastImage_filter_mem_eq_of_subset {A : Finset ℕ} {T : Finset ℤ}
    (hT : T ⊆ natCastImage A) :
    natCastImage (A.filter fun a => (a : ℤ) ∈ T) = T := by
  ext z
  constructor
  · intro hz
    rw [natCastImage] at hz
    rcases Finset.mem_image.mp hz with ⟨a, ha, rfl⟩
    rw [Finset.mem_filter] at ha
    exact ha.2
  · intro hz
    rw [natCastImage] at hT ⊢
    rcases Finset.mem_image.mp (hT hz) with ⟨a, haA, rfl⟩
    exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨haA, hz⟩, rfl⟩

private lemma natCastImage_add_subset {A B S : Finset ℕ} {A' B' : Finset ℤ}
    (hA' : A' ⊆ natCastImage A) (hB' : B' ⊆ natCastImage B)
    (hAB : A + B ⊆ S) :
    A' + B' ⊆ natCastImage S := by
  intro z hz
  rw [Finset.mem_add] at hz
  rcases hz with ⟨a, ha, b, hb, rfl⟩
  rcases Finset.mem_image.mp (hA' ha) with ⟨a₀, ha₀, rfl⟩
  rcases Finset.mem_image.mp (hB' hb) with ⟨b₀, hb₀, rfl⟩
  rw [natCastImage]
  refine Finset.mem_image.mpr ⟨a₀ + b₀, hAB (Finset.add_mem_add ha₀ hb₀), ?_⟩
  norm_num

def bltSmallWitnessPairs (P : Finset ℕ) (k : ℕ) (C γ : ℝ) :
    Finset (Finset ℤ × Finset ℤ) :=
  ((natCastImage P).powerset ×ˢ (natCastImage P).powerset).filter fun p =>
    ∃ (hC : 0 < 2 * C) (hε : 0 < ε γ),
      (p.1.card : ℝ) ≤ lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ) ∧
        (p.2.card : ℝ) ≤ lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)

/--
Dimension-aware BLT fingerprints used after Chang is applied to the large BLT subsets.
Only the small fingerprint pair has to lie in the GAP preimage container; the original `k`-sets
need not.
-/
def bltDimSmallWitnessPairs (P : Finset ℕ) (D k : ℕ) (C γ : ℝ) :
    Finset (Finset ℤ × Finset ℤ) := by
  classical
  exact (bltSmallWitnessPairs P k C γ).filter fun p =>
    1 ≤ D ∧ (1 - 3 * ε γ) * (D : ℝ) * (k : ℝ) ≤ ((p.1 + p.2).card : ℝ)

def bltWitnessPairSumsetIsSubset (p : Finset ℤ × Finset ℤ) (S : Finset ℕ) : Prop :=
  p.1 + p.2 ⊆ natCastImage S

def properGAPsZModUpToDim {q : ℕ} (D s : ℕ) (hq : 0 < q) :
    Finset (ProperGAP (ZMod q)) := by
  classical
  exact (Finset.range (D + 1)).biUnion fun d => properGAPsZModOfDim d s hq

lemma mem_properGAPsZModUpToDim {q D s : ℕ} (hq : 0 < q) {P : ProperGAP (ZMod q)} :
    P ∈ properGAPsZModUpToDim D s hq ↔ P.dim ≤ D ∧ P.carrier.card ≤ s := by
  simp [properGAPsZModUpToDim, properGAPsZModOfDim, properGAPsZModOfDimSet]

lemma mem_properGAPsZModOfDim {q d s : ℕ} (hq : 0 < q) {P : ProperGAP (ZMod q)} :
    P ∈ properGAPsZModOfDim d s hq ↔ P.dim = d ∧ P.carrier.card ≤ s := by
  simp [properGAPsZModOfDim, properGAPsZModOfDimSet]

private def subsetsUpToCard {α : Type*} [DecidableEq α] (U : Finset α) (M : ℕ) :
    Finset (Finset α) :=
  U.powerset.filter fun A => A.card ≤ M

private lemma mem_subsetsUpToCard {α : Type*} [DecidableEq α] {U A : Finset α} {M : ℕ} :
    A ∈ subsetsUpToCard U M ↔ A ⊆ U ∧ A.card ≤ M := by
  rw [subsetsUpToCard, Finset.mem_filter]
  constructor
  · intro h
    exact ⟨Finset.mem_powerset.mp h.1, h.2⟩
  · intro h
    exact ⟨Finset.mem_powerset.mpr h.1, h.2⟩

private lemma subsetsUpToCard_card_le {α : Type*} [DecidableEq α] (U : Finset α) (M : ℕ) :
    (subsetsUpToCard U M).card ≤ (M + 1) * (U.card + 1) ^ M := by
  classical
  refine (Finset.card_le_card (s := subsetsUpToCard U M)
    (t := (Finset.range (M + 1)).biUnion fun i => U.powersetCard i) ?_).trans ?_
  · intro A hA
    rw [Finset.mem_biUnion]
    rw [mem_subsetsUpToCard] at hA
    exact ⟨A.card, Finset.mem_range.mpr (Nat.lt_succ_of_le hA.2),
      Finset.mem_powersetCard.mpr ⟨hA.1, rfl⟩⟩
  · refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_sum (s := Finset.range (M + 1))
      (f := fun i => (U.powersetCard i).card)
      (g := fun _ => (U.card + 1) ^ M) ?_).trans_eq ?_
    · intro i hi
      rw [Finset.card_powersetCard]
      exact (Nat.choose_le_pow U.card i).trans
        ((Nat.pow_le_pow_left (Nat.le_succ U.card) i).trans
          (Nat.pow_le_pow_right (Nat.succ_pos U.card)
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))))
    · simp

private lemma bltDimSmallWitnessPairs_card_le (P : Finset ℕ) (D k : ℕ) (C γ : ℝ)
    (hC : 0 < 2 * C) (hε : 0 < ε γ) :
    (bltDimSmallWitnessPairs P D k C γ).card ≤
      (((⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1) *
          ((natCastImage P).card + 1) ^
            ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊) *
        ((⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1) *
          ((natCastImage P).card + 1) ^
            ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊)) := by
  classical
  refine (Finset.card_le_card (s := bltDimSmallWitnessPairs P D k C γ)
    (t := subsetsUpToCard (natCastImage P)
        ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ ×ˢ
      subsetsUpToCard (natCastImage P)
        ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊) ?_).trans ?_
  · intro p hp
    rw [bltDimSmallWitnessPairs, Finset.mem_filter] at hp
    rw [bltSmallWitnessPairs, Finset.mem_filter] at hp
    rcases hp with ⟨⟨hprod, hC', hε', hp₁, hp₂⟩, _⟩
    have hceil :
        lowerBltConstant C γ hC' hε' * Real.sqrt (k : ℝ) ≤
          (⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ : ℝ) := by
      simpa [lowerBltConstant] using
        Nat.le_ceil (lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ))
    rw [Finset.mem_product] at hprod
    rw [Finset.mem_product]
    constructor
    · rw [mem_subsetsUpToCard]
      refine ⟨Finset.mem_powerset.mp hprod.1, ?_⟩
      exact_mod_cast hp₁.trans hceil
    · rw [mem_subsetsUpToCard]
      refine ⟨Finset.mem_powerset.mp hprod.2, ?_⟩
      exact_mod_cast hp₂.trans hceil
  · rw [Finset.card_product]
    apply Nat.mul_le_mul
    · apply subsetsUpToCard_card_le
    · apply subsetsUpToCard_card_le

private lemma intToNat_injOn_of_subset_natCastImage {T : Finset ℤ} {S : Finset ℕ}
    (hT : T ⊆ natCastImage S) :
    Set.InjOn Int.toNat (T : Set ℤ) := by
  intro z hz w hw hzw
  rw [natCastImage] at hT
  rcases Finset.mem_image.mp (hT hz) with ⟨a, _ha, haz⟩
  rcases Finset.mem_image.mp (hT hw) with ⟨b, _hb, hbw⟩
  rw [← haz, ← hbw] at hzw ⊢
  simpa using hzw

private lemma bltWitnessPairSumsetIsSubset_subset_natSuperset
    (p : Finset ℤ × Finset ℤ) :
    {S : Finset ℕ | bltWitnessPairSumsetIsSubset p S} ⊆
      {S : Finset ℕ | (p.1 + p.2).image Int.toNat ⊆ S} := by
  intro S hS x hx
  rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
  change p.1 + p.2 ⊆ natCastImage S at hS
  rw [natCastImage] at hS
  rcases Finset.mem_image.mp (hS hz) with ⟨s, hs, hsz⟩
  rw [← hsz]
  simpa using hs

lemma bltWitnessPair_probability_le (n : ℕ) {δ : unitInterval}
    (p : Finset ℤ × Finset ℤ) :
    (binomialFinsetSubset (Set.Icc 1 n) δ).real
        {S : Finset ℕ | bltWitnessPairSumsetIsSubset p S} ≤
      (δ : ℝ) ^ (p.1 + p.2).card := by
  classical
  by_cases hnonempty : ∃ S : Finset ℕ, bltWitnessPairSumsetIsSubset p S
  · rcases hnonempty with ⟨S₀, hS₀⟩
    refine le_trans (b := (binomialFinsetSubset (Set.Icc 1 n) δ).real
      {S : Finset ℕ | (p.1 + p.2).image Int.toNat ⊆ S}) ?_ ?_
    · rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def]
      apply ENNReal.toReal_mono
      · exact MeasureTheory.measure_ne_top (binomialFinsetSubset (Set.Icc 1 n) δ) _
      · apply MeasureTheory.measure_mono
        simpa using bltWitnessPairSumsetIsSubset_subset_natSuperset p
    · refine (binomialFinsetSubset_real_superset_nat
        (Ω := Set.Icc 1 n) (p := δ) (Set.finite_Icc 1 n)
        (T := (p.1 + p.2).image Int.toNat)).trans_eq ?_
      rw [Finset.card_image_of_injOn (intToNat_injOn_of_subset_natCastImage hS₀)]
  · refine le_trans (b := 0) ?_ (pow_nonneg (unitInterval.nonneg δ) _)
    apply le_of_eq
    rw [MeasureTheory.measureReal_def]
    rw [ENNReal.toReal_eq_zero_iff]
    left
    rw [MeasureTheory.measure_eq_zero_iff_ae_notMem]
    filter_upwards with S hS
    exact hnonempty ⟨S, hS⟩

private lemma unitInterval_pow_le_exp_neg_mul_log_inv {δ : unitInterval} {m : ℕ} {L : ℝ}
    (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) (hL : L ≤ (m : ℝ)) :
    (δ : ℝ) ^ m ≤ Real.exp (-L * Real.log (1 / δ)) := by
  rw [← Real.exp_log (pow_pos hδ_pos m), Real.log_pow, mul_comm]
  refine (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hL ?_)).trans_eq ?_
  · rw [← Real.log_one]
    exact Real.log_le_log hδ_pos hδ_lt.le
  · rw [Real.log_div one_ne_zero (Ne.symm (ne_of_lt hδ_pos)), Real.log_one, zero_sub]
    ring_nf

private lemma bltDimSmallWitnessPairs_probability_sum_le (P : Finset ℕ) (D k : ℕ)
    (C γ : ℝ) {δ : unitInterval} (hC : 0 < 2 * C) (hε : 0 < ε γ)
    (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) :
    ∑ p ∈ bltDimSmallWitnessPairs P D k C γ, (δ : ℝ) ^ (p.1 + p.2).card ≤
      (((⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1) *
          ((natCastImage P).card + 1) ^
            ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ : ℝ) *
        ((⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1) *
          ((natCastImage P).card + 1) ^
            ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ : ℝ)) *
        Real.exp (-((1 - 3 * ε γ) * (D : ℝ) * (k : ℝ)) * Real.log (1 / δ)) := by
  classical
  refine (Finset.sum_le_sum (s := bltDimSmallWitnessPairs P D k C γ)
    (f := fun p => (δ : ℝ) ^ (p.1 + p.2).card)
    (g := fun _ => Real.exp (-((1 - 3 * ε γ) * (D : ℝ) * (k : ℝ)) *
      Real.log (1 / δ))) ?_).trans ?_
  · intro p hp
    rw [bltDimSmallWitnessPairs, Finset.mem_filter] at hp
    exact unitInterval_pow_le_exp_neg_mul_log_inv hδ_pos hδ_lt hp.2.2
  · rw [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast bltDimSmallWitnessPairs_card_le P D k C γ hC hε
    · positivity

private lemma sum_union_le_sum_add_sum {α : Type*} [DecidableEq α] (A B : Finset α)
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ A ∪ B, f x ≤ ∑ x ∈ A, f x + ∑ x ∈ B, f x := by
  classical
  refine le_trans (b := ∑ x ∈ A ∪ (B \ A), f x) ?_ ?_
  · apply le_of_eq
    congr 1
    ext x
    by_cases hxA : x ∈ A <;> simp [hxA]
  · rw [Finset.sum_union]
    · apply add_le_add_right
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        exact (Finset.mem_sdiff.mp hx).1
      · intro x _hxB _hxsdiff
        exact hf x
    · rw [Finset.disjoint_iff_inter_eq_empty]
      ext x
      simp

private lemma sum_biUnion_le_sum {α β : Type*} [DecidableEq β] (s : Finset α)
    (t : α → Finset β) (f : β → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ a ∈ s, ∑ x ∈ t a, f x := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    rw [Finset.biUnion_insert]
    refine (sum_union_le_sum_add_sum (t a) (s.biUnion t) f hf).trans ?_
    refine (add_le_add_right ih _).trans_eq ?_
    rw [Finset.sum_insert ha]

private lemma dim_fingerprint_sum_le_gap_dim_sum {q n k s : ℕ} (ψ : ℕ → ZMod q)
    (hqpos : 0 < q) (hψinj : Set.InjOn ψ (interval n : Set ℕ))
    {C γ : ℝ} {δ : unitInterval} (hC : 0 < 2 * C) (hε : 0 < ε γ)
    (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) :
    ∑ P ∈ (by
        classical
        exact (Finset.Icc 1 k).biUnion (fun d => properGAPsZModOfDim d s hqpos) :
        Finset (ProperGAP (ZMod q))),
        ∑ p ∈ bltDimSmallWitnessPairs (zmodGAPPreimageContainer n ψ P) P.dim k C γ,
          (δ : ℝ) ^ (p.1 + p.2).card ≤
      ∑ d ∈ Finset.Icc 1 k,
        ((properGAPsZModOfDim d s hqpos).card : ℝ) *
          (((⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1) *
              (s + 1) ^
                ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ : ℝ) *
            ((⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1) *
              (s + 1) ^
                ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ : ℝ)) *
          Real.exp (-((1 - 3 * ε γ) * (d : ℝ) * (k : ℝ)) * Real.log (1 / δ)) := by
  classical
  refine (sum_biUnion_le_sum (Finset.Icc 1 k)
    (fun d => properGAPsZModOfDim d s hqpos)
    (fun P => ∑ p ∈ bltDimSmallWitnessPairs
      (zmodGAPPreimageContainer n ψ P) P.dim k C γ,
        (δ : ℝ) ^ (p.1 + p.2).card)
    ?_).trans ?_
  · intro P
    apply Finset.sum_nonneg'
    intro p
    exact pow_nonneg (unitInterval.nonneg δ) (p.1 + p.2).card
  refine Finset.sum_le_sum ?_
  intro d _hd
  refine (Finset.sum_le_sum (s := properGAPsZModOfDim d s hqpos)
    (f := fun P => ∑ p ∈ bltDimSmallWitnessPairs
      (zmodGAPPreimageContainer n ψ P) P.dim k C γ,
        (δ : ℝ) ^ (p.1 + p.2).card)
    (g := fun _ =>
      (((⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1) *
          (s + 1) ^
            ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ : ℝ) *
        ((⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1) *
          (s + 1) ^
            ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ : ℝ)) *
        Real.exp (-((1 - 3 * ε γ) * (d : ℝ) * (k : ℝ)) * Real.log (1 / δ))) ?_).trans_eq ?_
  · intro P hP
    refine (bltDimSmallWitnessPairs_probability_sum_le
      (zmodGAPPreimageContainer n ψ P) P.dim k C γ hC hε hδ_pos hδ_lt).trans ?_
    rw [((mem_properGAPsZModOfDim hqpos).1 hP).1]
    have hbase :
        (natCastImage (zmodGAPPreimageContainer n ψ P)).card + 1 ≤ s + 1 := by
      rw [natCastImage_card]
      exact Nat.succ_le_succ
        ((zmodGAPPreimageContainer_card_le_carrier P hψinj).trans
          ((mem_properGAPsZModOfDim hqpos).1 hP).2)
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast Nat.mul_le_mul
        (Nat.mul_le_mul_left
          (⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1)
          (Nat.pow_le_pow_left hbase
            ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊))
        (Nat.mul_le_mul_left
          (⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1)
          (Nat.pow_le_pow_left hbase
            ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊))
    · positivity
  · rw [Finset.sum_const, nsmul_eq_mul]
    ring

private lemma card_add_self_le_sq_mul {G : Type*} [DecidableEq G] [AddCommGroup G]
    {A B : Finset G} {k : ℕ} {C : ℝ} (hk : k ≠ 0)
    (_hAcard : A.card = k) (hBcard : B.card = k) (hAB : (A + B).card ≤ C * k) :
    (A + A).card ≤ C ^ 2 * k := by
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have hratio : ((A + B).card : ℝ) / k ≤ C := by
    refine (div_le_iff₀ ?_).mpr hAB
    exact_mod_cast hkpos
  have hratio_nonneg : 0 ≤ ((A + B).card : ℝ) / k := by positivity
  refine le_trans
    (b := (((A + B).card : ℝ) / k) ^ 2 * k) ?_ ?_
  · rw [← two_nsmul A]
    have hplu :
        ((2 • A).card : ℚ≥0) ≤ (((A + B).card : ℚ≥0) / k) ^ 2 * k := by
      rw [← hBcard, add_comm]
      apply Finset.pluennecke_ruzsa_inequality_nsmul_add
      rw [← Finset.card_pos, hBcard]
      exact hkpos
    simpa using (NNRat.cast_le (K := ℝ)).mpr hplu
  · apply mul_le_mul_of_nonneg_right
    · nlinarith [mul_nonneg (sub_nonneg.mpr hratio)
        (add_nonneg (hratio_nonneg.trans hratio) hratio_nonneg)]
    · positivity

/--
Pluennecke-Ruzsa input for the small-sumset argument: two `k`-sets with small mixed sumset
have a union whose self-sumset has cardinality at most `κ C * k`.
-/
lemma card_union_add_union_le_κ_mul {G : Type*} [DecidableEq G] [AddCommGroup G]
    {A B : Finset G} {k : ℕ} {C : ℝ}
    (hAcard : A.card = k) (hBcard : B.card = k) (hAB : (A + B).card ≤ C * k) :
    ((A ∪ B) + (A ∪ B)).card ≤ κ C * k := by
  by_cases hk : k = 0
  · rw [hk] at hAcard hBcard ⊢
    rw [Finset.card_eq_zero] at hAcard hBcard
    simp [hAcard, hBcard]
  · rw [Finset.union_add, Finset.add_union, Finset.add_union, add_comm B A]
    simp only [Finset.union_assoc, Finset.union_left_idem]
    refine le_trans (b := ((A + A).card : ℝ) + (A + B).card + (B + B).card) ?_ ?_
    · norm_cast
      simpa only [Finset.union_assoc] using
        (Finset.card_union_le ((A + A) ∪ (A + B)) (B + B)).trans
          (Nat.add_le_add_right (Finset.card_union_le (A + A) (A + B)) (B + B).card)
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hk_le_sum : k ≤ (A + B).card := by
      rw [← hAcard]
      apply Finset.card_le_card_add_right
      apply Finset.card_pos.mp
      rw [hBcard]
      exact hkpos
    have hCone : (1 : ℝ) ≤ C := by
      nlinarith [(by exact_mod_cast hkpos : (0 : ℝ) < k),
        (by exact_mod_cast hk_le_sum : (k : ℝ) ≤ (A + B).card), hAB]
    have hBB : ((B + B).card : ℝ) ≤ C ^ 2 * k := by
      exact_mod_cast card_add_self_le_sq_mul (A := B) (B := A) hk hBcard hAcard
        (by simpa [add_comm] using hAB)
    rw [κ]
    nlinarith [hCone, card_add_self_le_sq_mul (A := A) (B := B) hk hAcard hBcard hAB,
      hBB, hAB]

private lemma card_large_subset_union_add_union_le_κ_mul_card
    {G : Type*} [DecidableEq G] [AddCommGroup G]
    {A B A₀ B₀ : Finset G} {k : ℕ} {C : ℝ}
    (hA₀A : A₀ ⊆ A) (hB₀B : B₀ ⊆ B)
    (hAcard : A.card = k) (hBcard : B.card = k)
    (hAB : (A + B).card ≤ C * k)
    (hXlower : (k : ℝ) / 2 ≤ ((A₀ ∪ B₀).card : ℝ))
    (hC_one : 1 ≤ C) :
    (((A₀ ∪ B₀) + (A₀ ∪ B₀)).card : ℝ) ≤
      κ C * ((A₀ ∪ B₀).card : ℝ) := by
  by_cases hk : k = 0
  · rw [hk] at hAcard hBcard
    simp [
      Finset.card_eq_zero.mp
        (Nat.eq_zero_of_le_zero (by simpa [hAcard] using Finset.card_le_card hA₀A)),
      Finset.card_eq_zero.mp
        (Nat.eq_zero_of_le_zero (by simpa [hBcard] using Finset.card_le_card hB₀B))]
  · refine le_trans
      (b := ((A + A).card : ℝ) + (A + B).card + (B + B).card) ?_ ?_
    · exact_mod_cast ((Finset.card_le_card (by
        intro x hx
        rw [Finset.mem_add] at hx
        rcases hx with ⟨a, ha, b, hb, rfl⟩
        rw [Finset.mem_union] at ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · simp [Finset.add_mem_add (hA₀A ha) (hA₀A hb)]
        · simp [Finset.add_mem_add (hA₀A ha) (hB₀B hb)]
        · simp [(by
            simpa [add_comm] using
              (Finset.add_mem_add (hA₀A hb) (hB₀B ha) : b + a ∈ A + B) :
            a + b ∈ A + B)]
        · simp [Finset.add_mem_add (hB₀B ha) (hB₀B hb)])).trans
          ((Finset.card_union_le ((A + A) ∪ (A + B)) (B + B)).trans
            (Nat.add_le_add_right (Finset.card_union_le (A + A) (A + B)) (B + B).card)))
    · refine le_trans (b := C ^ 2 * k + C * k + C ^ 2 * k) ?_ ?_
      · nlinarith [card_add_self_le_sq_mul hk hAcard hBcard hAB,
          hAB, card_add_self_le_sq_mul hk hBcard hAcard
            (by simpa [add_comm] using hAB)]
      · refine le_trans (b := 3 * C ^ 2 * k) ?_ ?_
        · nlinarith [sq_nonneg C, hC_one]
        · refine (by nlinarith [sq_nonneg C] :
            3 * C ^ 2 * k ≤ 6 * C ^ 2 * ((A₀ ∪ B₀).card : ℝ)).trans_eq ?_
          rw [κ]

private lemma choose_succ_two_le_sq (r : ℕ) :
    Nat.choose (r + 1) 2 ≤ r * r := by
  rw [Nat.choose_two_right]
  apply Nat.div_le_of_le_mul
  rw [Nat.add_sub_cancel]
  nlinarith

private lemma choose_succ_two_le_add_pred_mul {r a b : ℕ}
    (hr : 1 ≤ r) (hrb : r ≤ b) (hba : b ≤ a) :
    Nat.choose (r + 1) 2 ≤ a + (r - 1) * b := by
  refine (choose_succ_two_le_sq r).trans ?_
  refine (Nat.mul_le_mul_left r hrb).trans ?_
  rw [← Nat.sub_add_cancel hr]
  rw [Nat.add_mul, one_mul]
  rw [add_comm ((r - 1) * b) b]
  exact Nat.add_le_add_right hba ((r - 1) * b)

private lemma asym_large_subsets_sum_lower
    {G : Type*} [DecidableEq G] [AddCommMonoid G]
    {A B : Finset G} {r k : ℕ} {ε : ℝ}
    (hr : 1 ≤ r) (hA : A.Nonempty) (hB : B.Nonempty)
    (hBA : B.card ≤ A.card) (hdim : freimanDim (A ∪ B) = r)
    (_hε_nonneg : 0 ≤ ε) (hε_le_half : ε ≤ 1 / 2)
    (hr_le_εk : (r : ℝ) ≤ ε * (k : ℝ))
    (hA_large : (1 - ε) * (k : ℝ) ≤ (A.card : ℝ))
    (hB_large : (1 - ε) * (k : ℝ) ≤ (B.card : ℝ)) :
    (1 - 2 * ε) * (r : ℝ) * (k : ℝ) ≤ ((A + B).card : ℝ) := by
  refine (by
    rw [Nat.cast_sub hr]
    norm_num
    nlinarith [hA_large, hB_large,
      (by exact_mod_cast hr : (1 : ℝ) ≤ (r : ℝ)),
      (by
        nlinarith [
          (by exact_mod_cast choose_succ_two_le_sq r :
            (Nat.choose (r + 1) 2 : ℝ) ≤ (r : ℝ) * (r : ℝ)),
          mul_le_mul_of_nonneg_left hr_le_εk (by positivity : 0 ≤ (r : ℝ))] :
        (Nat.choose (r + 1) 2 : ℝ) ≤ ε * (r : ℝ) * (k : ℝ))] :
    (1 - 2 * ε) * (r : ℝ) * (k : ℝ) ≤
      (A.card : ℝ) + ((r - 1 : ℕ) : ℝ) * (B.card : ℝ) -
        (Nat.choose (r + 1) 2 : ℝ)).trans ?_
  rw [← Nat.cast_mul, ← Nat.cast_add]
  rw [← Nat.cast_sub (choose_succ_two_le_add_pred_mul hr
    (by
      exact_mod_cast (by nlinarith : (r : ℝ) ≤ (B.card : ℝ)) : r ≤ B.card)
    hBA)]
  exact_mod_cast card_add_lower_bound_of_freimanDim_union (G := G) r A B hr hA hB hBA hdim

private lemma mul_log_Ax_le_self_of_two_mul_log {A T x : ℝ}
    (hA : 0 < A) (hT : 0 < T) (hx : 0 < x)
    (hmain : 2 * T * Real.log (A * T) ≤ x) :
    T * Real.log (A * x) ≤ x := by
  rw [← mul_div_cancel_left₀ x hT.ne', mul_div_assoc]
  apply mul_le_mul_of_nonneg_left
  · rw [← mul_assoc]
    rw [Real.log_mul (by positivity) (by positivity)]
    nlinarith [log_le_half_self (div_pos hx hT),
      (by
        rw [div_div, mul_comm T 2]
        rw [le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hT)]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmain :
        Real.log (A * T) ≤ (x / T) / 2)]
  · exact hT.le

private lemma lower_log_le_quarter_self_of_sixteen_le {x : ℝ} (hx : 16 ≤ x) :
    Real.log x ≤ x / 4 := by
  refine (by
    have hlog_eq : Real.log x = 2 * Real.log (Real.sqrt x) := by
      nth_rw 1 [← Real.sq_sqrt (by nlinarith : 0 ≤ x)]
      rw [Real.log_pow]
      norm_num
    rw [hlog_eq]
    nlinarith [log_le_half_self (Real.sqrt_pos.2 (by nlinarith : 0 < x))] :
    Real.log x ≤ Real.sqrt x).trans ?_
  rw [Real.sqrt_le_left (by nlinarith : 0 ≤ x / 4)]
  nlinarith [mul_nonneg (by nlinarith : 0 ≤ x) (by nlinarith : 0 ≤ x - 16)]

private lemma log_fiftysix_gt_seven_div_two : (7 / 2 : ℝ) < Real.log (56 : ℝ) := by
  have h56 := Real.log_mul (by norm_num : (8 : ℝ) ≠ 0)
    (by norm_num : (7 : ℝ) ≠ 0)
  have h8 := Real.log_pow (2 : ℝ) 3
  norm_num at h56 h8
  nlinarith [h56, h8, Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1),
    Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 6)]

private lemma log_eightyfour_gt_four : (4 : ℝ) < Real.log (84 : ℝ) := by
  have h84 := Real.log_mul (by norm_num : (7 : ℝ) ≠ 0)
    (by norm_num : (12 : ℝ) ≠ 0)
  have h12 := Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
    (by norm_num : (4 : ℝ) ≠ 0)
  have h7prod := Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
    (by norm_num : (7 / 4 : ℝ) ≠ 0)
  have h4pow := Real.log_pow (2 : ℝ) 2
  norm_num at h84 h12 h7prod h4pow
  have h7 : (62 / 33 : ℝ) < Real.log 7 := by
    nlinarith [h7prod, h4pow,
      Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1),
      Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
  have h4 : (4 / 3 : ℝ) < Real.log 4 := by
    nlinarith [h4pow,
      Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1)]
  nlinarith [h84, h12, h7, h4,
    Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1)]

private lemma fifteen_lt_log_of_lowerAnalyticThreshold {C γ : ℝ} {n : ℕ}
    (hn : lowerSizeThreshold C γ < n) :
    (15 : ℝ) < Real.log (n : ℝ) := by
  refine (by nlinarith [log_fiftysix_gt_seven_div_two] :
    (15 : ℝ) < 4 * Real.log (56 : ℝ) + 1).trans ?_
  rw [← Real.log_exp (4 * Real.log (56 : ℝ) + 1)]
  apply Real.log_lt_log (Real.exp_pos _)
  exact (Real.exp_le_exp.mpr (le_max_left _ _)).trans_lt
    ((lowerAnalyticThreshold_le_lowerSizeThreshold C γ).trans_lt hn)

private lemma pairCardThreshold_pos_of_density {τ : ℝ} {n : ℕ} {δ : unitInterval}
    (hτ : 0 < τ) (hδ : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) (hn : 1 < n) :
    0 < pairCardThreshold τ n δ := by
  rw [pairCardThreshold, Nat.ceil_pos]
  apply div_pos
  · apply mul_pos
    · exact hτ
    · apply Real.log_pos
      exact_mod_cast hn
  · apply Real.log_pos
    rw [one_lt_div hδ]
    exact hδ_lt

private lemma one_lt_densityCoefficient {γ c : ℝ} (hγ_pos : 0 < γ)
    (hc_pos : 0 < c) (hc_lt : c < 1) :
    1 < densityCoefficient (3 + γ) c :=
  densityCoefficient_gt_one (by linarith) hc_pos hc_lt

private lemma one_le_lowerGapSqrtScale {C γ c : ℝ} (hγ_pos : 0 < γ)
    (hγ_le : γ ≤ 1) (hC : 0 < 2 * C) (hε : 0 < ε γ)
    (hc_pos : 0 < c) (hc_lt : c < 1) :
    1 ≤ lowerGapSqrtScale C γ c hC hε := by
  rw [lowerGapSqrtScale, le_div_iff₀ hε]
  have hsqrt : 1 ≤ Real.sqrt (densityCoefficient (3 + γ) c) := by
    rw [Real.one_le_sqrt]
    exact (one_lt_densityCoefficient hγ_pos hc_pos hc_lt).le
  nlinarith [one_le_lowerBltConstant hC hε,
    ε_le_one_twelfth hγ_pos hγ_le,
    mul_nonneg (by nlinarith [one_le_lowerBltConstant hC hε] :
      0 ≤ lowerBltConstant C γ hC hε - 1)
      (by nlinarith [hsqrt] : 0 ≤ Real.sqrt (densityCoefficient (3 + γ) c) - 1)]

private lemma κ_ge_six_of_one_le {C : ℝ} (hC : 1 ≤ C) : 6 ≤ κ C := by
  unfold κ
  nlinarith [sq_nonneg (C - 1)]

private lemma two_le_κ_of_one_le {C : ℝ} (hC : 1 ≤ C) : 2 ≤ κ C := by
  exact (by norm_num : (2 : ℝ) ≤ 6).trans (κ_ge_six_of_one_le hC)

private lemma one_lt_κ_of_one_le {C : ℝ} (hC : 1 ≤ C) : 1 < κ C := by
  exact (by norm_num : (1 : ℝ) < 6).trans_le (κ_ge_six_of_one_le hC)

private lemma chang_size_threshold_pos (C : ℝ) :
    0 < Real.exp (changContainerExponent (κ C)) :=
  Real.exp_pos _

private lemma lowerDensityExponent_pos_of_one_le {C γ : ℝ} (hγ : 0 < γ) (hC : 1 ≤ C) :
    0 < lowerDensityExponent C γ := by
  unfold lowerDensityExponent
  apply div_pos
  · apply lt_min
    · apply div_pos
      · apply mul_pos
        · linarith
        · exact ε_pos hγ
      · apply mul_pos
        · norm_num
        · apply sq_pos_of_pos
          exact zero_lt_one.trans_le hC
    · apply div_pos
      · linarith
      · positivity
  · norm_num

private lemma lowerDensityExponent_le_first_component_half (C γ : ℝ) :
    lowerDensityExponent C γ ≤ (((2 + γ) * ε γ) / (12 * C ^ (2 : ℕ))) / 2 := by
  unfold lowerDensityExponent
  apply div_le_div_of_nonneg_right
  · apply min_le_left
  · norm_num

private lemma lowerDensityExponent_le_second_component_half (C γ : ℝ) :
    lowerDensityExponent C γ ≤
      ((2 + γ) / (2 * Real.exp (changContainerExponent (κ C)))) / 2 := by
  unfold lowerDensityExponent
  apply div_le_div_of_nonneg_right
  · apply min_le_right
  · norm_num

private lemma one_le_sumset_card_coefficient_of_small_pair_sumset
    {G : Type*} [DecidableEq G] [Add G]
    [IsRightCancelAdd G]
    {A B : Finset G} {k : ℕ} {C : ℝ}
    (hk : 0 < k) (hAcard : A.card = k) (hBcard : B.card = k)
    (hAB : (A + B).card ≤ C * k) : 1 ≤ C := by
  nlinarith [hAB,
    (by
      exact_mod_cast (by
        rw [← hAcard]
        exact Finset.card_le_card_add_right
          (Finset.card_pos.mp (by rw [hBcard]; exact hk)) :
          k ≤ (A + B).card) :
          (k : ℝ) ≤ (A + B).card),
    (by exact_mod_cast hk : (0 : ℝ) < k)]

private lemma freiman_image_sum_card {G H : Type*} [DecidableEq G] [DecidableEq H]
    [AddCommMonoid G] [AddCommMonoid H]
    {X A B : Finset G} {Y : Set H} {f : G → H}
    (hiso : IsAddFreimanIso 2 (X : Set G) Y f)
    (hAX : A ⊆ X) (hBX : B ⊆ X) :
    (A.image f + B.image f).card = (A + B).card := by
  classical
  refine Eq.trans (b := ((A ×ˢ B).image (fun p : G × G => f p.1 + f p.2)).card) ?_ ?_
  · apply congrArg Finset.card
    ext y
    constructor
    · intro hy
      rw [Finset.mem_add] at hy
      obtain ⟨a', ha', b', hb', rfl⟩ := hy
      rw [Finset.mem_image] at ha' hb'
      obtain ⟨a, ha, rfl⟩ := ha'
      obtain ⟨b, hb, rfl⟩ := hb'
      exact Finset.mem_image.2 ⟨(a, b), by simp [ha, hb], by simp⟩
    · intro hy
      rw [Finset.mem_image] at hy
      obtain ⟨p, hp, rfl⟩ := hy
      rw [Finset.mem_product] at hp
      rw [Finset.mem_add]
      exact ⟨f p.1, Finset.mem_image.2 ⟨p.1, hp.1, rfl⟩,
        f p.2, Finset.mem_image.2 ⟨p.2, hp.2, rfl⟩, rfl⟩
  · refine Eq.trans
      (b := ((A ×ˢ B).image (fun p : G × G => p.1 + p.2)).card) ?_ ?_
    · apply card_image_eq_of_kernel_iff
      intro x hx y hy
      rw [Finset.mem_product] at hx hy
      exact hiso.add_eq_add (hAX hx.1) (hBX hx.2) (hAX hy.1) (hBX hy.2)
    · apply (congrArg Finset.card ?_).symm
      ext x
      constructor
      · intro hx
        rw [Finset.mem_add] at hx
        obtain ⟨a, ha, b, hb, rfl⟩ := hx
        exact Finset.mem_image.2 ⟨(a, b), by simp [ha, hb], rfl⟩
      · intro hx
        rw [Finset.mem_image] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        rw [Finset.mem_product] at hp
        rw [Finset.mem_add]
        exact ⟨p.1, hp.1, p.2, hp.2, rfl⟩

private lemma one_div_unitInterval_lt_rpow_lowerDensityExponent {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hn_pos : 0 < n) (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) :
    1 / (δ : ℝ) < (n : ℝ) ^ (lowerDensityExponent C γ) := by
  rw [Real.rpow_neg (le_of_lt (by exact_mod_cast hn_pos : 0 < (n : ℝ)))] at hδ_lower
  simpa [one_div] using
    one_div_lt_one_div_of_lt (inv_pos.mpr
      (Real.rpow_pos_of_pos (by exact_mod_cast hn_pos : 0 < (n : ℝ)) _)) hδ_lower

private lemma log_one_div_unitInterval_lt_lowerDensityExponent_mul_log {γ C : ℝ} {n : ℕ} {δ :
  unitInterval}
    (hn_pos : 0 < n) (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) :
    Real.log (1 / δ) < lowerDensityExponent C γ * Real.log (n : ℝ) := by
  refine (Real.log_lt_log (by
    apply div_pos
    · norm_num
    · exact (Real.rpow_pos_of_pos (by exact_mod_cast hn_pos : 0 < (n : ℝ)) _).trans hδ_lower)
    (one_div_unitInterval_lt_rpow_lowerDensityExponent hn_pos hδ_lower)).trans_eq ?_
  rw [Real.log_rpow (by exact_mod_cast hn_pos : 0 < (n : ℝ))]

private lemma log_one_div_unitInterval_pos {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hn_pos : 0 < n) (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ))
    (hδ_upper : (δ : ℝ) < 1) :
    0 < Real.log (1 / δ) := by
  apply Real.log_pos
  rw [one_lt_div (by
    exact (Real.rpow_pos_of_pos (by exact_mod_cast hn_pos : 0 < (n : ℝ)) _).trans hδ_lower)]
  linarith

private lemma pairCardThreshold_arg_le {γ : ℝ} {n : ℕ} {δ : unitInterval} :
    (3 + γ) * Real.log (n : ℝ) / Real.log (1 / δ) ≤
      (pairCardThreshold (3 + γ) n δ : ℝ) := by
  rw [pairCardThreshold]
  apply Nat.le_ceil

private lemma lowerDensityExponent_le_gamma_div_ninetysix_sq {C γ : ℝ}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) :
    lowerDensityExponent C γ ≤ γ / (96 * C ^ (2 : ℕ)) := by
  refine (lowerDensityExponent_le_first_component_half C γ).trans_eq ?_
  unfold ε
  field_simp [(sq_pos_of_pos (zero_lt_one.trans_le hC_one)).ne', (by linarith : γ + 2 ≠ 0)]
  ring

private lemma two_mul_ceil_κ_sub_one_pos {C : ℝ} (hC_one : 1 ≤ C) :
    0 < 2 * ⌈κ C⌉₊ - 1 := by
  apply Nat.sub_pos_of_lt
  exact_mod_cast (by
    nlinarith [(κ_ge_six_of_one_le hC_one).trans (Nat.le_ceil (κ C))] :
    (1 : ℝ) < 2 * (⌈κ C⌉₊ : ℝ))

private lemma two_mul_ceil_κ_sub_one_le_fourteen_sq {C : ℝ} (hC_one : 1 ≤ C) :
    ((2 * ⌈κ C⌉₊ - 1 : ℕ) : ℝ) ≤ 14 * C ^ (2 : ℕ) := by
  refine (by exact_mod_cast (Nat.sub_le (2 * ⌈κ C⌉₊) 1) :
    ((2 * ⌈κ C⌉₊ - 1 : ℕ) : ℝ) ≤ 2 * (⌈κ C⌉₊ : ℝ)).trans ?_
  refine (mul_le_mul_of_nonneg_left
    (le_of_lt (Nat.ceil_lt_add_one
      ((by norm_num : (0 : ℝ) ≤ 6).trans (κ_ge_six_of_one_le hC_one))))
    (by norm_num : (0 : ℝ) ≤ 2)).trans ?_
  unfold κ
  nlinarith [sq_nonneg (C - 1)]

private lemma two_mul_ceil_κ_sub_one_mul_lowerDensityExponent_lt {C γ : ℝ}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) :
    ((2 * ⌈κ C⌉₊ - 1 : ℕ) : ℝ) * lowerDensityExponent C γ < 3 + γ := by
  refine lt_of_le_of_lt (b := (7 / 48) * γ) ?_ ?_
  · refine le_trans (b := (14 * C ^ (2 : ℕ)) * lowerDensityExponent C γ) ?_ ?_
    · apply mul_le_mul_of_nonneg_right
      · exact two_mul_ceil_κ_sub_one_le_fourteen_sq hC_one
      · exact (lowerDensityExponent_pos_of_one_le hγ_pos hC_one).le
    · refine le_trans (b := (14 * C ^ (2 : ℕ)) * (γ / (96 * C ^ (2 : ℕ)))) ?_ ?_
      · apply mul_le_mul_of_nonneg_left
        · exact lowerDensityExponent_le_gamma_div_ninetysix_sq hγ_pos hC_one
        · positivity
      · field_simp [(sq_pos_of_pos (zero_lt_one.trans_le hC_one)).ne']
        ring_nf
        exact le_rfl
  · nlinarith

private lemma pairCardThreshold_gt_of_mul_lowerDensityExponent_lt {γ C R : ℝ} {n : ℕ} {δ :
  unitInterval}
    (_hR_pos : 0 < R) (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn_one : 1 < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hRα_lt : R * lowerDensityExponent C γ < 3 + γ) :
    R < (pairCardThreshold (3 + γ) n δ : ℝ) := by
  refine lt_of_lt_of_le ?_ pairCardThreshold_arg_le
  refine lt_trans (b := (3 + γ) * Real.log (n : ℝ) /
      (lowerDensityExponent C γ * Real.log (n : ℝ))) ?_ ?_
  · rw [lt_div_iff₀ (mul_pos (lowerDensityExponent_pos_of_one_le hγ_pos hC_one)
      (Real.log_pos (by exact_mod_cast hn_one : (1 : ℝ) < n)))]
    nlinarith [mul_lt_mul_of_pos_right hRα_lt
      (Real.log_pos (by exact_mod_cast hn_one : (1 : ℝ) < n))]
  · apply div_lt_div_of_pos_left
    · apply mul_pos
      · linarith
      · apply Real.log_pos
        exact_mod_cast hn_one
    · apply log_one_div_unitInterval_pos
      · exact zero_lt_one.trans hn_one
      · exact hδ_lower
      · exact hδ_upper
    · apply log_one_div_unitInterval_lt_lowerDensityExponent_mul_log
      · exact zero_lt_one.trans hn_one
      · exact hδ_lower

private lemma two_mul_chang_size_threshold_mul_lowerDensityExponent_lt {γ C : ℝ}
    (hγ_pos : 0 < γ) :
    (2 * (Real.exp (changContainerExponent (κ C)))) * lowerDensityExponent C γ <
      3 + γ := by
  have hT : (0 : ℝ) < Real.exp (changContainerExponent (κ C)) := chang_size_threshold_pos C
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left
    (lowerDensityExponent_le_second_component_half C γ) (by positivity)) ?_
  rw [div_div, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
  nlinarith

private lemma two_mul_chang_size_threshold_lt_pairCardThreshold {γ C : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn_one : 1 < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    2 * (Real.exp (changContainerExponent (κ C))) <
      (pairCardThreshold (3 + γ) n δ : ℝ) := by
  apply pairCardThreshold_gt_of_mul_lowerDensityExponent_lt
  · apply mul_pos
    · norm_num
    · exact chang_size_threshold_pos C
  · exact hγ_pos
  · exact hC_one
  · exact hn_one
  · exact hδ_lower
  · exact hδ_upper
  · exact two_mul_chang_size_threshold_mul_lowerDensityExponent_lt hγ_pos

private lemma fourteen_mul_sq_div_ε_mul_lowerDensityExponent_lt {γ C : ℝ}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) :
    (14 * C ^ (2 : ℕ) / ε γ) * lowerDensityExponent C γ < 3 + γ := by
  refine lt_of_le_of_lt (b := 14 * (2 + γ) / 24) ?_ ?_
  · refine le_trans (b :=
      (14 * C ^ (2 : ℕ) / ε γ) *
        (((2 + γ) * ε γ) / (24 * C ^ (2 : ℕ)))) ?_ ?_
    · apply mul_le_mul_of_nonneg_left
      · refine (lowerDensityExponent_le_first_component_half C γ).trans_eq ?_
        ring
      · apply div_nonneg
        · positivity
        · exact (ε_pos hγ_pos).le
    · field_simp [(ε_pos hγ_pos).ne',
        (sq_pos_of_pos (zero_lt_one.trans_le hC_one)).ne']
      exact le_refl (1 : ℝ)
  · nlinarith

private lemma fourteen_mul_sq_lt_ε_mul_pairCardThreshold {γ C : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (_hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn_one : 1 < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    14 * C ^ (2 : ℕ) < ε γ * (pairCardThreshold (3 + γ) n δ : ℝ) := by
  rw [mul_comm (ε γ) ((pairCardThreshold (3 + γ) n δ : ℕ) : ℝ)]
  rw [← div_lt_iff₀ (ε_pos hγ_pos)]
  apply pairCardThreshold_gt_of_mul_lowerDensityExponent_lt
  · apply div_pos
    · apply mul_pos
      · norm_num
      · apply pow_pos
        exact zero_lt_one.trans_le hC_one
    · exact ε_pos hγ_pos
  · exact hγ_pos
  · exact hC_one
  · exact hn_one
  · exact hδ_lower
  · exact hδ_upper
  · exact fourteen_mul_sq_div_ε_mul_lowerDensityExponent_lt hγ_pos hC_one

private lemma two_mul_ceil_κ_sub_one_le_ε_mul_pairCardThreshold {γ C : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn_one : 1 < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    ((2 * ⌈κ C⌉₊ - 1 : ℕ) : ℝ) ≤
      ε γ * (pairCardThreshold (3 + γ) n δ : ℝ) := by
  exact (two_mul_ceil_κ_sub_one_le_fourteen_sq hC_one).trans
    (le_of_lt
      (fourteen_mul_sq_lt_ε_mul_pairCardThreshold hγ_pos hγ_le hC_one hn_one hδ_lower
        hδ_upper))

private lemma two_mul_ceil_κ_sub_one_le_pairCardThreshold {γ C : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn_one : 1 < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    2 * ⌈κ C⌉₊ - 1 ≤ pairCardThreshold (3 + γ) n δ := by
  apply le_of_lt
  exact_mod_cast pairCardThreshold_gt_of_mul_lowerDensityExponent_lt
    (R := ((2 * ⌈κ C⌉₊ - 1 : ℕ) : ℝ))
    (by
      exact_mod_cast two_mul_ceil_κ_sub_one_pos hC_one :
        (0 : ℝ) < ((2 * ⌈κ C⌉₊ - 1 : ℕ) : ℝ))
    hγ_pos hC_one hn_one hδ_lower hδ_upper
    (two_mul_ceil_κ_sub_one_mul_lowerDensityExponent_lt hγ_pos hC_one)

private lemma old_model_threshold_lt_nat {C γ : ℝ} {n : ℕ} (hn : lowerSizeThreshold C γ < n) :
    ((36 * Real.exp (changExponent C)) ^ (2 : ℕ)) < (n : ℝ) := by
  exact (old_model_threshold_le_lowerSizeThreshold C γ).trans_lt hn

private lemma old_model_threshold_nat_pos {C γ : ℝ} {n : ℕ} (hn : lowerSizeThreshold C γ < n) :
    0 < (n : ℝ) := by
  exact (by positivity : (0 : ℝ) < (36 * Real.exp (changExponent C)) ^ (2 : ℕ)).trans
    (old_model_threshold_lt_nat hn)

private lemma log_nat_le_two_sqrt_of_old_model_threshold {C γ : ℝ} {n : ℕ}
    (hn : lowerSizeThreshold C γ < n) :
    Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
  simpa [Real.sqrt_eq_rpow, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    Real.log_le_rpow_div (x := (n : ℝ)) (ε := (1 / 2 : ℝ))
      (le_of_lt (old_model_threshold_nat_pos hn)) (by norm_num)

private lemma density_coeff_log_lt_exp_neg_mul_q {C γ c : ℝ} {n q : ℕ}
    (hγ_pos : 0 < γ) (hc_pos : 0 < c) (hc_lt : c < 1)
    (hn : lowerGapThreshold C γ c < n) (hq_lower : 2 * n ≤ q) :
    2 * densityCoefficient (3 + γ) c * Real.log (n : ℝ) <
      Real.exp (-(changExponent C)) * q := by
  let K := densityCoefficient (3 + γ) c
  have hK_pos : 0 < K := by
    dsimp [K, densityCoefficient]
    have : 0 < Real.log (1 / (1 - c)) := by
      apply Real.log_pos
      rw [one_lt_div] <;> linarith
    positivity
  have hn_old : lowerSizeThreshold C γ < n := (lowerSizeThreshold_le_lowerGapThreshold C γ
    c).trans_lt hn
  have hsquare : (2 * K * Real.exp (changExponent C)) ^ (2 : ℕ) < (n : ℝ) := by
    refine (le_max_left _ _ |>.trans (le_max_right (lowerSizeThreshold C γ) _)).trans_lt hn
  have hfactor : 2 * K * Real.exp (changExponent C) < Real.sqrt (n : ℝ) := by
    simpa [Real.sqrt_sq (by positivity : 0 ≤ 2 * K * Real.exp (changExponent C))] using
      Real.sqrt_lt_sqrt (sq_nonneg (2 * K * Real.exp (changExponent C))) hsquare
  refine (mul_le_mul_of_nonneg_left (log_nat_le_two_sqrt_of_old_model_threshold hn_old)
    (mul_nonneg (by norm_num) hK_pos.le)).trans_lt ?_
  have hsqrt : 4 * K * Real.sqrt (n : ℝ) <
      2 * Real.exp (-(changExponent C)) * (n : ℝ) := by
    refine lt_of_eq_of_lt (b :=
      (2 * K * Real.exp (changExponent C)) *
        (2 * (Real.exp (-(changExponent C)) * Real.sqrt (n : ℝ)))) ?_ ?_
    · rw [Real.exp_neg]
      field_simp
      ring
    · refine (mul_lt_mul_of_pos_right hfactor
        (mul_pos (by norm_num) (mul_pos (Real.exp_pos _) (Real.sqrt_pos.2 ?_)))).trans_eq ?_
      · exact old_model_threshold_nat_pos hn_old
      · conv_rhs => rw [← Real.sq_sqrt (le_of_lt (old_model_threshold_nat_pos hn_old))]
        ring
  refine lt_of_eq_of_lt ?_ (hsqrt.trans_le ?_)
  · ring
  · nlinarith [mul_le_mul_of_nonneg_left
      (by exact_mod_cast hq_lower : (2 * n : ℝ) ≤ q)
      (le_of_lt (Real.exp_pos (-(changExponent C))))]

private lemma lowerLogScale_log_bound_of_gap {C γ c : ℝ} {n : ℕ}
    (hC : 0 < 2 * C) (hε : 0 < ε γ)
    (hn : lowerGapThreshold C γ c < n) :
    lowerLogScale γ * Real.log
        (max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstant C γ hC hε *
          Real.log (n : ℝ)) ≤
      Real.log (n : ℝ) := by
  have hn_old : lowerSizeThreshold C γ < n := (lowerSizeThreshold_le_lowerGapThreshold C γ
    c).trans_lt hn
  apply mul_log_Ax_le_self_of_two_mul_log
  · exact mul_pos (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) (lowerConstant_pos C γ hC hε)
  · exact lowerLogScale_pos hε
  · exact (by norm_num : (0 : ℝ) < 15).trans
      (fifteen_lt_log_of_lowerAnalyticThreshold hn_old)
  rw [← lowerConstantDefault_eq C γ hC hε]
  refine le_of_lt ?_
  rw [← Real.log_exp (2 * lowerLogScale γ * Real.log
    (max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstantDefault C γ *
      lowerLogScale γ))]
  apply Real.log_lt_log (Real.exp_pos _)
  refine (Real.exp_le_exp.mpr (le_max_left
    (2 * lowerLogScale γ * Real.log
      (max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstantDefault C γ * lowerLogScale γ))
    ((4 * lowerGapSqrtScaleDefault C γ c * Real.log
      (2 * max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstantDefault C γ *
        lowerGapSqrtScaleDefault C γ c)) ^ (2 : ℕ)))).trans_lt ?_
  exact ((le_max_right
    ((2 * densityCoefficient (3 + γ) c * Real.exp (changExponent C)) ^ (2 : ℕ))
    (Real.exp (max
      (2 * lowerLogScale γ * Real.log
        (max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstantDefault C γ * lowerLogScale γ))
      ((4 * lowerGapSqrtScaleDefault C γ c * Real.log
        (2 * max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstantDefault C γ *
          lowerGapSqrtScaleDefault C γ c)) ^ (2 : ℕ))))).trans
    (le_max_right (lowerSizeThreshold C γ) _)).trans_lt hn

private lemma lowerGapSqrtScale_threshold_bound {C γ c : ℝ} {n : ℕ}
    (hC : 0 < 2 * C) (hε : 0 < ε γ)
    (hn : lowerGapThreshold C γ c < n) :
    4 * lowerGapSqrtScale C γ c hC hε * Real.log
        (2 * max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstant C γ hC hε *
          lowerGapSqrtScale C γ c hC hε) ≤
      Real.sqrt (Real.log (n : ℝ)) := by
  apply Real.le_sqrt_of_sq_le
  rw [← lowerConstantDefault_eq C γ hC hε, ← lowerGapSqrtScaleDefault_eq C γ c hC hε]
  refine le_of_lt ?_
  rw [← Real.log_exp ((4 * lowerGapSqrtScaleDefault C γ c * Real.log
    (2 * max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstantDefault C γ *
      lowerGapSqrtScaleDefault C γ c)) ^ (2 : ℕ))]
  apply Real.log_lt_log (Real.exp_pos _)
  refine (Real.exp_le_exp.mpr (le_max_right
    (2 * lowerLogScale γ * Real.log
      (max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstantDefault C γ * lowerLogScale γ))
    ((4 * lowerGapSqrtScaleDefault C γ c * Real.log
      (2 * max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstantDefault C γ *
        lowerGapSqrtScaleDefault C γ c)) ^ (2 : ℕ)))).trans_lt ?_
  exact ((le_max_right
    ((2 * densityCoefficient (3 + γ) c * Real.exp (changExponent C)) ^ (2 : ℕ))
    (Real.exp (max
      (2 * lowerLogScale γ * Real.log
        (max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstantDefault C γ * lowerLogScale γ))
      ((4 * lowerGapSqrtScaleDefault C γ c * Real.log
        (2 * max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstantDefault C γ *
          lowerGapSqrtScaleDefault C γ c)) ^ (2 : ℕ))))).trans
    (le_max_right (lowerSizeThreshold C γ) _)).trans_lt hn

private lemma lowerGapSqrtScale_log_bound {C γ c : ℝ} {n : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC : 0 < 2 * C) (hε : 0 < ε γ)
    (hc_pos : 0 < c) (hc_lt : c < 1)
    (hn : lowerGapThreshold C γ c < n) :
    lowerGapSqrtScale C γ c hC hε * Real.log
        (max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstant C γ hC hε *
          Real.log (n : ℝ)) ≤
      Real.sqrt (Real.log (n : ℝ)) := by
  let M := max 42 (3 * densityCoefficient (3 + γ) c)
  have hM : (42 : ℝ) ≤ M := le_max_left _ _
  have hM_pos : 0 < M := (by norm_num : (0 : ℝ) < 42).trans_le hM
  have hK_pos : 0 < densityCoefficient (3 + γ) c :=
    zero_lt_one.trans (one_lt_densityCoefficient hγ_pos hc_pos hc_lt)
  have hn_old : lowerSizeThreshold C γ < n := (lowerSizeThreshold_le_lowerGapThreshold C γ
    c).trans_lt hn
  have hlog_pos : 0 < Real.log (n : ℝ) :=
    (by norm_num : (0 : ℝ) < 15).trans
      (fifteen_lt_log_of_lowerAnalyticThreshold hn_old)
  rw [← mul_div_cancel_left₀ (Real.sqrt (Real.log (n : ℝ)))
    (lowerGapSqrtScale_pos hC hε hK_pos).ne', mul_div_assoc]
  apply mul_le_mul_of_nonneg_left
  · refine (Real.log_le_log
      (x := M * lowerConstant C γ hC hε * Real.log (n : ℝ))
      (y := (2 * M * lowerConstant C γ hC hε * lowerGapSqrtScale C γ c hC hε *
        (Real.sqrt (Real.log (n : ℝ)) / lowerGapSqrtScale C γ c hC hε)) ^ (2 : ℕ))
      (mul_pos (mul_pos hM_pos (lowerConstant_pos C γ hC hε)) hlog_pos) ?_).trans ?_
    · refine le_trans (b := (2 * M) ^ (2 : ℕ) * (lowerConstant C γ hC hε) ^ (2 : ℕ) *
          Real.log (n : ℝ)) ?_ ?_
      · apply mul_le_mul_of_nonneg_right
        · nlinarith [hM, one_le_lowerConstant hC hε,
            mul_nonneg hM_pos.le (by nlinarith [one_le_lowerConstant hC hε] :
              0 ≤ lowerConstant C γ hC hε - 1)]
        · exact hlog_pos.le
      · field_simp [(lowerGapSqrtScale_pos hC hε hK_pos).ne']
        rw [Real.sq_sqrt hlog_pos.le]
    · rw [Real.log_pow]
      rw [Real.log_mul (by
        exact mul_ne_zero
          (mul_ne_zero (mul_ne_zero (by norm_num) hM_pos.ne')
            (lowerConstant_pos C γ hC hε).ne')
          (lowerGapSqrtScale_pos hC hε hK_pos).ne') (by
        exact (div_pos (Real.sqrt_pos.2 hlog_pos) (lowerGapSqrtScale_pos hC hε hK_pos)).ne')]
      have hthreshold :
          4 * Real.log
              (2 * M * lowerConstant C γ hC hε * lowerGapSqrtScale C γ c hC hε) ≤
            Real.sqrt (Real.log (n : ℝ)) / lowerGapSqrtScale C γ c hC hε := by
        rw [le_div_iff₀ (lowerGapSqrtScale_pos hC hε hK_pos)]
        simpa [M, mul_assoc, mul_left_comm, mul_comm] using
          lowerGapSqrtScale_threshold_bound (C := C) (γ := γ) (c := c) hC hε hn
      have hfour : (4 : ℝ) ≤ Real.log
          (2 * M * lowerConstant C γ hC hε * lowerGapSqrtScale C γ c hC hε) := by
        refine (le_of_lt log_eightyfour_gt_four).trans ?_
        apply Real.log_le_log (by norm_num)
        nlinarith [one_le_lowerConstant hC hε,
          one_le_lowerGapSqrtScale hγ_pos hγ_le hC hε hc_pos hc_lt,
          mul_nonneg (by nlinarith [hM] : 0 ≤ 2 * M - 84)
            (by nlinarith [one_le_lowerConstant hC hε,
              one_le_lowerGapSqrtScale hγ_pos hγ_le hC hε hc_pos hc_lt] :
              0 ≤ lowerConstant C γ hC hε * lowerGapSqrtScale C γ c hC hε)]
      nlinarith [hthreshold,
        lower_log_le_quarter_self_of_sixteen_le (by nlinarith [hfour, hthreshold])]
  · exact (lowerGapSqrtScale_pos hC hε hK_pos).le

private abbrev zmodModelQ {γ C : ℝ} {n : ℕ}
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hn : lowerSizeThreshold C γ < n) : ℕ :=
  Classical.choose (exists_zmod_model n (lowerSizeThreshold_lt_nat_pos hγ_pos C_pos hn))

private lemma zmodModelQ_spec {γ C : ℝ} {n : ℕ}
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hn : lowerSizeThreshold C γ < n) :
    Nat.Prime (zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) ∧
      2 * n ≤ zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn ∧
        zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn ≤ 4 * n ∧
          ∃ ψ : ℕ → ZMod (zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn),
            IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ := by
  unfold zmodModelQ
  exact Classical.choose_spec (exists_zmod_model n (lowerSizeThreshold_lt_nat_pos hγ_pos C_pos hn))

private lemma zmodModelQ_prime {γ C : ℝ} {n : ℕ}
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hn : lowerSizeThreshold C γ < n) :
    Nat.Prime (zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) := by
  exact (zmodModelQ_spec hγ_pos C_pos hn).1

private lemma zmodModelQ_lower {γ C : ℝ} {n : ℕ}
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hn : lowerSizeThreshold C γ < n) :
    2 * n ≤ zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn := by
  exact (zmodModelQ_spec hγ_pos C_pos hn).2.1

private lemma zmodModelQ_upper {γ C : ℝ} {n : ℕ}
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hn : lowerSizeThreshold C γ < n) :
    zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn ≤ 4 * n := by
  exact (zmodModelQ_spec hγ_pos C_pos hn).2.2.1

private abbrev zmodModelEmbedding {γ C : ℝ} {n : ℕ}
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hn : lowerSizeThreshold C γ < n) :
    ℕ → ZMod (zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) :=
  Classical.choose
    (Classical.choose_spec (exists_zmod_model n (lowerSizeThreshold_lt_nat_pos hγ_pos C_pos
      hn))).2.2.2

private lemma zmodModelEmbedding_iso {γ C : ℝ} {n : ℕ}
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hn : lowerSizeThreshold C γ < n) :
    IsAddFreimanIso 2 (interval n)
      (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn '' (interval n))
      (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) := by
  unfold zmodModelEmbedding
  exact Classical.choose_spec
    (Classical.choose_spec (exists_zmod_model n (lowerSizeThreshold_lt_nat_pos hγ_pos C_pos
      hn))).2.2.2

private lemma two_lt_nat_of_lowerSizeThreshold_lt {C γ : ℝ} {n : ℕ} (hn : lowerSizeThreshold C γ
  < n) :
    2 < n := by
  exact_mod_cast (two_le_lowerSizeThreshold C γ).trans_lt hn

private lemma two_le_nat_of_lowerSizeThreshold_lt {C γ : ℝ} {n : ℕ} (hn : lowerSizeThreshold C γ
  < n) :
    2 ≤ n := by
  exact (two_lt_nat_of_lowerSizeThreshold_lt hn).le

private lemma one_lt_nat_of_lowerSizeThreshold_lt {C γ : ℝ} {n : ℕ} (hn : lowerSizeThreshold C γ
  < n) :
    1 < n := by
  exact (by norm_num : 1 < 2).trans (two_lt_nat_of_lowerSizeThreshold_lt hn)

private lemma unitInterval_pos_of_density_lower {C γ : ℝ} {n : ℕ} {δ : unitInterval}
    (hn : lowerSizeThreshold C γ < n) (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) :
    0 < (δ : ℝ) := by
  exact (Real.rpow_pos_of_pos (old_model_threshold_nat_pos hn) _).trans hδ_lower

private lemma unitInterval_lt_one {δ : unitInterval}
    (hδ_upper : (δ : ℝ) < 1) :
    (δ : ℝ) < 1 := by
  linarith

private lemma pairCardThreshold_pos_of_lower_density {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    0 < pairCardThreshold (3 + γ) n δ := by
  apply pairCardThreshold_pos_of_density
  · linarith
  · exact unitInterval_pos_of_density_lower hn hδ_lower
  · exact unitInterval_lt_one hδ_upper
  · exact one_lt_nat_of_lowerSizeThreshold_lt hn

private lemma pairCardThreshold_le_density_log_of_lower_density {γ C c : ℝ} {n : ℕ}
    {δ : unitInterval} (hγ_pos : 0 < γ) (hc_pos : 0 < c) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ))
    (hδ_upper : (δ : ℝ) ≤ 1 - c) :
    (pairCardThreshold (3 + γ) n δ : ℝ) ≤
      densityCoefficient (3 + γ) c * Real.log (n : ℝ) := by
  refine pairCardThreshold_le_densityCoefficient_mul_log ?_ hc_pos
    (two_le_nat_of_lowerSizeThreshold_lt hn) (unitInterval_pos_of_density_lower hn hδ_lower)
    hδ_upper
  linarith

private lemma one_le_sumset_card_coefficient_of_threshold_pair_sumset
    {G : Type*} [DecidableEq G] [Add G]
    [IsRightCancelAdd G] {γ C : ℝ} {n : ℕ} {δ : unitInterval} {A B : Finset G}
    (hγ_pos : 0 < γ) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hAcard : A.card = pairCardThreshold (3 + γ) n δ)
    (hBcard : B.card = pairCardThreshold (3 + γ) n δ)
    (hAB : (A + B).card ≤ C * pairCardThreshold (3 + γ) n δ) :
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
  refine (by
    nlinarith [half_le_one_sub_ε hγ_pos hγ_le, hA₀large,
      (by positivity : 0 ≤ (k : ℝ))] :
    (k : ℝ) / 2 ≤ (A₀.card : ℝ)).trans ?_
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
  refine (Finset.card_union_le (A₀.image ψ) (B₀.image ψ)).trans ?_
  rw [freiman_image_card_eq_of_subset hψ (hA₀A.trans hAint),
    freiman_image_card_eq_of_subset hψ (hB₀B.trans hBint)]
  refine (Nat.add_le_add (Finset.card_le_card hA₀A) (Finset.card_le_card hB₀B)).trans ?_
  rw [hAcard, hBcard]
  omega

private lemma image_union_card_le_density_coeff_log {γ C c : ℝ} {n q : ℕ}
    {δ : unitInterval} {ψ : ℕ → ZMod q} {A B A₀ B₀ : Finset ℕ}
    (hγ_pos : 0 < γ) (hc_pos : 0 < c) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ))
    (hδ_upper : (δ : ℝ) ≤ 1 - c)
    (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ)
    (hAint : A ⊆ interval n) (hBint : B ⊆ interval n)
    (hAcard : A.card = pairCardThreshold (3 + γ) n δ)
    (hBcard : B.card = pairCardThreshold (3 + γ) n δ)
    (hA₀A : A₀ ⊆ A) (hB₀B : B₀ ⊆ B) :
    ((A₀.image ψ ∪ B₀.image ψ).card : ℝ) ≤
      2 * densityCoefficient (3 + γ) c * Real.log (n : ℝ) := by
  refine (by
    exact_mod_cast image_union_card_le_two_mul_threshold hψ hAint hBint hAcard hBcard hA₀A
      hB₀B :
    ((A₀.image ψ ∪ B₀.image ψ).card : ℝ) ≤
      ((2 * pairCardThreshold (3 + γ) n δ : ℕ) : ℝ)).trans ?_
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
    (hAcard : A.card = pairCardThreshold (3 + γ) n δ)
    (hBcard : B.card = pairCardThreshold (3 + γ) n δ)
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
    (hAcard : A.card = pairCardThreshold (3 + γ) n δ)
    (hBcard : B.card = pairCardThreshold (3 + γ) n δ)
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
    (hA₀large : (1 - ε γ) * (pairCardThreshold (3 + γ) n δ : ℝ) ≤ (A₀.card : ℝ)) :
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
    (hkdef : k = pairCardThreshold (3 + γ) n δ)
    (hdim_bound : freimanDim (A₀.image ψ ∪ B₀.image ψ) ≤ 2 * ⌈κ C⌉₊ - 1) :
    (freimanDim (A₀.image ψ ∪ B₀.image ψ) : ℝ) ≤ ε γ * (k : ℝ) := by
  rw [hkdef]
  refine (by exact_mod_cast hdim_bound :
    (freimanDim (A₀.image ψ ∪ B₀.image ψ) : ℝ) ≤
      ((2 * ⌈κ C⌉₊ - 1 : ℕ) : ℝ)).trans ?_
  exact two_mul_ceil_κ_sub_one_le_ε_mul_pairCardThreshold hγ_pos hγ_le hC_one hn_one
    hδ_lower hδ_upper

private lemma large_subsets_image_sum_lower {γ C : ℝ} {n q : ℕ}
    {δ : unitInterval} {ψ : ℕ → ZMod q} {A₀ B₀ : Finset ℕ} {k : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn_one : 1 < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ)
    (hA₀int : A₀ ⊆ interval n) (hB₀int : B₀ ⊆ interval n)
    (hkdef : k = pairCardThreshold (3 + γ) n δ) (hkpos : 0 < k)
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
      A.card = pairCardThreshold (3 + γ) n δ → B.card = pairCardThreshold (3 + γ) n δ →
      A₀ ⊆ A → B₀ ⊆ B →
      (1 - ε γ) * (pairCardThreshold (3 + γ) n δ : ℝ) ≤ (A₀.card : ℝ) →
      (1 - ε γ) * (pairCardThreshold (3 + γ) n δ : ℝ) ≤ (B₀.card : ℝ) →
      (A + B).card ≤ C * pairCardThreshold (3 + γ) n δ →
      ∃ P ∈ properGAPsZModUpToDim (pairCardThreshold (3 + γ) n δ)
          ⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊
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
    refine ⟨?_, ?_⟩
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
    refine ⟨hA₀A.trans hAint ha, ?_⟩
    apply hXP
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.2 ⟨a, ha, rfl⟩))
  · intro b hb
    rw [zmodGAPPreimageContainer, Finset.mem_filter]
    refine ⟨hB₀B.trans hBint hb, ?_⟩
    apply hXP
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.2 ⟨b, hb, rfl⟩))
  · exact image_union_freimanDim_le_two_ceil_κ_sub_one hγ_pos hγ_le
      (one_le_sumset_card_coefficient_of_threshold_pair_sumset hγ_pos hn hδ_lower hδ_upper
        hAcard hBcard hAB)
      (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn)
      (zmodModelEmbedding_iso (γ := γ) (C := C) (n := n) hγ_pos C_pos hn)
      hAint hBint hAcard hBcard hA₀A hB₀B hA₀large hAB

private lemma large_subsets_first_term_lower_by_dim {γ C : ℝ} {n q : ℕ}
    {δ : unitInterval} {ψ : ℕ → ZMod q} {A₀ B₀ : Finset ℕ} {D k : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn_one : 1 < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hψ : IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ)
    (hA₀int : A₀ ⊆ interval n) (hB₀int : B₀ ⊆ interval n)
    (hkdef : k = pairCardThreshold (3 + γ) n δ) (hkpos : 0 < k)
    (hA₀large : (1 - ε γ) * (k : ℝ) ≤ (A₀.card : ℝ))
    (hB₀large : (1 - ε γ) * (k : ℝ) ≤ (B₀.card : ℝ))
    (hDdim : D ≤ freimanDim (A₀.image ψ ∪ B₀.image ψ))
    (hdim_bound : freimanDim (A₀.image ψ ∪ B₀.image ψ) ≤ 2 * ⌈κ C⌉₊ - 1) :
    (1 - 3 * ε γ) * (D : ℝ) * (k : ℝ) ≤
      (1 - ε γ) * ((natCastImage A₀ + natCastImage B₀).card : ℝ) := by
  refine le_trans (b :=
      (1 - ε γ) *
        ((1 - 2 * ε γ) * (freimanDim (A₀.image ψ ∪ B₀.image ψ) : ℝ) * (k : ℝ))) ?_ ?_
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
  refine (mul_le_mul_of_nonneg_left
    (large_subsets_image_sum_lower hγ_pos hγ_le hC_one hn_one hδ_lower hδ_upper hψ
      hA₀int hB₀int hkdef hkpos hA₀large hB₀large hdim_bound)
    (by
      exact (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (half_le_one_sub_ε hγ_pos hγ_le))).trans_eq ?_
  rw [freiman_image_sum_card hψ hA₀int hB₀int, natCastImage_sum_card A₀ B₀]

private abbrev lowerModelGAPs {γ C : ℝ} {n : ℕ} (δ : unitInterval)
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hn : lowerSizeThreshold C γ < n) :
    Finset (ProperGAP (ZMod (zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn))) := by
  classical
  exact (Finset.Icc 1 (pairCardThreshold (3 + γ) n δ)).biUnion fun d =>
    properGAPsZModOfDim d
        ⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊
        (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).pos

private abbrev bltLargePreimage (A : Finset ℕ) (T : Finset ℤ) : Finset ℕ :=
  A.filter fun a => (a : ℤ) ∈ T

private lemma bltLargePreimage_subset (A : Finset ℕ) (T : Finset ℤ) :
    bltLargePreimage A T ⊆ A := by
  intro a ha
  rw [bltLargePreimage, Finset.mem_filter] at ha
  exact ha.1

private lemma natCastImage_bltLargePreimage_eq_of_subset {A : Finset ℕ} {T : Finset ℤ}
    (hT : T ⊆ natCastImage A) :
    natCastImage (bltLargePreimage A T) = T := by
  unfold bltLargePreimage
  exact natCastImage_filter_mem_eq_of_subset hT

private lemma bltLargePreimage_card_eq_of_subset {A : Finset ℕ} {T : Finset ℤ}
    (hT : T ⊆ natCastImage A) :
    (bltLargePreimage A T).card = T.card := by
  rw [← natCastImage_card (bltLargePreimage A T), natCastImage_bltLargePreimage_eq_of_subset hT]

private lemma bltLargePreimage_large_of_blt {γ : ℝ} {A : Finset ℕ} {T : Finset ℤ}
    {k : ℕ}
    (hAcard : A.card = k) (hT : T ⊆ natCastImage A)
    (hTlarge : (1 - ε γ) * ((natCastImage A).card : ℝ) ≤ (T.card : ℝ)) :
    (1 - ε γ) * (k : ℝ) ≤ ((bltLargePreimage A T).card : ℝ) := by
  simpa [natCastImage_card A, hAcard, bltLargePreimage_card_eq_of_subset hT] using hTlarge

private lemma natCastImage_nonempty_of_card_eq {A : Finset ℕ} {k : ℕ}
    (hAcard : A.card = k) (hk : 0 < k) :
    (natCastImage A).Nonempty := by
  apply Finset.card_pos.mp
  rw [natCastImage_card, hAcard]
  exact hk

private lemma two_le_two_mul_ceil_κ_sub_one {C : ℝ} (hC_one : 1 ≤ C) :
    2 ≤ 2 * ⌈κ C⌉₊ - 1 := by
  exact (by norm_num : 2 ≤ 2 * 6 - 1).trans
    (Nat.sub_le_sub_right
      (Nat.mul_le_mul_left 2 (by
        exact_mod_cast (κ_ge_six_of_one_le hC_one).trans (Nat.le_ceil (κ C))))
      1)

private lemma two_le_pairCardThreshold_of_one_le {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    2 ≤ pairCardThreshold (3 + γ) n δ := by
  exact (two_le_two_mul_ceil_κ_sub_one hC_one).trans
    (two_mul_ceil_κ_sub_one_le_pairCardThreshold hγ_pos hC_one
      (one_lt_nat_of_lowerSizeThreshold_lt hn)
      hδ_lower hδ_upper)

private lemma four_le_pairCardThreshold_of_one_le {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    4 ≤ pairCardThreshold (3 + γ) n δ := by
  apply le_of_lt
  exact_mod_cast (by
    nlinarith [fourteen_mul_sq_lt_ε_mul_pairCardThreshold hγ_pos hγ_le hC_one
      (one_lt_nat_of_lowerSizeThreshold_lt hn) hδ_lower hδ_upper,
      ε_le_one_twelfth hγ_pos hγ_le,
      sq_nonneg (C - 1)] :
      (4 : ℝ) < pairCardThreshold (3 + γ) n δ)

private lemma two_le_blt_sqrt_pairCardThreshold {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    2 ≤ lowerBltConstant C γ hC_two hε *
        Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ) := by
  nlinarith [one_le_lowerBltConstant hC_two hε,
    Real.le_sqrt_of_sq_le (x := (2 : ℝ))
      (y := (pairCardThreshold (3 + γ) n δ : ℝ)) (by
      convert (by
        exact_mod_cast four_le_pairCardThreshold_of_one_le hγ_pos hγ_le hC_one hn hδ_lower
          hδ_upper :
          (4 : ℝ) ≤ pairCardThreshold (3 + γ) n δ) using 1
      norm_num)]

private lemma lower_blt_ceiling_succ_le_two_mul {γ C : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    ((⌈lowerBltConstant C γ hC_two hε *
          Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ + 1 : ℕ) : ℝ) ≤
      2 * lowerBltConstant C γ hC_two hε *
        Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ) := by
  rw [Nat.cast_add, Nat.cast_one]
  nlinarith [Nat.ceil_lt_add_one
    (a := lowerBltConstant C γ hC_two hε *
      Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)) (mul_nonneg
    ((zero_le_one' ℝ).trans (one_le_lowerBltConstant hC_two hε))
    (Real.sqrt_nonneg (pairCardThreshold (3 + γ) n δ : ℝ))),
    two_le_blt_sqrt_pairCardThreshold hγ_pos hγ_le hC_one hn hδ_lower hδ_upper hC_two
      hε]

private lemma changCarrierBound_ceil_succ_le_three_mul_lowerConstant {γ C : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    ((⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ + 1 : ℕ) : ℝ) ≤
      3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ) := by
  simp [changCarrierBound]
  nlinarith [Nat.ceil_lt_add_one
    (a := Real.exp (changTheoremExponent (κ C)) *
      (2 * (pairCardThreshold (3 + γ) n δ : ℝ)))
    (mul_nonneg (Real.exp_pos _).le (by positivity :
      0 ≤ 2 * (pairCardThreshold (3 + γ) n δ : ℝ))),
    le_max_left (Real.exp (changTheoremExponent (κ C)))
      (4 * lowerBltConstant C γ hC_two hε),
    mul_le_mul_of_nonneg_right
      (le_max_left (Real.exp (changTheoremExponent (κ C)))
        (4 * lowerBltConstant C γ hC_two hε))
      (by positivity : 0 ≤ 2 * (pairCardThreshold (3 + γ) n δ : ℝ)),
    (by
      rw [lowerConstant_eq C γ hC_two hε]
      exact (mul_le_mul_of_nonneg_right
        (le_max_left (Real.exp (changTheoremExponent (κ C)))
          (4 * lowerBltConstant C γ hC_two hε))
        (by positivity : 0 ≤ 2 * (pairCardThreshold (3 + γ) n δ : ℝ))).trans_eq (by ring) :
      Real.exp (changTheoremExponent (κ C)) *
          (2 * (pairCardThreshold (3 + γ) n δ : ℝ)) ≤
        2 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ)),
    one_le_lowerConstant hC_two hε,
    (by
      exact_mod_cast two_le_pairCardThreshold_of_one_le hγ_pos hC_one hn hδ_lower hδ_upper :
        (2 : ℝ) ≤ pairCardThreshold (3 + γ) n δ),
    (by
      rw [← one_mul (2 : ℝ)]
      exact mul_le_mul (one_le_lowerConstant hC_two hε)
        (by
          exact_mod_cast two_le_pairCardThreshold_of_one_le hγ_pos hC_one hn hδ_lower
            hδ_upper :
            (2 : ℝ) ≤ pairCardThreshold (3 + γ) n δ)
        (by norm_num) ((zero_le_one' ℝ).trans (one_le_lowerConstant hC_two hε)) :
      (2 : ℝ) ≤ lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ)),
    two_le_pairCardThreshold_of_one_le hγ_pos hC_one hn hδ_lower hδ_upper]

private lemma lower_exponent_coefficient {γ : ℝ} (hγ_pos : 0 < γ) (_hγ_le : γ ≤ 1) :
    2 * (1 + ε γ) ≤ (1 - 3 * ε γ) * (3 + γ) := by
  unfold ε
  field_simp [(by positivity : 0 < 4 * (γ + 2)).ne']
  nlinarith

private lemma one_le_lower_counting_base {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    1 ≤ 3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ) := by
  refine (by norm_num : (1 : ℝ) ≤ 3 * 2).trans ?_
  nlinarith [(by
    rw [← one_mul (2 : ℝ)]
    exact mul_le_mul (one_le_lowerConstant hC_two hε)
      (by
        exact_mod_cast two_le_pairCardThreshold_of_one_le hγ_pos hC_one hn hδ_lower hδ_upper :
        (2 : ℝ) ≤ pairCardThreshold (3 + γ) n δ)
      (by norm_num) ((zero_le_one' ℝ).trans (one_le_lowerConstant hC_two hε)) :
    (2 : ℝ) ≤ lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ))]

private lemma four_le_lower_counting_base {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    4 ≤ 3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ) := by
  refine (by norm_num : (4 : ℝ) ≤ 3 * 2).trans ?_
  nlinarith [(by
    rw [← one_mul (2 : ℝ)]
    exact mul_le_mul (one_le_lowerConstant hC_two hε)
      (by
        exact_mod_cast two_le_pairCardThreshold_of_one_le hγ_pos hC_one hn hδ_lower hδ_upper :
        (2 : ℝ) ≤ pairCardThreshold (3 + γ) n δ)
      (by norm_num) ((zero_le_one' ℝ).trans (one_le_lowerConstant hC_two hε)) :
    (2 : ℝ) ≤ lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ))]

private lemma lower_counting_base_pos {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    0 < 3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ) := by
  exact zero_lt_one.trans_le
    (one_le_lower_counting_base hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε)

private lemma lower_chang_carrier_ceil_pos {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (_hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    0 < ⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ := by
  rw [Nat.ceil_pos]
  rw [changCarrierBound]
  apply mul_pos
  · exact Real.exp_pos _
  · exact_mod_cast Nat.mul_pos (by norm_num : 0 < 2)
      (pairCardThreshold_pos_of_lower_density hγ_pos hn hδ_lower hδ_upper)

private lemma changCarrierBound_ceil_le_lower_counting_base {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    (⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ : ℝ) ≤
      3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ) := by
  exact (by exact_mod_cast
      Nat.le_succ ⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ :
      (⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ : ℝ) ≤
        (⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ + 1 : ℕ)).trans
    (changCarrierBound_ceil_succ_le_three_mul_lowerConstant hγ_pos hC_one hn hδ_lower hδ_upper
      hC_two hε)

private lemma blt_ceiling_succ_le_lower_counting_base {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    ((⌈lowerBltConstant C γ hC_two hε *
          Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ + 1 : ℕ) : ℝ) ≤
      3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ) := by
  refine (lower_blt_ceiling_succ_le_two_mul hγ_pos hγ_le hC_one hn hδ_lower hδ_upper
    hC_two hε).trans ?_
  nlinarith [
    (mul_le_mul (lowerBltConstant_le_lowerConstant hC_two hε)
      (by
        rw [Real.sqrt_le_left (by positivity :
          0 ≤ (pairCardThreshold (3 + γ) n δ : ℝ))]
        have hk_one : (1 : ℝ) ≤ pairCardThreshold (3 + γ) n δ := by
          exact_mod_cast ((by norm_num : 1 ≤ 2).trans
            (two_le_pairCardThreshold_of_one_le hγ_pos hC_one hn hδ_lower hδ_upper))
        nlinarith)
      (Real.sqrt_nonneg (pairCardThreshold (3 + γ) n δ : ℝ))
      ((zero_le_one' ℝ).trans (one_le_lowerConstant hC_two hε)) :
      lowerBltConstant C γ hC_two hε *
          Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ) ≤
        lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ)),
    lowerConstant_pos C γ hC_two hε,
    pairCardThreshold_pos_of_lower_density hγ_pos hn hδ_lower hδ_upper]

private lemma zmodModelQ_le_n_mul_lower_counting_base {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    (zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn : ℝ) ≤
      (n : ℝ) * (3 * lowerConstant C γ hC_two hε *
        (pairCardThreshold (3 + γ) n δ : ℝ)) := by
  refine (by
      exact_mod_cast zmodModelQ_upper (γ := γ) (C := C) (n := n) hγ_pos C_pos hn :
        (zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn : ℝ) ≤
          4 * (n : ℝ)).trans ?_
  rw [mul_comm (4 : ℝ) (n : ℝ)]
  exact mul_le_mul_of_nonneg_left
    (four_le_lower_counting_base hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε)
    (le_of_lt (old_model_threshold_nat_pos hn))

private lemma lower_counting_base_log_le_epsilon_log_div_eight {γ C c : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (_hγ_le : γ ≤ 1) (hC_one : 1 ≤ C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    Real.log (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ)) ≤
      ε γ * Real.log (n : ℝ) / 8 := by
  refine (Real.log_le_log
    (x := 3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ))
    (y := max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstant C γ hC_two hε *
      Real.log (n : ℝ))
    (lower_counting_base_pos hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε) ?_).trans ?_
  · have hk := pairCardThreshold_le_density_log_of_lower_density hγ_pos hc_pos hn hδ_lower
      hδ_upper_c
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      linarith [fifteen_lt_log_of_lowerAnalyticThreshold hn]
    nlinarith [mul_le_mul_of_nonneg_left hk
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (lowerConstant_pos C γ hC_two hε).le),
      mul_le_mul_of_nonneg_right (le_max_right (42 : ℝ)
        (3 * densityCoefficient (3 + γ) c))
        (mul_nonneg (lowerConstant_pos C γ hC_two hε).le hlog_nonneg)]
  · have hT₁ := lowerLogScale_log_bound_of_gap (C := C) (γ := γ) (c := c) (n := n)
      hC_two hε hn_gap
    rw [lowerLogScale] at hT₁
    rw [div_mul_eq_mul_div] at hT₁
    rw [div_le_iff₀ hε] at hT₁
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
    nlinarith

private lemma lower_c_sqrt_counting_base_log_le_epsilon_log_div_eight {γ C c : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    lowerBltConstant C γ hC_two hε *
        Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ) *
        Real.log (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ)) ≤
      ε γ * Real.log (n : ℝ) / 8 := by
  refine (mul_le_mul_of_nonneg_left
      (Real.log_le_log
        (x := 3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ))
        (y := max 42 (3 * densityCoefficient (3 + γ) c) * lowerConstant C γ hC_two hε *
          Real.log (n : ℝ))
        (lower_counting_base_pos hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε) ?_) ?_).trans ?_
  · have hk := pairCardThreshold_le_density_log_of_lower_density hγ_pos hc_pos hn hδ_lower
      hδ_upper_c
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      linarith [fifteen_lt_log_of_lowerAnalyticThreshold hn]
    nlinarith [mul_le_mul_of_nonneg_left hk
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (lowerConstant_pos C γ hC_two hε).le),
      mul_le_mul_of_nonneg_right (le_max_right (42 : ℝ)
        (3 * densityCoefficient (3 + γ) c))
        (mul_nonneg (lowerConstant_pos C γ hC_two hε).le hlog_nonneg)]
  · exact mul_nonneg ((zero_le_one' ℝ).trans (one_le_lowerBltConstant hC_two hε))
      (Real.sqrt_nonneg (pairCardThreshold (3 + γ) n δ : ℝ))
  · refine (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt
          (pairCardThreshold_le_density_log_of_lower_density hγ_pos hc_pos hn hδ_lower
            hδ_upper_c))
        ((zero_le_one' ℝ).trans (one_le_lowerBltConstant hC_two hε))) ?_).trans ?_
    · apply Real.log_nonneg
      have hbase : (1 : ℝ) ≤ lowerConstant C γ hC_two hε * Real.log (n : ℝ) := by
        rw [← one_mul (1 : ℝ)]
        exact mul_le_mul (one_le_lowerConstant hC_two hε)
          ((by norm_num : (1 : ℝ) < 15).le.trans
            (le_of_lt (fifteen_lt_log_of_lowerAnalyticThreshold hn)))
          (by norm_num) ((zero_le_one' ℝ).trans (one_le_lowerConstant hC_two hε))
      refine hbase.trans ?_
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right
        ((by norm_num : (1 : ℝ) ≤ 42).trans
          (le_max_left (42 : ℝ) (3 * densityCoefficient (3 + γ) c)))
        (zero_le_one.trans hbase)
    · rw [Real.sqrt_mul
        (zero_lt_one.trans (one_lt_densityCoefficient hγ_pos hc_pos hc_lt)).le]
      have hT₂ := lowerGapSqrtScale_log_bound hγ_pos hγ_le hC_two hε hc_pos hc_lt hn_gap
      rw [lowerGapSqrtScale, div_mul_eq_mul_div] at hT₂
      rw [div_le_iff₀ hε] at hT₂
      have := mul_le_mul_of_nonneg_right hT₂ (Real.sqrt_nonneg (Real.log (n : ℝ)))
      have hsquare : Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (Real.log (n : ℝ)) =
          Real.log (n : ℝ) := by
        rw [← pow_two, Real.sq_sqrt (le_of_lt ((by norm_num : (0 : ℝ) < 15).trans
          (fifteen_lt_log_of_lowerAnalyticThreshold hn)))]
      nlinarith [this, hsquare]

private lemma natCast_pow_le_exp_log_of_le {a m : ℕ} {B : ℝ}
    (hB_pos : 0 < B) (ha : (a : ℝ) ≤ B) :
    ((a ^ m : ℕ) : ℝ) ≤ Real.exp ((m : ℝ) * Real.log B) := by
  rw [Nat.cast_pow]
  refine (pow_le_pow_left₀ (by positivity : 0 ≤ (a : ℝ)) ha m).trans_eq ?_
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hB_pos]
  ring_nf

private lemma lower_positive_log_budget {γ C c : ℝ} {n : ℕ} {δ : unitInterval}
    {d : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ)
    (hd : d ∈ Finset.Icc 1 (pairCardThreshold (3 + γ) n δ)) :
    (2 * ((d : ℝ) + 1) +
        4 * lowerBltConstant C γ hC_two hε *
          Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)) *
        Real.log (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ)) ≤
      (ε γ / 2) * ((d : ℝ) + 1) * Real.log (n : ℝ) := by
  rw [add_mul]
  have hd_one : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hmain' :
      2 * ((d : ℝ) + 1) *
          Real.log (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ)) ≤
        (ε γ / 4) * ((d : ℝ) + 1) * Real.log (n : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left
      (lower_counting_base_log_le_epsilon_log_div_eight hγ_pos hγ_le hC_one hc_pos hc_lt hn
        hn_gap hδ_lower hδ_upper hδ_upper_c hC_two hε)
      (by positivity : 0 ≤ 2 * ((d : ℝ) + 1))]
  have hsqrt' :
      4 * lowerBltConstant C γ hC_two hε *
          Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ) *
          Real.log (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ)) ≤
        ε γ * Real.log (n : ℝ) / 2 := by
    nlinarith [lower_c_sqrt_counting_base_log_le_epsilon_log_div_eight
      hγ_pos hγ_le hC_one hc_pos hc_lt hn hn_gap hδ_lower hδ_upper hδ_upper_c hC_two hε]
  have htail :
      ε γ * Real.log (n : ℝ) / 2 ≤
        (ε γ / 4) * ((d : ℝ) + 1) * Real.log (n : ℝ) := by
    ring_nf
    nlinarith [mul_nonneg hε.le
      (le_of_lt ((by norm_num : (0 : ℝ) < 15).trans
        (fifteen_lt_log_of_lowerAnalyticThreshold hn)))]
  nlinarith [hmain', hsqrt', htail]

private lemma lower_negative_log_margin {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    {d : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (_hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hd : d ∈ Finset.Icc 1 (pairCardThreshold (3 + γ) n δ)) :
    (1 + ε γ) * ((d : ℝ) + 1) * Real.log (n : ℝ) ≤
      (1 - 3 * ε γ) * (d : ℝ) * (pairCardThreshold (3 + γ) n δ : ℝ) *
        Real.log (1 / δ) := by
  have hlog_inv_pos := log_one_div_unitInterval_pos
    (zero_lt_one.trans (one_lt_nat_of_lowerSizeThreshold_lt hn)) hδ_lower hδ_upper
  have harg := pairCardThreshold_arg_le (γ := γ) (n := n) (δ := δ)
  rw [div_le_iff₀ hlog_inv_pos] at harg
  have hd_one : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hx_nonneg : 0 ≤ Real.log (n : ℝ) := by
    linarith [fifteen_lt_log_of_lowerAnalyticThreshold hn]
  have hleft :
      2 * (1 + ε γ) * (d : ℝ) * Real.log (n : ℝ) ≤
        (1 - 3 * ε γ) * (d : ℝ) *
          (pairCardThreshold (3 + γ) n δ : ℝ) * Real.log (1 / δ) := by
    nlinarith [
      mul_le_mul_of_nonneg_right (lower_exponent_coefficient hγ_pos hγ_le)
        (mul_nonneg (by positivity : 0 ≤ (d : ℝ)) hx_nonneg),
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left harg (by positivity : 0 ≤ (d : ℝ)))
        (one_sub_three_mul_ε_pos hγ_pos hγ_le).le]
  suffices hcompress :
      (1 + ε γ) * ((d : ℝ) + 1) * Real.log (n : ℝ) ≤
        2 * (1 + ε γ) * (d : ℝ) * Real.log (n : ℝ) by
    exact hcompress.trans hleft
  ring_nf
  nlinarith [mul_nonneg (by nlinarith [ε_pos hγ_pos] : 0 ≤ 1 + ε γ)
    hx_nonneg]

private lemma lower_summand_exponent_le {γ C c : ℝ} {n : ℕ} {δ : unitInterval}
    {d : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ)
    (hd : d ∈ Finset.Icc 1 (pairCardThreshold (3 + γ) n δ)) :
    ((d : ℝ) + 1) * (Real.log (n : ℝ) +
        2 * Real.log (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ))) +
        4 * lowerBltConstant C γ hC_two hε *
          Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ) *
          Real.log (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ)) -
        (1 - 3 * ε γ) * (d : ℝ) *
          (pairCardThreshold (3 + γ) n δ : ℝ) * Real.log (1 / δ) ≤
      -(ε γ / 2) * Real.log (n : ℝ) := by
  have hneg := lower_negative_log_margin hγ_pos hγ_le hC_one hn hδ_lower hδ_upper hd
  have hd_one : (1 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hpos' :
      2 * ((d : ℝ) + 1) *
          Real.log (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ)) +
          4 * lowerBltConstant C γ hC_two hε *
            Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ) *
            Real.log (3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ)) ≤
        (ε γ / 2) * ((d : ℝ) + 1) * Real.log (n : ℝ) := by
    simpa [add_mul] using
      lower_positive_log_budget hγ_pos hγ_le hC_one hc_pos hc_lt hn hn_gap hδ_lower
        hδ_upper hδ_upper_c hC_two hε hd
  have hlast :
      -(ε γ / 2) * ((d : ℝ) + 1) * Real.log (n : ℝ) ≤
        -(ε γ / 2) * Real.log (n : ℝ) := by
    nlinarith [
      mul_le_mul_of_nonneg_left (by nlinarith [hd_one] : (1 : ℝ) ≤ (d : ℝ) + 1)
        (by nlinarith [hε, fifteen_lt_log_of_lowerAnalyticThreshold hn] :
          0 ≤ (ε γ / 2) * Real.log (n : ℝ))]
  nlinarith [hpos', hneg, hlast]

private lemma lower_fingerprint_factor_le_exp {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    ((((⌈lowerBltConstant C γ hC_two hε *
          Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ + 1) *
        (⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ + 1) ^
          ⌈lowerBltConstant C γ hC_two hε *
            Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ : ℕ) : ℝ) *
      (((⌈lowerBltConstant C γ hC_two hε *
          Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ + 1) *
        (⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ + 1) ^
          ⌈lowerBltConstant C γ hC_two hε *
            Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ : ℕ) : ℝ)) ≤
      Real.exp (4 * lowerBltConstant C γ hC_two hε *
        Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ) *
        Real.log (3 * lowerConstant C γ hC_two hε *
          (pairCardThreshold (3 + γ) n δ : ℝ))) := by
  let M := ⌈lowerBltConstant C γ hC_two hε *
    Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)⌉₊
  let s := ⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊
  let B := 3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ)
  let T := lowerBltConstant C γ hC_two hε *
    Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)
  have hB_pos : 0 < B := by
    dsimp [B]
    exact lower_counting_base_pos hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε
  have hB_one : 1 ≤ B := by
    dsimp [B]
    exact one_le_lower_counting_base hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε
  have hlogB_nonneg : 0 ≤ Real.log B := Real.log_nonneg hB_one
  have hMsucc_le_T : ((M + 1 : ℕ) : ℝ) ≤ 2 * T := by
    dsimp [M, T]
    simpa [mul_assoc] using
      lower_blt_ceiling_succ_le_two_mul hγ_pos hγ_le hC_one hn hδ_lower hδ_upper
        hC_two hε
  have hMsucc_le_B : ((M + 1 : ℕ) : ℝ) ≤ B := by
    dsimp [M, B]
    exact blt_ceiling_succ_le_lower_counting_base hγ_pos hγ_le hC_one hn hδ_lower hδ_upper hC_two hε
  have hs_succ_le_B : ((s + 1 : ℕ) : ℝ) ≤ B := by
    dsimp [s, B]
    exact changCarrierBound_ceil_succ_le_three_mul_lowerConstant hγ_pos hC_one hn hδ_lower
      hδ_upper hC_two hε
  have hMexp : ((M + 1 : ℕ) : ℝ) ≤ Real.exp (Real.log B) := by
    rw [Real.exp_log hB_pos]
    exact hMsucc_le_B
  have hpow :
      (((s + 1) ^ M : ℕ) : ℝ) ≤ Real.exp ((M : ℝ) * Real.log B) :=
    natCast_pow_le_exp_log_of_le hB_pos hs_succ_le_B
  have hone :
      (((M + 1) * (s + 1) ^ M : ℕ) : ℝ) ≤
        Real.exp (((M + 1 : ℕ) : ℝ) * Real.log B) := by
    rw [Nat.cast_mul]
    refine (mul_le_mul hMexp hpow (by positivity) (by positivity)).trans_eq ?_
    rw [← Real.exp_add]
    congr 1
    rw [Nat.cast_add, Nat.cast_one]
    ring
  refine (mul_le_mul hone hone (by positivity) (by positivity)).trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [hMsucc_le_T, hlogB_nonneg]

private lemma lower_gap_count_le_exp {γ C : ℝ} {n : ℕ} {δ : unitInterval} {d : ℕ}
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hC_one : 1 ≤ C) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ) :
    ((properGAPsZModOfDim d
        ⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊
        (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).pos).card : ℝ) ≤
      Real.exp (((d : ℝ) + 1) * (Real.log (n : ℝ) +
        2 * Real.log (3 * lowerConstant C γ hC_two hε *
          (pairCardThreshold (3 + γ) n δ : ℝ)))) := by
  let q := zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn
  let s := ⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊
  let B := 3 * lowerConstant C γ hC_two hε * (pairCardThreshold (3 + γ) n δ : ℝ)
  have hB_pos : 0 < B := by
    dsimp [B]
    exact lower_counting_base_pos hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε
  have hB_one : 1 ≤ B := by
    dsimp [B]
    exact one_le_lower_counting_base hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε
  have hlogB_nonneg : 0 ≤ Real.log B := Real.log_nonneg hB_one
  have hn_pos : 0 < (n : ℝ) := old_model_threshold_nat_pos hn
  have hq_le : (q : ℝ) ≤ (n : ℝ) * B := by
    dsimp [q, B]
    exact zmodModelQ_le_n_mul_lower_counting_base hγ_pos C_pos hC_one hn hδ_lower hδ_upper hC_two hε
  have hs_pos : 0 < s := by
    dsimp [s]
    exact lower_chang_carrier_ceil_pos hγ_pos hC_one hn hδ_lower hδ_upper
  have hs_le : (s : ℝ) ≤ B := by
    dsimp [s, B]
    exact changCarrierBound_ceil_le_lower_counting_base hγ_pos hC_one hn hδ_lower hδ_upper hC_two hε
  refine (by
    dsimp [q, s]
    exact_mod_cast properGAPsZModOfDim_card
      (lower_chang_carrier_ceil_pos hγ_pos hC_one hn hδ_lower hδ_upper)
      (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).pos :
    ((properGAPsZModOfDim d
        ⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊
        (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).pos).card : ℝ) ≤
      ((q ^ (d + 1) * s ^ d : ℕ) : ℝ)).trans ?_
  have hqpow :
      (((q ^ (d + 1) : ℕ) : ℝ)) ≤
        Real.exp (((d + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) * B)) :=
    natCast_pow_le_exp_log_of_le (mul_pos hn_pos hB_pos) hq_le
  have hspow :
      (((s ^ d : ℕ) : ℝ)) ≤ Real.exp ((d : ℝ) * Real.log B) :=
    natCast_pow_le_exp_log_of_le hB_pos hs_le
  refine (by
    rw [Nat.cast_mul]
    exact mul_le_mul hqpow hspow (by positivity) (by positivity) :
    ((q ^ (d + 1) * s ^ d : ℕ) : ℝ) ≤
      Real.exp (((d + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) * B)) *
        Real.exp ((d : ℝ) * Real.log B)).trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [Real.log_mul hn_pos.ne' hB_pos.ne']
  rw [Nat.cast_add, Nat.cast_one]
  nlinarith

private lemma lower_gap_dim_summand_le {γ C c : ℝ} {n : ℕ} {δ : unitInterval} {d : ℕ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (C_pos : 0 < C) (hC_one : 1 ≤ C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c)
    (hC_two : 0 < 2 * C) (hε : 0 < ε γ)
    (hd : d ∈ Finset.Icc 1 (pairCardThreshold (3 + γ) n δ)) :
    ((properGAPsZModOfDim d
        ⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊
        (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).pos).card : ℝ) *
        ((((⌈lowerBltConstant C γ hC_two hε *
              Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ + 1) *
            (⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ + 1) ^
              ⌈lowerBltConstant C γ hC_two hε *
                Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ : ℕ) : ℝ) *
          (((⌈lowerBltConstant C γ hC_two hε *
              Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ + 1) *
            (⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ + 1) ^
              ⌈lowerBltConstant C γ hC_two hε *
                Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ : ℕ) : ℝ)) *
        Real.exp (-((1 - 3 * ε γ) * (d : ℝ) *
            (pairCardThreshold (3 + γ) n δ : ℝ)) * Real.log (1 / δ)) ≤
      (n : ℝ) ^ (-(ε γ / 2)) := by
  refine (mul_le_mul_of_nonneg_right
      (mul_le_mul
        (lower_gap_count_le_exp hγ_pos C_pos hC_one hn hδ_lower hδ_upper hC_two hε)
        (lower_fingerprint_factor_le_exp hγ_pos hγ_le hC_one hn hδ_lower hδ_upper
          hC_two hε)
        (by positivity)
        (by positivity))
      (by positivity)).trans ?_
  rw [← Real.exp_add, ← Real.exp_add]
  rw [Real.rpow_def_of_pos (old_model_threshold_nat_pos hn)]
  rw [mul_comm (Real.log (n : ℝ)) (-(ε γ / 2))]
  apply Real.exp_le_exp.mpr
  simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
    lower_summand_exponent_le hγ_pos hγ_le hC_one hc_pos hc_lt hn hn_gap hδ_lower
      hδ_upper hδ_upper_c hC_two hε hd

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

abbrev smallSumsetMeasure (n : ℕ) (δ : unitInterval) :
    MeasureTheory.Measure (Finset ℕ) :=
  binomialFinsetSubset (Set.Icc 1 n) δ

theorem small_sumset_pair_probability_le_fingerprint_sum {γ C c : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (C_pos : 0 < C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c) :
    (smallSumsetMeasure n δ).real
        (pairSumsetIsSubset n (pairCardThreshold (3 + γ) n δ) 0
          (C * pairCardThreshold (3 + γ) n δ)) ≤
      ∑ P ∈ lowerModelGAPs (γ := γ) (C := C) (n := n) δ hγ_pos C_pos hn,
        ∑ p ∈ bltDimSmallWitnessPairs
            (zmodGAPPreimageContainer n
              (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) P)
            P.dim (pairCardThreshold (3 + γ) n δ) C γ,
          (δ : ℝ) ^ (p.1 + p.2).card := by
  classical
  refine le_trans (b := (smallSumsetMeasure n δ).real
      (⋃ P ∈ lowerModelGAPs (γ := γ) (C := C) (n := n) δ hγ_pos C_pos hn,
        ⋃ p ∈ bltDimSmallWitnessPairs
            (zmodGAPPreimageContainer n
              (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) P)
            P.dim (pairCardThreshold (3 + γ) n δ) C γ,
          {S : Finset ℕ | bltWitnessPairSumsetIsSubset p S})) ?_ ?_
  · change (smallSumsetMeasure n δ).real
      {S : Finset ℕ |
        pairSumsetIsSubset n (pairCardThreshold (3 + γ) n δ) 0
          (C * pairCardThreshold (3 + γ) n δ) S} ≤ _
    rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def]
    exact ENNReal.toReal_mono (MeasureTheory.measure_ne_top (smallSumsetMeasure n δ) _)
      (MeasureTheory.measure_mono (by
        simpa using
          pairSumsetIsSubset_event_subset_zmodGAPPreimageDimSmallWitnessPairs
            (γ := γ) (C := C) (c := c) (n := n) (δ := δ)
            hγ_pos hγ_le C_pos hc_pos hc_lt hn hn_gap hδ_lower hδ_upper hδ_upper_c))
  refine (MeasureTheory.measureReal_biUnion_finset_le
    (lowerModelGAPs (γ := γ) (C := C) (n := n) δ hγ_pos C_pos hn)
    (fun P =>
      ⋃ p ∈ bltDimSmallWitnessPairs
          (zmodGAPPreimageContainer n
            (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) P)
          P.dim (pairCardThreshold (3 + γ) n δ) C γ,
        {S : Finset ℕ | bltWitnessPairSumsetIsSubset p S})).trans ?_
  refine Finset.sum_le_sum ?_
  intro P _hP
  refine (MeasureTheory.measureReal_biUnion_finset_le
    (bltDimSmallWitnessPairs
      (zmodGAPPreimageContainer n
        (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) P)
      P.dim (pairCardThreshold (3 + γ) n δ) C γ)
    (fun p => {S : Finset ℕ | bltWitnessPairSumsetIsSubset p S})).trans ?_
  refine Finset.sum_le_sum ?_
  intro p _hp
  simpa [smallSumsetMeasure] using bltWitnessPair_probability_le n (δ := δ) p

private lemma lower_dim_fingerprint_sum_bound {γ C c : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (C_pos : 0 < C) (hC_one : 1 ≤ C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c) :
      ∑ P ∈ lowerModelGAPs (γ := γ) (C := C) (n := n) δ hγ_pos C_pos hn,
        ∑ p ∈ bltDimSmallWitnessPairs
            (zmodGAPPreimageContainer n
              (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) P)
            P.dim (pairCardThreshold (3 + γ) n δ) C γ,
          (δ : ℝ) ^ (p.1 + p.2).card ≤
      2 * (pairCardThreshold (3 + γ) n δ : ℝ) / (n : ℝ) ^ (ε γ / 2) := by
  classical
  have hC_two : 0 < 2 * C := by positivity
  have hε : 0 < ε γ := ε_pos hγ_pos
  have hδ_pos : 0 < (δ : ℝ) := unitInterval_pos_of_density_lower hn hδ_lower
  have hδ_lt : (δ : ℝ) < 1 := unitInterval_lt_one hδ_upper
  have hkpos : 0 < pairCardThreshold (3 + γ) n δ :=
    pairCardThreshold_pos_of_lower_density hγ_pos hn hδ_lower hδ_upper
  refine le_trans (b :=
    ∑ d ∈ Finset.Icc 1 (pairCardThreshold (3 + γ) n δ),
      ((properGAPsZModOfDim d
        ⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊
        (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).pos).card : ℝ) *
          ((((⌈lowerBltConstant C γ hC_two hε *
                Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ + 1) *
              (⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ + 1) ^
                ⌈lowerBltConstant C γ hC_two hε *
                  Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ : ℕ) : ℝ) *
            (((⌈lowerBltConstant C γ hC_two hε *
                Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ + 1) *
              (⌈changCarrierBound (2 * pairCardThreshold (3 + γ) n δ) (κ C)⌉₊ + 1) ^
                ⌈lowerBltConstant C γ hC_two hε *
                  Real.sqrt (pairCardThreshold (3 + γ) n δ : ℝ)⌉₊ : ℕ) : ℝ)) *
          Real.exp (-((1 - 3 * ε γ) * (d : ℝ) *
            (pairCardThreshold (3 + γ) n δ : ℝ)) * Real.log (1 / δ))) ?_ ?_
  · simpa [lowerModelGAPs] using
      dim_fingerprint_sum_le_gap_dim_sum
        (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn)
        (zmodModelQ_prime (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).pos
        (zmodModelEmbedding_iso (γ := γ) (C := C) (n := n) hγ_pos C_pos hn).bijOn.injOn
        hC_two hε hδ_pos hδ_lt
  refine le_trans (b := ∑ d ∈ Finset.Icc 1 (pairCardThreshold (3 + γ) n δ),
    (n : ℝ) ^ (-(ε γ / 2))) ?_ ?_
  · refine Finset.sum_le_sum ?_
    intro d hd
    exact lower_gap_dim_summand_le hγ_pos hγ_le C_pos hC_one hc_pos hc_lt hn hn_gap
      hδ_lower hδ_upper hδ_upper_c hC_two hε hd
  · rw [Finset.sum_const, nsmul_eq_mul]
    have hcoef : ((Finset.Icc 1 (pairCardThreshold (3 + γ) n δ)).card : ℝ) ≤
        2 * (pairCardThreshold (3 + γ) n δ : ℝ) := by
      have hcard : ((Finset.Icc 1 (pairCardThreshold (3 + γ) n δ)).card : ℝ) ≤
          (pairCardThreshold (3 + γ) n δ : ℝ) := by
        rw [Nat.card_Icc]
        exact_mod_cast (Nat.succ_sub_one
          (pairCardThreshold (3 + γ) n δ)).le
      nlinarith [hcard, ((by exact_mod_cast hkpos) :
        (0 : ℝ) < pairCardThreshold (3 + γ) n δ)]
    refine (mul_le_mul_of_nonneg_right hcoef (by positivity)).trans ?_
    rw [Real.rpow_neg (le_of_lt (old_model_threshold_nat_pos hn))]
    ring_nf
    exact le_rfl

/-- Probability estimate for pairs with a small sumset. -/
theorem small_sumset_pair_probability_le {γ C c : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (C_pos : 0 < C) (hc_pos : 0 < c)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ))
    (hδ_upper : (δ : ℝ) ≤ 1 - c) :
    (smallSumsetMeasure n δ).real
        (pairSumsetIsSubset n (pairCardThreshold (3 + γ) n δ) 0
          (C * pairCardThreshold (3 + γ) n δ)) ≤
      2 * (pairCardThreshold (3 + γ) n δ : ℝ) / (n : ℝ) ^ (ε γ / 2) := by
  have hn : lowerSizeThreshold C γ < n := (lowerSizeThreshold_le_lowerGapThreshold C γ
    c).trans_lt hn_gap
  have hδ_pos : 0 < (δ : ℝ) := unitInterval_pos_of_density_lower hn hδ_lower
  have hc_lt : c < 1 := by linarith
  have hδ_lt : (δ : ℝ) < 1 := by linarith
  by_cases hC_one : 1 ≤ C
  · exact (small_sumset_pair_probability_le_fingerprint_sum
      hγ_pos hγ_le C_pos hc_pos hc_lt
      hn hn_gap hδ_lower hδ_lt hδ_upper).trans
      (lower_dim_fingerprint_sum_bound hγ_pos hγ_le C_pos hC_one hc_pos hc_lt hn hn_gap
        hδ_lower hδ_lt hδ_upper)
  · change (smallSumsetMeasure n δ).real
        {S : Finset ℕ |
          pairSumsetIsSubset n (pairCardThreshold (3 + γ) n δ) 0
            (C * pairCardThreshold (3 + γ) n δ) S} ≤
        2 * (pairCardThreshold (3 + γ) n δ : ℝ) / (n : ℝ) ^ (ε γ / 2)
    rw [(Set.eq_empty_iff_forall_notMem (s := {S : Finset ℕ |
        pairSumsetIsSubset n (pairCardThreshold (3 + γ) n δ) 0
          (C * pairCardThreshold (3 + γ) n δ) S})).mpr (by
      intro S hS
      rcases hS with ⟨A, B, _hAint, _hBint, hAcard, hBcard, _hAB_lower, hAB, _hAB_subset⟩
      exact hC_one
        (one_le_sumset_card_coefficient_of_threshold_pair_sumset hγ_pos hn hδ_lower hδ_lt hAcard
          hBcard
          hAB))]
    rw [MeasureTheory.measureReal_def]
    simp only [MeasureTheory.measure_empty, ENNReal.toReal_zero]
    positivity

end

end DenseSetsWithoutLargeSumsets
