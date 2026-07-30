/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.Constants
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.FreimanDimension
import DenseSetsWithoutLargeSumsets.Probability
import DenseSetsWithoutLargeSumsets.Common
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.GeneralizedArithmeticProgression
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.LargeSumsetsFromMediumSizedSubsets.MediumSizedSubsets
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.Chang.Reduction
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.NumberTheory.Bertrand

/-!
GAP preimage containers and BLT witness pairs.

Defines `zmodGAPPreimageContainer`, the preimage in `interval n` of a proper GAP under the
model embedding, and the finite sets of BLT fingerprint pairs (`bltSmallWitnessPairs`,
`bltDimSmallWitnessPairs`) whose sumset a small-sumset pair must land in, together with the
cardinality bounds used to count them.
-/

namespace DenseSetsWithoutLargeSumsets

open Nat hiding div_pos
open scoped Pointwise

noncomputable section

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

lemma properGAP_card_eq_one_of_dim_zero {G : Type*} [DecidableEq G] [AddCommMonoid G]
    (P : ProperGAP G) (hPdim : P.dim = 0) : P.carrier.card = 1 := by
  rcases P with ⟨dim, carrier, origin, step, length, length_one_lt, carrier_eq, proper⟩
  dsimp at hPdim ⊢
  subst dim
  rw [carrier_eq]
  simp [gapMap]

lemma natCastImage_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    natCastImage A ⊆ natCastImage B := by
  intro z hz
  rw [natCastImage] at hz ⊢
  rcases Finset.mem_image.mp hz with ⟨a, ha, rfl⟩
  exact Finset.mem_image.mpr ⟨a, hAB ha, rfl⟩

lemma natCastImage_filter_mem_eq_of_subset {A : Finset ℕ} {T : Finset ℤ}
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

lemma natCastImage_add_subset {A B S : Finset ℕ} {A' B' : Finset ℤ}
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

lemma bltDimSmallWitnessPairs_card_le (P : Finset ℕ) (D k : ℕ) (C γ : ℝ)
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


end

end DenseSetsWithoutLargeSumsets
