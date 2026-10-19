/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.Constants

/-!
# Progressions and pairs of small subsets

The union bound of Section 2 of *Dense sets without large sumsets* (Dahia, Marciano, Souza) runs
over the proper generalized arithmetic progressions `P` of `ZMod q` and over the pairs `(A', B')`
of small subsets of the preimage of `P` in `[n]` with a large sumset. Here `A'` and `B'` are the
sets of size about `√k` given by Theorem 2 of Bollobás, Leader and Tiba. This file defines these
families and bounds the number of pairs.

## Main definitions

* `zmodGAPPreimageContainer n ψ P`: the elements of `[n]` that `ψ` maps into `P`.
* `bltSmallWitnessPairs Q k C γ`: the pairs of subsets of `Q`, as sets of integers, of size at
  most `lowerBltConstant C γ * √k`.
* `bltDimSmallWitnessPairs Q D k C γ`: the pairs `(A', B')` in `bltSmallWitnessPairs Q k C γ` with
  `|A' + B'| ≥ (1 - 3 * ε γ) * D * k`, for `D ≥ 1`.
* `bltWitnessPairSumsetIsSubset p S`: the sumset of the pair `p` is contained in `S`.
* `properGAPsZModUpToDim D s hq`: the proper progressions of dimension at most `D` with at most
  `s` points in `ZMod q`.

## Main statements

* `zmodGAPPreimageContainer_card_le_carrier`: if `ψ` is injective on `[n]`, then
  `zmodGAPPreimageContainer n ψ P` has at most `|P|` elements.
* `bltDimSmallWitnessPairs_card_le`: with `m = ⌈lowerBltConstant C γ * √k⌉₊`, there are at most
  `((m + 1) * (|Q| + 1) ^ m) ^ 2` pairs in `bltDimSmallWitnessPairs Q D k C γ`.
-/

@[expose] public section

namespace DenseSetsWithoutLargeSumsets

open Finset ChangFreimanRuzsa
open scoped Pointwise

noncomputable section

/-- The elements of `[n]` that `ψ` maps into the progression `P`. -/
def zmodGAPPreimageContainer {q : ℕ} (n : ℕ) (ψ : ℕ → ZMod q)
    (P : GAP (ZMod q)) : Finset ℕ :=
  (interval n).filter fun x ↦ ψ x ∈ P.carrier

lemma zmodGAPPreimageContainer_card_le_carrier {q n : ℕ} {ψ : ℕ → ZMod q}
    (P : GAP (ZMod q)) (hψinj : Set.InjOn ψ (interval n : Set ℕ)) :
    #(zmodGAPPreimageContainer n ψ P) ≤ #P.carrier := by
  rw [zmodGAPPreimageContainer,
    ← card_image_of_injOn (hψinj.mono (coe_subset.2 (filter_subset _ _)))]
  exact card_le_card (image_subset_iff.2 fun x hx ↦ (mem_filter.1 hx).2)

lemma natCastImage_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    natCastImage A ⊆ natCastImage B :=
  image_subset_image hAB

lemma natCastImage_filter_mem_eq_of_subset {A : Finset ℕ} {T : Finset ℤ}
    (hT : T ⊆ natCastImage A) :
    natCastImage (A.filter fun a ↦ (a : ℤ) ∈ T) = T := by
  ext z
  refine ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩
  · obtain ⟨a, ha, rfl⟩ := mem_image.1 hz
    exact (mem_filter.1 ha).2
  · obtain ⟨a, ha, rfl⟩ := mem_image.1 (hT hz)
    exact mem_image.2 ⟨a, mem_filter.2 ⟨ha, hz⟩, rfl⟩

lemma natCastImage_add_subset {A B S : Finset ℕ} {A' B' : Finset ℤ}
    (hA' : A' ⊆ natCastImage A) (hB' : B' ⊆ natCastImage B)
    (hAB : A + B ⊆ S) :
    A' + B' ⊆ natCastImage S := by
  refine (add_subset_add hA' hB').trans ?_
  rw [← natCastImage_add]
  exact natCastImage_mono hAB

/-- The pairs `(A', B')` of sets of integers that are images of subsets of `P` and have at most
`lowerBltConstant C γ * √k` elements each. -/
def bltSmallWitnessPairs (P : Finset ℕ) (k : ℕ) (C γ : ℝ) :
    Finset (Finset ℤ × Finset ℤ) :=
  ((natCastImage P).powerset ×ˢ (natCastImage P).powerset).filter fun p ↦
    ∃ (hC : 0 < 2 * C) (hε : 0 < ε γ),
      (p.1.card : ℝ) ≤ lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ) ∧
        (p.2.card : ℝ) ≤ lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)

/-- The pairs `(A', B')` in `bltSmallWitnessPairs P k C γ` with
`|A' + B'| ≥ (1 - 3 * ε γ) * D * k`, where `D ≥ 1`. For `D = 0` the family is empty. -/
def bltDimSmallWitnessPairs (P : Finset ℕ) (D k : ℕ) (C γ : ℝ) :
    Finset (Finset ℤ × Finset ℤ) := by
  classical
  exact (bltSmallWitnessPairs P k C γ).filter fun p ↦
    1 ≤ D ∧ (1 - 3 * ε γ) * (D : ℝ) * (k : ℝ) ≤ ((p.1 + p.2).card : ℝ)

/-- The sumset of the pair `p` of sets of integers is contained in the image of `S`. -/
def bltWitnessPairSumsetIsSubset (p : Finset ℤ × Finset ℤ) (S : Finset ℕ) : Prop :=
  p.1 + p.2 ⊆ natCastImage S

/-- The proper progressions of dimension at most `D` with at most `s` points in `ZMod q`. -/
def properGAPsZModUpToDim {q : ℕ} (D s : ℕ) (hq : 0 < q) :
    Finset (GAP (ZMod q)) := by
  classical
  exact (Finset.range (D + 1)).biUnion fun d ↦ properGAPsZModOfDim d s hq

lemma mem_properGAPsZModUpToDim {q D s : ℕ} (hq : 0 < q) {P : GAP (ZMod q)} :
    P ∈ properGAPsZModUpToDim D s hq ↔ P.Proper ∧ P.dim ≤ D ∧ #P.carrier ≤ s := by
  simp only [properGAPsZModUpToDim, mem_biUnion, mem_range, mem_properGAPsZModOfDim]
  grind

private lemma card_powerset_filter_card_le {α : Type*} (U : Finset α) (M : ℕ) :
    #(U.powerset.filter fun A ↦ #A ≤ M) ≤ (M + 1) * (#U + 1) ^ M := by
  classical
  have hsub : (U.powerset.filter fun A ↦ #A ≤ M) ⊆ (range (M + 1)).biUnion U.powersetCard := by
    intro A hA
    rw [mem_filter, mem_powerset] at hA
    exact mem_biUnion.2 ⟨#A, by grind, mem_powersetCard.2 ⟨hA.1, rfl⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  refine (sum_le_sum (g := fun _ ↦ (#U + 1) ^ M) fun i hi ↦ ?_).trans_eq (by simp)
  rw [card_powersetCard]
  exact (Nat.choose_le_pow _ _).trans ((Nat.pow_le_pow_left (Nat.le_succ _) i).trans
    (Nat.pow_le_pow_right (Nat.succ_pos _) (mem_range_succ_iff.1 hi)))

/-- With `m = ⌈lowerBltConstant C γ * √k⌉₊`, there are at most `((m + 1) * (|P| + 1) ^ m) ^ 2`
pairs in `bltDimSmallWitnessPairs P D k C γ`. -/
lemma bltDimSmallWitnessPairs_card_le (P : Finset ℕ) (D k : ℕ) (C γ : ℝ)
    (hC : 0 < 2 * C) (hε : 0 < ε γ) :
    #(bltDimSmallWitnessPairs P D k C γ) ≤
      (((⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1) *
          (#(natCastImage P) + 1) ^
            ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊) *
        ((⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊ + 1) *
          (#(natCastImage P) + 1) ^
            ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊)) := by
  classical
  refine (card_le_card (t :=
    ((natCastImage P).powerset.filter fun A ↦
      #A ≤ ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊) ×ˢ
    ((natCastImage P).powerset.filter fun A ↦
      #A ≤ ⌈lowerBltConstant C γ hC hε * Real.sqrt (k : ℝ)⌉₊)) ?_).trans ?_
  · intro p hp
    rw [bltDimSmallWitnessPairs, mem_filter, bltSmallWitnessPairs, mem_filter, mem_product] at hp
    obtain ⟨⟨hp, _, _, h₁, h₂⟩, -⟩ := hp
    rw [mem_product, mem_filter, mem_filter]
    exact ⟨⟨hp.1, Nat.cast_le.1 (h₁.trans (Nat.le_ceil _))⟩,
      ⟨hp.2, Nat.cast_le.1 (h₂.trans (Nat.le_ceil _))⟩⟩
  · rw [card_product]
    exact Nat.mul_le_mul (card_powerset_filter_card_le _ _) (card_powerset_filter_card_le _ _)

end

end DenseSetsWithoutLargeSumsets
