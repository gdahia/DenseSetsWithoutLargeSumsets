/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.FreimanDimension
import DenseSetsWithoutLargeSumsets.Common

/-!
# Freiman-isomorphism classes

This file formalizes the Freiman-isomorphism machinery from Section 3 of Green's paper
`Counting sets with small sumset, and the clique number of random Cayley graphs`. Its public
results follow the paper's progression: encode additive relation systems, pass from labeled
tuples to isomorphism classes, introduce Freiman dimension and determining coordinates, and
finally count bounded-dimension realizations. The restricted-sumset and extension-code lemmas
needed by Section 4 are developed alongside the relation encodings they use.

The source of version 2 is available at <https://arxiv.org/e-print/math/0304183>.
-/

namespace DenseSetsWithoutLargeSumsets

open scoped Pointwise

noncomputable section

/-! ### Freiman relation systems and finite codes -/

abbrev FreimanRelationIndex (s t : ℕ) :=
  (Fin s → Fin t) × (Fin s → Fin t)

private noncomputable instance freimanRelationCodeLinearOrder (s t : ℕ) :
    LinearOrder (Fin t → FreimanRelationIndex s t) :=
  LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective

private def freimanRelationVector {s t : ℕ} (p : FreimanRelationIndex s t) :
    Fin t →₀ ℚ :=
  (∑ i, Finsupp.single (p.1 i) 1) - ∑ i, Finsupp.single (p.2 i) 1

def freimanRelationHolds {s t : ℕ} (a : Fin t → ℕ)
    (p : FreimanRelationIndex s t) : Prop :=
  ∑ i, a (p.1 i) = ∑ i, a (p.2 i)

private def rationalTupleEval {t : ℕ} (a : Fin t → ℕ) :
    (Fin t →₀ ℚ) →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ fun i ↦ (a i : ℚ)

private lemma rationalTupleEval_freimanRelationVector {s t : ℕ} (a : Fin t → ℕ)
    (p : FreimanRelationIndex s t) :
    rationalTupleEval a (freimanRelationVector p) =
      (∑ i, (a (p.1 i) : ℚ)) - ∑ i, (a (p.2 i) : ℚ) := by
  simp only [rationalTupleEval, freimanRelationVector, map_sub, map_sum,
    Finsupp.linearCombination_single, one_smul]

private lemma freimanRelationVector_mem_ker_iff {s t : ℕ} (a : Fin t → ℕ)
    (p : FreimanRelationIndex s t) :
    freimanRelationVector p ∈ LinearMap.ker (rationalTupleEval a) ↔
      freimanRelationHolds a p := by
  rw [LinearMap.mem_ker, rationalTupleEval_freimanRelationVector]
  unfold freimanRelationHolds
  rw [sub_eq_zero]
  exact_mod_cast Iff.rfl

private def freimanRelationSpace {s t : ℕ} (a : Fin t → ℕ) :
    Submodule ℚ (Fin t →₀ ℚ) :=
  Submodule.span ℚ (freimanRelationVector (s := s) ''
    {p : FreimanRelationIndex s t | freimanRelationHolds a p})

private lemma freimanRelation_iff_mem_space {s t : ℕ} (a : Fin t → ℕ)
    (p : FreimanRelationIndex s t) :
    freimanRelationHolds a p ↔
      freimanRelationVector p ∈ freimanRelationSpace (s := s) a := by
  constructor
  · intro hp
    exact Submodule.subset_span ⟨p, hp, rfl⟩
  · intro hp
    rw [← freimanRelationVector_mem_ker_iff]
    exact (Submodule.span_le.mpr fun _ h ↦ by
      obtain ⟨q, hq, rfl⟩ := h
      exact (freimanRelationVector_mem_ker_iff a q).mpr hq) hp

private lemma finrank_freimanRelationSpace_le {s t : ℕ} (a : Fin t → ℕ) :
    Module.finrank ℚ (freimanRelationSpace (s := s) a) ≤ t := by
  refine (freimanRelationSpace (s := s) a).finrank_le.trans_eq ?_
  simp

private lemma freimanRelationVector_reflexive_zero {s t : ℕ} (p : Fin s → Fin t) :
    freimanRelationVector (p, p) = 0 := by
  unfold freimanRelationVector
  exact sub_self _

/-- Green's spanning argument: at most `t` many `s`-relations determine every `s`-relation
of a labeled `t`-set. -/
private lemma exists_freimanRelationCode {s t : ℕ} (ht : 0 < t) (a : Fin t → ℕ) :
    ∃ code : Fin t → FreimanRelationIndex s t,
      Submodule.span ℚ (freimanRelationVector '' Set.range code) =
        freimanRelationSpace (s := s) a := by
  let relations : Set (Fin t →₀ ℚ) := freimanRelationVector ''
    {p : FreimanRelationIndex s t | freimanRelationHolds a p}
  obtain ⟨basis, hbasis_mem, hbasis_span, -⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ relations
  let d := Module.finrank ℚ (Submodule.span ℚ relations)
  have hdt : d ≤ t := by
    change Module.finrank ℚ (freimanRelationSpace a) ≤ t
    exact finrank_freimanRelationSpace_le a
  let index : Fin d → FreimanRelationIndex s t :=
    fun i ↦ Classical.choose (hbasis_mem i)
  have hindex (i : Fin d) : freimanRelationVector (index i) = basis i :=
    (Classical.choose_spec (hbasis_mem i)).2
  let i₀ : Fin t := ⟨0, ht⟩
  let zeroIndex : FreimanRelationIndex s t := (fun _ ↦ i₀, fun _ ↦ i₀)
  have hzero : freimanRelationVector zeroIndex = 0 :=
    freimanRelationVector_reflexive_zero _
  let code : Fin t → FreimanRelationIndex s t := fun i ↦
    if hi : i.val < d then index ⟨i.val, hi⟩ else zeroIndex
  refine ⟨code, ?_⟩
  change Submodule.span ℚ (freimanRelationVector '' Set.range code) =
    Submodule.span ℚ relations
  rw [← hbasis_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    by_cases hi : i.val < d
    · dsimp only [code]
      rw [dif_pos hi, hindex]
      exact Submodule.subset_span ⟨⟨i.val, hi⟩, rfl⟩
    · dsimp only [code]
      rw [dif_neg hi, hzero]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    let j : Fin t := ⟨i.val, lt_of_lt_of_le i.isLt hdt⟩
    rw [← hindex]
    refine Submodule.subset_span ⟨index i, ⟨j, ?_⟩, rfl⟩
    have hj : j.val < d := i.isLt
    simp [code, hj, j]

private def freimanRelationCodes {s t : ℕ} (a : Fin t → ℕ) :
    Finset (Fin t → FreimanRelationIndex s t) :=
  Finset.univ.filter fun code ↦
    Submodule.span ℚ (freimanRelationVector '' Set.range code) =
      freimanRelationSpace (s := s) a

private lemma freimanRelationCodes_nonempty {s t : ℕ} (ht : 0 < t)
    (a : Fin t → ℕ) : (freimanRelationCodes (s := s) a).Nonempty := by
  obtain ⟨code, hcode⟩ := exists_freimanRelationCode (s := s) ht a
  refine ⟨code, ?_⟩
  simp [freimanRelationCodes, hcode]

noncomputable def freimanRelationCode {s t : ℕ} (ht : 0 < t)
    (a : Fin t → ℕ) : Fin t → FreimanRelationIndex s t :=
  (freimanRelationCodes (s := s) a).min'
    (freimanRelationCodes_nonempty (s := s) ht a)

private lemma freimanRelationCode_span {s t : ℕ} (ht : 0 < t) (a : Fin t → ℕ) :
    Submodule.span ℚ
      (freimanRelationVector '' Set.range (freimanRelationCode (s := s) ht a)) =
        freimanRelationSpace (s := s) a := by
  unfold freimanRelationCode
  have hmem := Finset.min'_mem (freimanRelationCodes (s := s) a)
    (freimanRelationCodes_nonempty (s := s) ht a)
  exact (Finset.mem_filter.mp hmem).2

private lemma freimanRelationCode_eq_of_space_eq {s t : ℕ} (ht : 0 < t)
    {a b : Fin t → ℕ}
    (hspace : freimanRelationSpace (s := s) a = freimanRelationSpace (s := s) b) :
    freimanRelationCode (s := s) ht a = freimanRelationCode ht b := by
  letI : LinearOrder (Fin t → FreimanRelationIndex s t) :=
    freimanRelationCodeLinearOrder s t
  have hcodes : freimanRelationCodes (s := s) a = freimanRelationCodes (s := s) b := by
    unfold freimanRelationCodes
    rw [hspace]
  unfold freimanRelationCode
  apply (Finset.min'_eq_iff
    (s := freimanRelationCodes (s := s) a)
    (H := freimanRelationCodes_nonempty (s := s) ht a)
    ((freimanRelationCodes (s := s) b).min'
      (freimanRelationCodes_nonempty (s := s) ht b))).mpr
  refine ⟨?_, ?_⟩
  · rw [hcodes]
    exact Finset.min'_mem _ _
  · intro code hcode
    exact Finset.min'_le _ _ (by rwa [← hcodes])

private lemma freimanRelationSpace_eq_of_relations_iff {s t : ℕ}
    {a b : Fin t → ℕ}
    (hrelations : ∀ p : FreimanRelationIndex s t,
      freimanRelationHolds a p ↔ freimanRelationHolds b p) :
    freimanRelationSpace (s := s) a = freimanRelationSpace (s := s) b := by
  unfold freimanRelationSpace
  congr 1
  ext v
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (hrelations p).mp hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (hrelations p).mpr hp, rfl⟩

private lemma freimanRelationCode_eq_of_relations_iff {s t : ℕ} (ht : 0 < t)
    {a b : Fin t → ℕ}
    (hrelations : ∀ p : FreimanRelationIndex s t,
      freimanRelationHolds a p ↔ freimanRelationHolds b p) :
    freimanRelationCode (s := s) ht a = freimanRelationCode ht b := by
  refine freimanRelationCode_eq_of_space_eq ht ?_
  exact freimanRelationSpace_eq_of_relations_iff hrelations

lemma freimanRelations_iff_of_code_eq {s t : ℕ} (ht : 0 < t)
    {a b : Fin t → ℕ}
    (hcode : freimanRelationCode (s := s) ht a = freimanRelationCode ht b)
    (p : FreimanRelationIndex s t) :
    freimanRelationHolds a p ↔ freimanRelationHolds b p := by
  classical
  rw [freimanRelation_iff_mem_space, freimanRelation_iff_mem_space,
    ← freimanRelationCode_span ht a, ← freimanRelationCode_span ht b, hcode]

/-- The number `t^(2*s*t)` in Green's Lemma 12. -/
lemma card_freimanRelationCodes (s t : ℕ) :
    Fintype.card (Fin t → FreimanRelationIndex s t) = t ^ (2 * s * t) := by
  simp only [FreimanRelationIndex, Fintype.card_fun, Fintype.card_prod,
    Fintype.card_fin]
  rw [← pow_add, ← pow_mul]
  congr 1
  ring

/-! ### Restricted sumsets and popular representations -/

/-- The restricted sumset, in which the two summands must be distinct. -/
def restrictedSumset {G : Type*} [DecidableEq G] [Add G] (A : Finset G) : Finset G :=
  ((A ×ˢ A).filter fun p ↦ p.1 ≠ p.2).image fun p ↦ p.1 + p.2

lemma restrictedSumset_subset_add {G : Type*} [DecidableEq G] [Add G] (A : Finset G) :
    restrictedSumset A ⊆ A + A := by
  intro x hx
  rw [restrictedSumset, Finset.mem_image] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  rw [Finset.mem_filter, Finset.mem_product] at hp
  exact Finset.add_mem_add hp.1.1 hp.1.2

lemma card_restrictedSumset_le_card_add {G : Type*} [DecidableEq G] [Add G]
    (A : Finset G) :
    (restrictedSumset A).card ≤ (A + A).card :=
  Finset.card_le_card (restrictedSumset_subset_add A)

private lemma image_add_erase_subset_restrictedSumset {G : Type*} [DecidableEq G]
    [Add G] {A : Finset G} {a : G} (ha : a ∈ A) :
    (A.erase a).image (a + ·) ⊆ restrictedSumset A := by
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  rw [restrictedSumset, Finset.mem_image]
  refine ⟨(a, b), ?_, rfl⟩
  rw [Finset.mem_erase] at hb
  rw [Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨ha, hb.2⟩, hb.1.symm⟩

lemma card_sub_one_le_card_restrictedSumset {G : Type*} [DecidableEq G]
    [AddLeftCancelSemigroup G] {A : Finset G} (hA : A.Nonempty) :
    A.card - 1 ≤ (restrictedSumset A).card := by
  obtain ⟨a, ha⟩ := hA
  rw [← Finset.card_erase_of_mem ha,
    ← Finset.card_image_of_injective (A.erase a) (add_right_injective a)]
  exact Finset.card_le_card (image_add_erase_subset_restrictedSumset ha)

private lemma restrictedSumset_eq_image_offDiag {G : Type*} [DecidableEq G] [Add G]
    (A : Finset G) :
    restrictedSumset A = A.offDiag.image fun p ↦ p.1 + p.2 := by
  ext x
  simp only [restrictedSumset, Finset.mem_image, Finset.mem_filter,
    Finset.mem_product, Finset.mem_offDiag]
  tauto

/-- The ordered representations of `x` as a sum of two distinct elements of `A`. -/
private def restrictedRepresentationPairs {G : Type*} [DecidableEq G] [Add G]
    (A : Finset G) (x : G) : Finset (G × G) :=
  A.offDiag.filter fun p ↦ p.1 + p.2 = x

private lemma mem_restrictedRepresentationPairs {G : Type*} [DecidableEq G] [Add G]
    {A : Finset G} {x : G} {p : G × G} :
    p ∈ restrictedRepresentationPairs A x ↔
      p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≠ p.2 ∧ p.1 + p.2 = x := by
  simp only [restrictedRepresentationPairs, Finset.mem_filter, Finset.mem_offDiag]
  tauto

private lemma mem_restrictedSumset_iff_representationPairs_nonempty
    {G : Type*} [DecidableEq G] [Add G] {A : Finset G} {x : G} :
    x ∈ restrictedSumset A ↔ (restrictedRepresentationPairs A x).Nonempty := by
  rw [restrictedSumset_eq_image_offDiag]
  constructor
  · rw [Finset.mem_image]
    rintro ⟨p, hp, rfl⟩
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩
  · rintro ⟨p, hp⟩
    rw [restrictedRepresentationPairs, Finset.mem_filter] at hp
    exact Finset.mem_image.mpr ⟨p, hp.1, hp.2⟩

private def increasingRestrictedRepresentationPairs (A : Finset ℕ) (x : ℕ) :
    Finset (ℕ × ℕ) :=
  (restrictedRepresentationPairs A x).filter fun p ↦ p.1 < p.2

private def decreasingRestrictedRepresentationPairs (A : Finset ℕ) (x : ℕ) :
    Finset (ℕ × ℕ) :=
  (restrictedRepresentationPairs A x).filter fun p ↦ p.2 < p.1

private lemma mem_increasingRestrictedRepresentationPairs
    {A : Finset ℕ} {x : ℕ} {p : ℕ × ℕ} :
    p ∈ increasingRestrictedRepresentationPairs A x ↔
      p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 < p.2 ∧ p.1 + p.2 = x := by
  rw [increasingRestrictedRepresentationPairs, Finset.mem_filter,
    mem_restrictedRepresentationPairs]
  constructor
  · rintro ⟨⟨hp, hq, -, hsum⟩, hpq⟩
    exact ⟨hp, hq, hpq, hsum⟩
  · rintro ⟨hp, hq, hpq, hsum⟩
    exact ⟨⟨hp, hq, hpq.ne, hsum⟩, hpq⟩

private lemma increasing_representations_pairwise_disjoint {A : Finset ℕ} {x : ℕ} :
    ((increasingRestrictedRepresentationPairs A x : Finset (ℕ × ℕ)) :
      Set (ℕ × ℕ)).Pairwise fun p q ↦
        Disjoint ({p.1, p.2} : Finset ℕ) ({q.1, q.2} : Finset ℕ) := by
  intro p hp q hq hpq
  change p ∈ increasingRestrictedRepresentationPairs A x at hp
  change q ∈ increasingRestrictedRepresentationPairs A x at hq
  rw [mem_increasingRestrictedRepresentationPairs] at hp hq
  rw [Finset.disjoint_left]
  intro y hyp hyq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hyp hyq
  rcases hyp with hyp | hyp <;> rcases hyq with hyq | hyq
  · apply hpq
    apply Prod.ext
    · exact hyp.symm.trans hyq
    · omega
  · omega
  · omega
  · apply hpq
    apply Prod.ext
    · omega
    · exact hyp.symm.trans hyq

private lemma card_decreasingRestrictedRepresentationPairs_eq_increasing
    (A : Finset ℕ) (x : ℕ) :
    (decreasingRestrictedRepresentationPairs A x).card =
      (increasingRestrictedRepresentationPairs A x).card := by
  apply Finset.card_equiv (Equiv.prodComm ℕ ℕ)
  intro p
  simp only [decreasingRestrictedRepresentationPairs,
    increasingRestrictedRepresentationPairs, Finset.mem_filter,
    mem_restrictedRepresentationPairs, Equiv.prodComm_apply]
  constructor
  · rintro ⟨⟨hp, hq, hpq, hsum⟩, hlt⟩
    exact ⟨⟨hq, hp, hpq.symm, by rwa [add_comm]⟩, hlt⟩
  · rintro ⟨⟨hq, hp, hqp, hsum⟩, hlt⟩
    exact ⟨⟨hp, hq, hqp.symm, by rwa [add_comm]⟩, hlt⟩

private lemma card_restrictedRepresentationPairs_eq_two_mul_increasing
    (A : Finset ℕ) (x : ℕ) :
    (restrictedRepresentationPairs A x).card =
      2 * (increasingRestrictedRepresentationPairs A x).card := by
  have hunion : increasingRestrictedRepresentationPairs A x ∪
      decreasingRestrictedRepresentationPairs A x = restrictedRepresentationPairs A x := by
    ext p
    simp only [increasingRestrictedRepresentationPairs,
      decreasingRestrictedRepresentationPairs, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      rcases hp with hp | hp
      · exact hp.1
      · exact hp.1
    · intro hp
      have hpne : p.1 ≠ p.2 := (mem_restrictedRepresentationPairs.mp hp).2.2.1
      exact (lt_or_gt_of_ne hpne).elim (fun h ↦ Or.inl ⟨hp, h⟩)
        (fun h ↦ Or.inr ⟨hp, h⟩)
  have hdisjoint : Disjoint (increasingRestrictedRepresentationPairs A x)
      (decreasingRestrictedRepresentationPairs A x) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [increasingRestrictedRepresentationPairs,
      decreasingRestrictedRepresentationPairs, Finset.mem_filter] at hp hq
    omega
  rw [← hunion, Finset.card_union_of_disjoint hdisjoint,
    card_decreasingRestrictedRepresentationPairs_eq_increasing]
  omega

private lemma half_le_card_increasing_of_popular {A : Finset ℕ} {x Q : ℕ}
    (hpopular : Q ≤ (restrictedRepresentationPairs A x).card) :
    Q / 2 ≤ (increasingRestrictedRepresentationPairs A x).card := by
  rw [card_restrictedRepresentationPairs_eq_two_mul_increasing] at hpopular
  omega

private def unpopularOrderedPairs (A : Finset ℕ) (Q : ℕ) : Finset (ℕ × ℕ) :=
  A.offDiag.filter fun p ↦ (restrictedRepresentationPairs A (p.1 + p.2)).card < Q

private def unpopularNeighbors (A : Finset ℕ) (Q : ℕ) (a : ℕ) : Finset ℕ :=
  (A.erase a).filter fun b ↦ (restrictedRepresentationPairs A (a + b)).card < Q

private lemma card_unpopularOrderedPairs_le (A : Finset ℕ) (Q : ℕ) :
    (unpopularOrderedPairs A Q).card ≤ Q * (restrictedSumset A).card := by
  rw [Finset.card_eq_sum_card_fiberwise (t := restrictedSumset A)
    (f := fun p : ℕ × ℕ ↦ p.1 + p.2) (s := unpopularOrderedPairs A Q) (by
      intro p hp
      change p ∈ unpopularOrderedPairs A Q at hp
      rw [unpopularOrderedPairs, Finset.mem_filter, Finset.mem_offDiag] at hp
      change p.1 + p.2 ∈ restrictedSumset A
      rw [mem_restrictedSumset_iff_representationPairs_nonempty]
      exact ⟨p, mem_restrictedRepresentationPairs.mpr
        ⟨hp.1.1, hp.1.2.1, hp.1.2.2, rfl⟩⟩)]
  rw [mul_comm, ← Finset.sum_const_nat fun _ _ ↦ rfl]
  apply Finset.sum_le_sum
  intro x hx
  let fiber := (unpopularOrderedPairs A Q).filter fun p ↦ p.1 + p.2 = x
  change fiber.card ≤ Q
  by_cases hfiber : fiber.Nonempty
  · obtain ⟨p, hp⟩ := hfiber
    have hpopular : (restrictedRepresentationPairs A x).card < Q := by
      dsimp only [fiber] at hp
      rw [Finset.mem_filter, unpopularOrderedPairs, Finset.mem_filter] at hp
      simpa only [hp.2] using hp.1.2
    refine (Finset.card_le_card ?_).trans (Nat.le_of_lt hpopular)
    intro p hp
    dsimp only [fiber] at hp
    rw [Finset.mem_filter, unpopularOrderedPairs, Finset.mem_filter,
      Finset.mem_offDiag] at hp
    rw [mem_restrictedRepresentationPairs]
    exact ⟨hp.1.1.1, hp.1.1.2.1, hp.1.1.2.2, hp.2⟩
  · rw [Finset.not_nonempty_iff_eq_empty.mp hfiber, Finset.card_empty]
    exact Nat.zero_le Q

private lemma sum_card_unpopularNeighbors_eq (A : Finset ℕ) (Q : ℕ) :
    ∑ a ∈ A, (unpopularNeighbors A Q a).card = (unpopularOrderedPairs A Q).card := by
  rw [Finset.card_eq_sum_card_fiberwise (t := A) (f := Prod.fst)
    (s := unpopularOrderedPairs A Q) (by
      intro p hp
      change p ∈ unpopularOrderedPairs A Q at hp
      rw [unpopularOrderedPairs, Finset.mem_filter, Finset.mem_offDiag] at hp
      exact hp.1.1)]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.card_bij (s := unpopularNeighbors A Q a)
    (t := (unpopularOrderedPairs A Q).filter fun p ↦ p.1 = a)
    (fun b _ ↦ (a, b))
  · intro b hb
    rw [unpopularNeighbors, Finset.mem_filter, Finset.mem_erase] at hb
    rw [Finset.mem_filter, unpopularOrderedPairs, Finset.mem_filter,
      Finset.mem_offDiag]
    exact ⟨⟨⟨ha, hb.1.2, hb.1.1.symm⟩, hb.2⟩, rfl⟩
  · intro b₁ hb₁ b₂ hb₂ h
    exact congrArg Prod.snd h
  · intro p hp
    rw [Finset.mem_filter, unpopularOrderedPairs, Finset.mem_filter,
      Finset.mem_offDiag] at hp
    refine ⟨p.2, ?_, ?_⟩
    · rw [unpopularNeighbors, Finset.mem_filter, Finset.mem_erase]
      refine ⟨⟨?_, hp.1.1.2.1⟩, ?_⟩
      · intro h
        exact hp.1.1.2.2 (hp.2.trans h.symm)
      · simpa only [← hp.2] using hp.1.2
    · apply Prod.ext
      · exact hp.2.symm
      · rfl

private lemma exists_low_unpopular_degree {A : Finset ℕ} {t m Q : ℕ}
    (hA : A.card = t) (hA0 : A.Nonempty)
    (hm : (restrictedSumset A).card ≤ m) :
    ∃ a ∈ A, t * (unpopularNeighbors A Q a).card ≤ Q * m := by
  apply Finset.exists_le_of_sum_le hA0
  rw [← Finset.mul_sum, sum_card_unpopularNeighbors_eq,
    Finset.sum_const_nat fun _ _ ↦ rfl, hA]
  exact Nat.mul_le_mul_left t
    ((card_unpopularOrderedPairs_le A Q).trans (Nat.mul_le_mul_left Q hm))

/-! ### A finite Bernoulli alteration for core decompositions -/

private def assignmentWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℝ) (ω : ι → Bool) : ℝ :=
  ∏ i, if ω i then q else 1 - q

private def selectedIndices {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ω : ι → Bool) : Finset ι :=
  Finset.univ.filter fun i ↦ ω i

private lemma sum_assignmentWeight {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℝ) :
    ∑ ω : ι → Bool, assignmentWeight q ω = 1 := by
  unfold assignmentWeight
  rw [← Fintype.prod_sum
    (f := fun (_ : ι) (b : Bool) ↦ if b then q else 1 - q)]
  simp

private lemma sum_assignmentWeight_selectedIndicator {ι : Type*} [Fintype ι]
    [DecidableEq ι] (q : ℝ) (i : ι) :
    ∑ ω : ι → Bool, assignmentWeight q ω * (if ω i then 1 else 0) = q := by
  unfold assignmentWeight
  conv_lhs =>
    enter [2, ω]
    rw [← Fintype.prod_ite_eq' i (fun j ↦ if ω j then 1 else 0),
      ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (f := fun j (b : Bool) ↦
    (if b then q else 1 - q) * if j = i then (if b then 1 else 0) else 1)]
  simp

private lemma sum_assignmentWeight_selectedCard {ι : Type*} [Fintype ι]
    [DecidableEq ι] (q : ℝ) :
    ∑ ω : ι → Bool, assignmentWeight q ω * (selectedIndices ω).card =
      q * Fintype.card ι := by
  have hcard (ω : ι → Bool) :
      ((selectedIndices ω).card : ℝ) = ∑ i : ι, if ω i then 1 else 0 := by
    simp [selectedIndices]
  simp_rw [hcard, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [sum_assignmentWeight_selectedIndicator]
  simp [nsmul_eq_mul, mul_comm]

private noncomputable def injectionSumComplEquiv {κ ι : Type*} [Fintype κ] [Fintype ι]
    (f : κ → ι) (hf : Function.Injective f) :
    κ ⊕ ((Set.range f)ᶜ : Set ι) ≃ ι := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective f hf) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range f))

private lemma injectionSumComplEquiv_apply_inl {κ ι : Type*} [Fintype κ] [Fintype ι]
    (f : κ → ι) (hf : Function.Injective f) (x : κ) :
    injectionSumComplEquiv f hf (Sum.inl x) = f x := by
  classical
  rfl

private lemma sum_assignmentWeight_marginal {κ ι : Type*} [Fintype κ] [Fintype ι]
    [DecidableEq κ] [DecidableEq ι] (q : ℝ) (f : κ → ι)
    (hf : Function.Injective f) (F : (κ → Bool) → ℝ) :
    ∑ ω : ι → Bool, assignmentWeight q ω * F (ω ∘ f) =
      ∑ v : κ → Bool, assignmentWeight q v * F v := by
  classical
  let C := (Set.range f)ᶜ
  let e : κ ⊕ C ≃ ι := injectionSumComplEquiv f hf
  let eΩ : ((κ → Bool) × (C → Bool)) ≃ (ι → Bool) :=
    (Equiv.sumPiEquivProdPi (fun _ : κ ⊕ C ↦ Bool)).symm.trans
      (e.arrowCongr (Equiv.refl Bool))
  calc
    ∑ ω : ι → Bool, assignmentWeight q ω * F (ω ∘ f) =
        ∑ z : (κ → Bool) × (C → Bool),
          (assignmentWeight q z.1 * F z.1) * assignmentWeight q z.2 := by
      refine (eΩ.sum_comp
        (fun ω ↦ assignmentWeight q ω * F (ω ∘ f))).symm.trans ?_
      apply Fintype.sum_congr
      intro z
      let η : κ ⊕ C → Bool :=
        (Equiv.sumPiEquivProdPi (fun _ : κ ⊕ C ↦ Bool)).symm z
      let Ω : ι → Bool := (e.arrowCongr (Equiv.refl Bool)) η
      change assignmentWeight q Ω * F (Ω ∘ f) =
        (assignmentWeight q z.1 * F z.1) * assignmentWeight q z.2
      have hΩ_inl (x : κ) : Ω (e (Sum.inl x)) = z.1 x := by
        simp [Ω, η, Equiv.arrowCongr, Equiv.sumPiEquivProdPi]
      have hΩ_inr (x : C) : Ω (e (Sum.inr x)) = z.2 x := by
        simp [Ω, η, Equiv.arrowCongr, Equiv.sumPiEquivProdPi]
      have hΩ_f : Ω ∘ f = z.1 := by
        funext x
        change Ω (f x) = z.1 x
        rw [← injectionSumComplEquiv_apply_inl f hf x]
        exact hΩ_inl x
      rw [hΩ_f, assignmentWeight, assignmentWeight, assignmentWeight,
        ← e.prod_comp]
      simp only [Fintype.prod_sum_type, hΩ_inl, hΩ_inr]
      ring
    _ = ∑ v : κ → Bool, assignmentWeight q v * F v := by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, sum_assignmentWeight]
      simp

private def increasingRepresentationEndpoint (A : Finset ℕ) (x : ℕ)
    (u : (increasingRestrictedRepresentationPairs A x) × Fin 2) : A :=
  if u.2 = 0 then
    ⟨u.1.1.1, (mem_increasingRestrictedRepresentationPairs.mp u.1.2).1⟩
  else
    ⟨u.1.1.2, (mem_increasingRestrictedRepresentationPairs.mp u.1.2).2.1⟩

private lemma increasingRepresentationEndpoint_zero (A : Finset ℕ) (x : ℕ)
    (p : increasingRestrictedRepresentationPairs A x) :
    (increasingRepresentationEndpoint A x (p, 0) : ℕ) = p.1.1 := by
  simp [increasingRepresentationEndpoint]

private lemma increasingRepresentationEndpoint_one (A : Finset ℕ) (x : ℕ)
    (p : increasingRestrictedRepresentationPairs A x) :
    (increasingRepresentationEndpoint A x (p, 1) : ℕ) = p.1.2 := by
  simp [increasingRepresentationEndpoint]

private lemma increasingRepresentationEndpoint_mem_pair (A : Finset ℕ) (x : ℕ)
    (p : increasingRestrictedRepresentationPairs A x) (i : Fin 2) :
    (increasingRepresentationEndpoint A x (p, i) : ℕ) ∈
      ({p.1.1, p.1.2} : Finset ℕ) := by
  by_cases hi : i = 0
  · simp [increasingRepresentationEndpoint, hi]
  · simp [increasingRepresentationEndpoint, hi]

private lemma increasingRepresentationEndpoint_index_injective (A : Finset ℕ) (x : ℕ)
    (p : increasingRestrictedRepresentationPairs A x) :
    Function.Injective fun i : Fin 2 ↦ increasingRepresentationEndpoint A x (p, i) := by
  intro i j h
  apply Fin.ext
  have hlt := (mem_increasingRestrictedRepresentationPairs.mp p.2).2.2.1
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso
    apply hlt.ne
    exact congrArg Subtype.val h
  · exfalso
    apply hlt.ne'
    exact congrArg Subtype.val h
  · rfl

private lemma increasingRepresentationEndpoint_injective (A : Finset ℕ) (x : ℕ) :
    Function.Injective (increasingRepresentationEndpoint A x) := by
  rintro ⟨p, i⟩ ⟨q, j⟩ h
  have hend : (increasingRepresentationEndpoint A x (p, i) : ℕ) =
      increasingRepresentationEndpoint A x (q, j) :=
    congrArg Subtype.val h
  have hpq : p = q := by
    by_contra hpq
    have hdisjoint := increasing_representations_pairwise_disjoint
      p.2 q.2 (Subtype.coe_ne_coe.mpr hpq)
    change Disjoint ({p.1.1, p.1.2} : Finset ℕ)
      ({q.1.1, q.1.2} : Finset ℕ) at hdisjoint
    rw [Finset.disjoint_left] at hdisjoint
    exact hdisjoint
      (increasingRepresentationEndpoint_mem_pair A x p i)
      (hend ▸ increasingRepresentationEndpoint_mem_pair A x q j)
  subst q
  apply Prod.ext
  · rfl
  · exact increasingRepresentationEndpoint_index_injective A x p h

private abbrev pairAssignmentAvoids (v : Fin 2 → Bool) : Prop :=
  ¬(v 0 ∧ v 1)

private lemma sum_assignmentWeight_pairAssignmentAvoids (q : ℝ) :
    ∑ v : Fin 2 → Bool, assignmentWeight q v *
      (if pairAssignmentAvoids v then 1 else 0) = 1 - q ^ 2 := by
  classical
  let f := fun v : Fin 2 → Bool ↦
    assignmentWeight q v * (if pairAssignmentAvoids v then 1 else 0)
  calc
    ∑ v : Fin 2 → Bool, f v =
        ∑ z : Bool × Bool, f ((finTwoArrowEquiv Bool).symm z) :=
      ((finTwoArrowEquiv Bool).symm.sum_comp f).symm
    _ = 1 - q ^ 2 := by
      rw [Fintype.sum_prod_type]
      simp [f, assignmentWeight, pairAssignmentAvoids, finTwoArrowEquiv,
        piFinTwoEquiv]
      ring

private def allPairAssignmentsAvoidIndicator {ρ : Type*} [Fintype ρ]
    [DecidableEq ρ] (v : ρ × Fin 2 → Bool) : ℝ :=
  ∏ p : ρ, if pairAssignmentAvoids (fun i ↦ v (p, i)) then 1 else 0

private lemma sum_assignmentWeight_allPairAssignmentsAvoid {ρ : Type*}
    [Fintype ρ] [DecidableEq ρ] (q : ℝ) :
    ∑ v : ρ × Fin 2 → Bool, assignmentWeight q v *
      allPairAssignmentsAvoidIndicator v =
        (1 - q ^ 2) ^ Fintype.card ρ := by
  classical
  let e := Equiv.curry ρ (Fin 2) Bool
  let f := fun v : ρ × Fin 2 → Bool ↦ assignmentWeight q v *
    allPairAssignmentsAvoidIndicator v
  calc
    ∑ v : ρ × Fin 2 → Bool, f v =
        ∑ g : ρ → Fin 2 → Bool, f (e.symm g) :=
      (e.symm.sum_comp f).symm
    _ = ∑ g : ρ → Fin 2 → Bool, ∏ p : ρ,
        assignmentWeight q (g p) * (if pairAssignmentAvoids (g p) then 1 else 0) := by
      apply Fintype.sum_congr
      intro g
      unfold f
      rw [assignmentWeight, Fintype.prod_prod_type]
      unfold allPairAssignmentsAvoidIndicator
      simp only [e, Equiv.curry_symm_apply]
      rw [← Finset.prod_mul_distrib]
      rfl
    _ = (1 - q ^ 2) ^ Fintype.card ρ := by
      rw [← Fintype.prod_sum (f := fun (_ : ρ) (v : Fin 2 → Bool) ↦
        assignmentWeight q v * (if pairAssignmentAvoids v then 1 else 0))]
      simp_rw [sum_assignmentWeight_pairAssignmentAvoids]
      simp

private def representationAvoidanceIndicator (A : Finset ℕ) (x : ℕ)
    (ω : A → Bool) : ℝ :=
  allPairAssignmentsAvoidIndicator fun u ↦
    ω (increasingRepresentationEndpoint A x u)

private lemma sum_assignmentWeight_representationAvoidanceIndicator
    (A : Finset ℕ) (x : ℕ) (q : ℝ) :
    ∑ ω : A → Bool, assignmentWeight q ω *
      representationAvoidanceIndicator A x ω =
        (1 - q ^ 2) ^ (increasingRestrictedRepresentationPairs A x).card := by
  unfold representationAvoidanceIndicator
  change (∑ ω : A → Bool, assignmentWeight q ω *
    allPairAssignmentsAvoidIndicator
      (ω ∘ increasingRepresentationEndpoint A x)) = _
  rw [sum_assignmentWeight_marginal q
    (increasingRepresentationEndpoint A x)
    (increasingRepresentationEndpoint_injective A x)
    allPairAssignmentsAvoidIndicator]
  simpa using sum_assignmentWeight_allPairAssignmentsAvoid
    (ρ := increasingRestrictedRepresentationPairs A x) q

private def selectedElements (A : Finset ℕ) (ω : A → Bool) : Finset ℕ :=
  (selectedIndices ω).image Subtype.val

private lemma card_selectedElements (A : Finset ℕ) (ω : A → Bool) :
    (selectedElements A ω).card = (selectedIndices ω).card := by
  rw [selectedElements, Finset.card_image_of_injective]
  exact Subtype.val_injective

private lemma selectedElements_subset (A : Finset ℕ) (ω : A → Bool) :
    selectedElements A ω ⊆ A := by
  intro a ha
  rw [selectedElements, Finset.mem_image] at ha
  obtain ⟨a, -, rfl⟩ := ha
  exact a.2

private lemma mem_restrictedSumset_iff_increasing_nonempty {A : Finset ℕ} {x : ℕ} :
    x ∈ restrictedSumset A ↔ (increasingRestrictedRepresentationPairs A x).Nonempty := by
  rw [mem_restrictedSumset_iff_representationPairs_nonempty]
  constructor
  · rintro ⟨p, hp⟩
    rw [mem_restrictedRepresentationPairs] at hp
    rcases lt_or_gt_of_ne hp.2.2.1 with hpq | hqp
    · exact ⟨p, mem_increasingRestrictedRepresentationPairs.mpr
        ⟨hp.1, hp.2.1, hpq, hp.2.2.2⟩⟩
    · exact ⟨(p.2, p.1), mem_increasingRestrictedRepresentationPairs.mpr
        ⟨hp.2.1, hp.1, hqp, by simpa [add_comm] using hp.2.2.2⟩⟩
  · rintro ⟨p, hp⟩
    rw [mem_increasingRestrictedRepresentationPairs] at hp
    exact ⟨p, mem_restrictedRepresentationPairs.mpr
      ⟨hp.1, hp.2.1, hp.2.2.1.ne, hp.2.2.2⟩⟩

private lemma endpoint_mem_selectedElements_iff (A : Finset ℕ) (x : ℕ)
    (ω : A → Bool) (u : (increasingRestrictedRepresentationPairs A x) × Fin 2) :
    (increasingRepresentationEndpoint A x u : ℕ) ∈ selectedElements A ω ↔
      ω (increasingRepresentationEndpoint A x u) := by
  simp [selectedElements, selectedIndices]

private lemma representationAvoidanceIndicator_eq_one_iff
    (A : Finset ℕ) (x : ℕ) (ω : A → Bool) :
    representationAvoidanceIndicator A x ω = 1 ↔
      x ∉ restrictedSumset (selectedElements A ω) := by
  rw [mem_restrictedSumset_iff_increasing_nonempty]
  unfold representationAvoidanceIndicator allPairAssignmentsAvoidIndicator
  rw [Fintype.prod_boole]
  simp only [ite_eq_left_iff, zero_ne_one, imp_false, not_forall,
    not_not, Finset.not_nonempty_iff_eq_empty, Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h p hp
    rw [mem_increasingRestrictedRepresentationPairs] at hp
    obtain ⟨hpA, hqA⟩ := selectedElements_subset A ω hp.1,
      selectedElements_subset A ω hp.2.1
    let pA : increasingRestrictedRepresentationPairs A x :=
      ⟨p, mem_increasingRestrictedRepresentationPairs.mpr
        ⟨hpA, hqA, hp.2.2.1, hp.2.2.2⟩⟩
    have hpSelected : ω (increasingRepresentationEndpoint A x (pA, 0)) := by
      rw [← endpoint_mem_selectedElements_iff]
      simpa only [increasingRepresentationEndpoint_zero] using hp.1
    have hqSelected : ω (increasingRepresentationEndpoint A x (pA, 1)) := by
      rw [← endpoint_mem_selectedElements_iff]
      simpa only [increasingRepresentationEndpoint_one] using hp.2.1
    apply h
    exact ⟨pA, hpSelected, hqSelected⟩
  · intro h
    rintro ⟨p, hpSelected, hqSelected⟩
    apply h p.1
    rw [mem_increasingRestrictedRepresentationPairs]
    refine ⟨?_, ?_, (mem_increasingRestrictedRepresentationPairs.mp p.2).2.2.1,
      (mem_increasingRestrictedRepresentationPairs.mp p.2).2.2.2⟩
    · rw [← increasingRepresentationEndpoint_zero A x p,
        endpoint_mem_selectedElements_iff]
      exact hpSelected
    · rw [← increasingRepresentationEndpoint_one A x p,
        endpoint_mem_selectedElements_iff]
      exact hqSelected

private lemma representationAvoidanceIndicator_eq_boole
    (A : Finset ℕ) (x : ℕ) (ω : A → Bool) :
    representationAvoidanceIndicator A x ω =
      if x ∉ restrictedSumset (selectedElements A ω) then 1 else 0 := by
  by_cases hx : x ∉ restrictedSumset (selectedElements A ω)
  · rw [if_pos hx]
    exact (representationAvoidanceIndicator_eq_one_iff A x ω).mpr hx
  · rw [if_neg hx]
    have hzero_or_one : representationAvoidanceIndicator A x ω = 0 ∨
        representationAvoidanceIndicator A x ω = 1 := by
      unfold representationAvoidanceIndicator allPairAssignmentsAvoidIndicator
      rw [Fintype.prod_boole]
      split_ifs <;> simp
    exact hzero_or_one.resolve_right fun h ↦
      hx ((representationAvoidanceIndicator_eq_one_iff A x ω).mp h)

private def missedTranslateElements (A : Finset ℕ) (a : ℕ)
    (ω : A → Bool) : Finset ℕ :=
  A.filter fun b ↦ a + b ∉ restrictedSumset (selectedElements A ω)

private lemma sum_assignmentWeight_missedTranslateCard (A : Finset ℕ)
    (a : ℕ) (q : ℝ) :
    ∑ ω : A → Bool, assignmentWeight q ω * (missedTranslateElements A a ω).card =
      ∑ b ∈ A, (1 - q ^ 2) ^
        (increasingRestrictedRepresentationPairs A (a + b)).card := by
  have hcard (ω : A → Bool) :
      ((missedTranslateElements A a ω).card : ℝ) =
        ∑ b ∈ A, if a + b ∉ restrictedSumset (selectedElements A ω) then 1 else 0 := by
    exact_mod_cast (by
      rw [missedTranslateElements, Finset.card_eq_sum_ones, Finset.sum_filter])
  simp_rw [hcard, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  simp_rw [← representationAvoidanceIndicator_eq_boole A (a + b)]
  exact sum_assignmentWeight_representationAvoidanceIndicator A (a + b) q

private lemma sum_representationAvoidance_le (A : Finset ℕ) {a : ℕ}
    (ha : a ∈ A) (Q : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∑ b ∈ A, (1 - q ^ 2) ^
      (increasingRestrictedRepresentationPairs A (a + b)).card ≤
        1 + (unpopularNeighbors A Q a).card +
          A.card * (1 - q ^ 2) ^ (Q / 2) := by
  have hbase0 : 0 ≤ 1 - q ^ 2 := by nlinarith [sq_nonneg q]
  have hbase1 : 1 - q ^ 2 ≤ 1 := by nlinarith [sq_nonneg q]
  calc
    ∑ b ∈ A, (1 - q ^ 2) ^
        (increasingRestrictedRepresentationPairs A (a + b)).card ≤
        ∑ b ∈ A, ((if b = a then (1 : ℝ) else 0) +
          (if b ∈ unpopularNeighbors A Q a then 1 else 0) +
            (1 - q ^ 2) ^ (Q / 2)) := by
      apply Finset.sum_le_sum
      intro b hb
      let term := (1 - q ^ 2) ^
        (increasingRestrictedRepresentationPairs A (a + b)).card
      change term ≤ _
      have hterm0 : 0 ≤ term := pow_nonneg hbase0 _
      have hterm1 : term ≤ 1 := pow_le_one₀ hbase0 hbase1
      by_cases hba : b = a
      · simp only [hba, if_pos]
        split_ifs <;> nlinarith [pow_nonneg hbase0 (Q / 2)]
      · by_cases hbad : b ∈ unpopularNeighbors A Q a
        · simp only [hba, hbad, if_false, if_pos, zero_add]
          nlinarith [pow_nonneg hbase0 (Q / 2)]
        · simp only [hba, hbad, if_false, zero_add]
          have hpopular : Q ≤ (restrictedRepresentationPairs A (a + b)).card := by
            by_contra hQ
            apply hbad
            rw [unpopularNeighbors, Finset.mem_filter, Finset.mem_erase]
            exact ⟨⟨hba, hb⟩, Nat.lt_of_not_ge hQ⟩
          exact pow_le_pow_of_le_one hbase0 hbase1
            (half_le_card_increasing_of_popular hpopular)
    _ = 1 + (unpopularNeighbors A Q a).card +
        A.card * (1 - q ^ 2) ^ (Q / 2) := by
      simp_rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', ha, if_true]
      have hunpopular : unpopularNeighbors A Q a ⊆ A := by
        intro b hb
        rw [unpopularNeighbors, Finset.mem_filter, Finset.mem_erase] at hb
        exact hb.1.2
      have hcard : (∑ b ∈ A, if b ∈ unpopularNeighbors A Q a then (1 : ℝ) else 0) =
          (unpopularNeighbors A Q a).card := by
        rw [← Finset.sum_filter]
        have hfilter : A.filter (· ∈ unpopularNeighbors A Q a) =
            unpopularNeighbors A Q a := by
          ext b
          simp only [Finset.mem_filter]
          constructor
          · exact And.right
          · intro hb
            exact ⟨hunpopular hb, hb⟩
        rw [hfilter]
        simp
      rw [hcard]
      simp only [Finset.sum_const, nsmul_eq_mul]

private lemma assignmentWeight_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (ω : ι → Bool) :
    0 < assignmentWeight q ω := by
  unfold assignmentWeight
  apply Finset.prod_pos
  intro i _
  split <;> linarith

private lemma exists_le_of_weighted_sum_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] {q B : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (F : (ι → Bool) → ℝ)
    (hsum : ∑ ω : ι → Bool, assignmentWeight q ω * F ω ≤ B) :
    ∃ ω, F ω ≤ B := by
  have hweighted :
      ∑ ω : ι → Bool, assignmentWeight q ω * F ω ≤
        ∑ ω : ι → Bool, assignmentWeight q ω * B := by
    rw [← Finset.sum_mul, sum_assignmentWeight, one_mul]
    exact hsum
  obtain ⟨ω, -, hω⟩ := Finset.exists_le_of_sum_le
    (s := Finset.univ) Finset.univ_nonempty hweighted
  refine ⟨ω, le_of_mul_le_mul_left ?_ (assignmentWeight_pos hq0 hq1 ω)⟩
  simpa only [Finset.mem_univ] using hω

private lemma exists_sample_with_bounded_cost (A : Finset ℕ) {a : ℕ} (ha : a ∈ A)
    (Q : ℕ) {q R : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hR : 0 ≤ R) :
    ∃ ω : A → Bool,
      ((selectedElements A ω).card : ℝ) +
          R * (missedTranslateElements A a ω).card ≤
        q * A.card + R * (1 + (unpopularNeighbors A Q a).card +
          A.card * (1 - q ^ 2) ^ (Q / 2)) := by
  apply exists_le_of_weighted_sum_le hq0 hq1
  simp_rw [mul_add, Finset.sum_add_distrib]
  ring_nf
  simp_rw [mul_comm _ R, mul_assoc]
  rw [← Finset.mul_sum]
  simp_rw [card_selectedElements]
  rw [sum_assignmentWeight_selectedCard]
  rw [Fintype.card_coe]
  rw [sum_assignmentWeight_missedTranslateCard]
  have hbound := add_le_add_right (mul_le_mul_of_nonneg_left
    (sum_representationAvoidance_le A ha Q hq0.le hq1.le) hR)
      (q * A.card)
  ring_nf at hbound ⊢
  exact hbound

private lemma missedTranslateElements_compl_image_subset (A : Finset ℕ) (a : ℕ)
    (ω : A → Bool) :
    (A \ missedTranslateElements A a ω).image (a + ·) ⊆
      restrictedSumset (selectedElements A ω) := by
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  rw [Finset.mem_sdiff] at hb
  unfold missedTranslateElements at hb
  simpa only [Finset.mem_filter, hb.1, true_and, not_not] using hb.2

/-- The combinatorial core of Green's Proposition 2, before fixing its numerical parameters. -/
theorem exists_core_decomposition (A : Finset ℕ) {t m : ℕ} (hA : A.card = t)
    (hA0 : A.Nonempty) (hm : (restrictedSumset A).card ≤ m) (Q : ℕ)
    {q R : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hR : 0 ≤ R) :
    ∃ a A₀ Z, a ∈ A ∧ A₀ ⊆ A ∧ Z ⊆ A ∧
      (A \ Z).image (a + ·) ⊆ restrictedSumset A₀ ∧
      (A₀.card : ℝ) + R * Z.card ≤
        q * t + R * (1 + (Q : ℝ) * m / t +
          t * (1 - q ^ 2) ^ (Q / 2)) := by
  obtain ⟨a, ha, hdegree⟩ := exists_low_unpopular_degree hA hA0 hm (Q := Q)
  obtain ⟨ω, hω⟩ := exists_sample_with_bounded_cost A ha Q hq0 hq1 hR
  refine ⟨a, selectedElements A ω, missedTranslateElements A a ω,
    ha, selectedElements_subset A ω, ?_,
    missedTranslateElements_compl_image_subset A a ω, hω.trans ?_⟩
  · intro b hb
    exact (Finset.mem_filter.mp hb).1
  · rw [hA]
    have ht0 : (0 : ℝ) < t := by
      exact_mod_cast hA0.card_pos.trans_eq hA
    have hdegreeReal : (t : ℝ) * (unpopularNeighbors A Q a).card ≤
        (Q : ℝ) * m := by
      exact_mod_cast hdegree
    have hunpopular : ((unpopularNeighbors A Q a).card : ℝ) ≤
        (Q : ℝ) * m / t := by
      exact (le_div_iff₀ ht0).mpr (by simpa [mul_comm] using hdegreeReal)
    gcongr

/-! ### Extension relation codes -/

private abbrev ExtensionSlot (d : ℕ) := Unit ⊕ Fin d

private abbrev ExtensionShape (d : ℕ) :=
  (Fin 2 → ExtensionSlot d) × (Fin 2 → ExtensionSlot d)

private def extensionSlot {l d : ℕ} (i : Fin (l + d)) : ExtensionSlot d :=
  match finSumFinEquiv.symm i with
  | Sum.inl _ => Sum.inl ()
  | Sum.inr j => Sum.inr j

private def extensionShape {l d : ℕ} (p : FreimanRelationIndex 2 (l + d)) :
    ExtensionShape d :=
  (extensionSlot ∘ p.1, extensionSlot ∘ p.2)

private def extensionBaseIndex {l d : ℕ} (i₀ : Fin l) (i : Fin (l + d)) : Fin l :=
  match finSumFinEquiv.symm i with
  | Sum.inl j => j
  | Sum.inr _ => i₀

private def extensionBaseWitness {l d : ℕ} (i₀ : Fin l)
    (p : FreimanRelationIndex 2 (l + d)) : FreimanRelationIndex 2 l :=
  (extensionBaseIndex i₀ ∘ p.1, extensionBaseIndex i₀ ∘ p.2)

private def extensionRelation {l d : ℕ} (shape : ExtensionShape d)
    (witness : FreimanRelationIndex 2 l) : FreimanRelationIndex 2 (l + d) :=
  (fun j ↦ match shape.1 j with
    | Sum.inl _ => finSumFinEquiv (Sum.inl (witness.1 j))
    | Sum.inr i => finSumFinEquiv (Sum.inr i),
   fun j ↦ match shape.2 j with
    | Sum.inl _ => finSumFinEquiv (Sum.inl (witness.2 j))
    | Sum.inr i => finSumFinEquiv (Sum.inr i))

private lemma extensionRelation_shape_witness {l d : ℕ} (i₀ : Fin l)
    (p : FreimanRelationIndex 2 (l + d)) :
    extensionRelation (extensionShape p) (extensionBaseWitness i₀ p) = p := by
  apply Prod.ext <;> funext j
  · generalize hz : finSumFinEquiv.symm (p.1 j) = z
    obtain i | i := z
    · simpa [extensionRelation, extensionShape, extensionSlot, extensionBaseWitness,
        extensionBaseIndex, Function.comp_def, hz] using
          finSumFinEquiv.apply_symm_apply (p.1 j)
    · simpa [extensionRelation, extensionShape, extensionSlot, extensionBaseWitness,
        extensionBaseIndex, Function.comp_def, hz] using
          finSumFinEquiv.apply_symm_apply (p.1 j)
  · generalize hz : finSumFinEquiv.symm (p.2 j) = z
    obtain i | i := z
    · simpa [extensionRelation, extensionShape, extensionSlot, extensionBaseWitness,
        extensionBaseIndex, Function.comp_def, hz] using
          finSumFinEquiv.apply_symm_apply (p.2 j)
    · simpa [extensionRelation, extensionShape, extensionSlot, extensionBaseWitness,
        extensionBaseIndex, Function.comp_def, hz] using
          finSumFinEquiv.apply_symm_apply (p.2 j)

private lemma card_extensionShape (d : ℕ) :
    Fintype.card (ExtensionShape d) = (d + 1) ^ 4 := by
  simp only [ExtensionShape, ExtensionSlot, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  ring

private noncomputable instance extensionWitnessLinearOrder (l : ℕ) :
    LinearOrder (FreimanRelationIndex 2 l) :=
  LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective

private noncomputable def extensionWitnesses {l d : ℕ} (a : Fin (l + d) → ℕ)
    (shape : ExtensionShape d) : Finset (FreimanRelationIndex 2 l) := by
  classical
  exact Finset.univ.filter fun witness ↦
    freimanRelationHolds a (extensionRelation shape witness)

private noncomputable def extensionCode {l d : ℕ} (a : Fin (l + d) → ℕ) :
    ExtensionShape d → Option (FreimanRelationIndex 2 l) :=
  fun shape ↦ if h : (extensionWitnesses a shape).Nonempty then
    some ((extensionWitnesses a shape).min' h) else none

private lemma extensionCode_eq_none_iff {l d : ℕ} (a : Fin (l + d) → ℕ)
    (shape : ExtensionShape d) :
    extensionCode a shape = none ↔ (extensionWitnesses a shape) = ∅ := by
  classical
  unfold extensionCode
  split_ifs with h
  · simp only [false_iff]
    exact h.ne_empty
  · simp only [true_iff]
    exact Finset.not_nonempty_iff_eq_empty.mp h

private lemma extensionCode_some_mem {l d : ℕ} (a : Fin (l + d) → ℕ)
    (shape : ExtensionShape d) {witness : FreimanRelationIndex 2 l}
    (hcode : extensionCode a shape = some witness) :
    witness ∈ extensionWitnesses a shape := by
  classical
  unfold extensionCode at hcode
  split_ifs at hcode with h
  rw [Option.some.injEq] at hcode
  rw [← hcode]
  exact Finset.min'_mem _ _

private lemma extensionCode_ne_none_of_relation {l d : ℕ} (i₀ : Fin l)
    (a : Fin (l + d) → ℕ) (p : FreimanRelationIndex 2 (l + d))
    (hp : freimanRelationHolds a p) :
    extensionCode a (extensionShape p) ≠ none := by
  classical
  intro hnone
  have hempty := (extensionCode_eq_none_iff a (extensionShape p)).mp hnone
  have hwitness : extensionBaseWitness i₀ p ∈
      extensionWitnesses a (extensionShape p) := by
    simp only [extensionWitnesses, Finset.mem_filter, Finset.mem_univ, true_and,
      extensionRelation_shape_witness]
    exact hp
  rw [hempty] at hwitness
  simp at hwitness

private lemma card_extensionCodeType (l d : ℕ) :
    Fintype.card (ExtensionShape d → Option (FreimanRelationIndex 2 l)) =
      (1 + l ^ 4) ^ ((d + 1) ^ 4) := by
  rw [Fintype.card_fun, card_extensionShape]
  simp only [Fintype.card_option, FreimanRelationIndex, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin]
  congr 1
  ring

def extensionBaseTuple {l d : ℕ} (a : Fin (l + d) → ℕ) : Fin l → ℕ :=
  fun i ↦ a (finSumFinEquiv (Sum.inl i))

private lemma extensionSlot_sub_eq_base_sub {l d : ℕ} (i₀ : Fin l)
    (a : Fin (l + d) → ℕ) {i j : Fin (l + d)}
    (hslot : extensionSlot i = extensionSlot j) :
    (a i : ℤ) - a j =
      extensionBaseTuple a (extensionBaseIndex i₀ i) -
        extensionBaseTuple a (extensionBaseIndex i₀ j) := by
  generalize hi : finSumFinEquiv.symm i = si
  generalize hj : finSumFinEquiv.symm j = sj
  obtain i' | i' := si <;> obtain j' | j' := sj
  · have hi' := finSumFinEquiv.apply_symm_apply i
    have hj' := finSumFinEquiv.apply_symm_apply j
    simp only [hi, hj] at hi' hj'
    simp [extensionBaseIndex, extensionBaseTuple, ← hi', ← hj']
  · simp [extensionSlot, hi, hj] at hslot
  · simp [extensionSlot, hi, hj] at hslot
  · have hij : i' = j' := by
      simpa [extensionSlot, hi, hj] using hslot
    subst j'
    have hi' := finSumFinEquiv.apply_symm_apply i
    have hj' := finSumFinEquiv.apply_symm_apply j
    simp only [hi, hj] at hi' hj'
    rw [← hi', ← hj']
    simp [extensionBaseIndex, extensionBaseTuple]

private def extensionComparison {l d : ℕ} (i₀ : Fin l)
    (p q : FreimanRelationIndex 2 (l + d)) : FreimanRelationIndex 4 l :=
  (fun j ↦ match finSumFinEquiv.symm j with
    | Sum.inl k => extensionBaseIndex i₀ (p.1 k)
    | Sum.inr k => extensionBaseIndex i₀ (q.2 k),
   fun j ↦ match finSumFinEquiv.symm j with
    | Sum.inl k => extensionBaseIndex i₀ (p.2 k)
    | Sum.inr k => extensionBaseIndex i₀ (q.1 k))

private lemma freimanRelationHolds_iff_of_same_extensionShape {l d : ℕ}
    (i₀ : Fin l) (a : Fin (l + d) → ℕ)
    (p q : FreimanRelationIndex 2 (l + d))
    (hshape : extensionShape p = extensionShape q)
    (hcomparison : freimanRelationHolds (extensionBaseTuple a)
      (extensionComparison i₀ p q)) :
    freimanRelationHolds a p ↔ freimanRelationHolds a q := by
  have hleft (j : Fin 2) : extensionSlot (p.1 j) = extensionSlot (q.1 j) := by
    exact congrFun (congrArg Prod.fst hshape) j
  have hright (j : Fin 2) : extensionSlot (p.2 j) = extensionSlot (q.2 j) := by
    exact congrFun (congrArg Prod.snd hshape) j
  have hl0 := extensionSlot_sub_eq_base_sub i₀ a (hleft 0)
  have hl1 := extensionSlot_sub_eq_base_sub i₀ a (hleft 1)
  have hr0 := extensionSlot_sub_eq_base_sub i₀ a (hright 0)
  have hr1 := extensionSlot_sub_eq_base_sub i₀ a (hright 1)
  unfold freimanRelationHolds at hcomparison ⊢
  simp only [Fin.sum_univ_two] at ⊢
  rw [← Equiv.sum_comp (@finSumFinEquiv 2 2)] at hcomparison
  rw [← Equiv.sum_comp (@finSumFinEquiv 2 2)] at hcomparison
  simp only [extensionComparison, Equiv.symm_apply_apply,
    Fintype.sum_sum_type, Fin.sum_univ_two] at hcomparison
  have hcomparisonZ :
      (extensionBaseTuple a (extensionBaseIndex i₀ (p.1 0)) : ℤ) +
          extensionBaseTuple a (extensionBaseIndex i₀ (p.1 1)) +
          extensionBaseTuple a (extensionBaseIndex i₀ (q.2 0)) +
          extensionBaseTuple a (extensionBaseIndex i₀ (q.2 1)) =
        extensionBaseTuple a (extensionBaseIndex i₀ (p.2 0)) +
          extensionBaseTuple a (extensionBaseIndex i₀ (p.2 1)) +
          extensionBaseTuple a (extensionBaseIndex i₀ (q.1 0)) +
          extensionBaseTuple a (extensionBaseIndex i₀ (q.1 1)) := by
    exact_mod_cast (by omega)
  constructor <;> intro hrelation
  · have hrelationZ : (a (p.1 0) : ℤ) + a (p.1 1) =
        a (p.2 0) + a (p.2 1) := by exact_mod_cast hrelation
    exact_mod_cast (by omega :
      (a (q.1 0) : ℤ) + a (q.1 1) = a (q.2 0) + a (q.2 1))
  · have hrelationZ : (a (q.1 0) : ℤ) + a (q.1 1) =
        a (q.2 0) + a (q.2 1) := by exact_mod_cast hrelation
    exact_mod_cast (by omega :
      (a (p.1 0) : ℤ) + a (p.1 1) = a (p.2 0) + a (p.2 1))

private lemma extensionShape_extensionRelation {l d : ℕ} (shape : ExtensionShape d)
    (witness : FreimanRelationIndex 2 l) :
    extensionShape (extensionRelation shape witness) = shape := by
  apply Prod.ext <;> funext j
  · cases h : shape.1 j <;>
      simp [extensionShape, extensionRelation, extensionSlot, Function.comp_def, h]
  · cases h : shape.2 j <;>
      simp [extensionShape, extensionRelation, extensionSlot, Function.comp_def, h]

private lemma freimanRelationHolds_extensionComparison {l d : ℕ}
    (i₀ : Fin l) (a : Fin (l + d) → ℕ)
    (p q : FreimanRelationIndex 2 (l + d))
    (hshape : extensionShape p = extensionShape q)
    (hp : freimanRelationHolds a p) (hq : freimanRelationHolds a q) :
    freimanRelationHolds (extensionBaseTuple a) (extensionComparison i₀ p q) := by
  have hleft (j : Fin 2) : extensionSlot (p.1 j) = extensionSlot (q.1 j) := by
    exact congrFun (congrArg Prod.fst hshape) j
  have hright (j : Fin 2) : extensionSlot (p.2 j) = extensionSlot (q.2 j) := by
    exact congrFun (congrArg Prod.snd hshape) j
  have hl0 := extensionSlot_sub_eq_base_sub i₀ a (hleft 0)
  have hl1 := extensionSlot_sub_eq_base_sub i₀ a (hleft 1)
  have hr0 := extensionSlot_sub_eq_base_sub i₀ a (hright 0)
  have hr1 := extensionSlot_sub_eq_base_sub i₀ a (hright 1)
  unfold freimanRelationHolds at hp hq ⊢
  simp only [Fin.sum_univ_two] at hp hq
  rw [← Equiv.sum_comp (@finSumFinEquiv 2 2)]
  rw [← Equiv.sum_comp (@finSumFinEquiv 2 2)]
  simp only [extensionComparison, Equiv.symm_apply_apply,
    Fintype.sum_sum_type, Fin.sum_univ_two]
  have hpZ : (a (p.1 0) : ℤ) + a (p.1 1) = a (p.2 0) + a (p.2 1) := by
    exact_mod_cast hp
  have hqZ : (a (q.1 0) : ℤ) + a (q.1 1) = a (q.2 0) + a (q.2 1) := by
    exact_mod_cast hq
  exact_mod_cast (by omega)

private lemma freimanRelations_iff_of_extensionCode_eq {l d : ℕ} (i₀ : Fin l)
    (a b : Fin (l + d) → ℕ) (hcode : extensionCode a = extensionCode b)
    (hbase : ∀ p : FreimanRelationIndex 4 l,
      freimanRelationHolds (extensionBaseTuple a) p ↔
        freimanRelationHolds (extensionBaseTuple b) p)
    (p : FreimanRelationIndex 2 (l + d)) :
    freimanRelationHolds a p ↔ freimanRelationHolds b p := by
  have forward {a b : Fin (l + d) → ℕ}
      (hcode : extensionCode a = extensionCode b)
      (hbase : ∀ r : FreimanRelationIndex 4 l,
        freimanRelationHolds (extensionBaseTuple a) r ↔
          freimanRelationHolds (extensionBaseTuple b) r)
      (hp : freimanRelationHolds a p) : freimanRelationHolds b p := by
    classical
    have hsome : extensionCode a (extensionShape p) ≠ none :=
      extensionCode_ne_none_of_relation i₀ a p hp
    generalize hw : extensionCode a (extensionShape p) = code
    obtain _ | witness := code
    · exact (hsome hw).elim
    · have hcodeA : extensionCode a (extensionShape p) = some witness := hw
      have hcodeB : extensionCode b (extensionShape p) = some witness := by
        rw [← hcode]
        exact hcodeA
      have hqa : freimanRelationHolds a
          (extensionRelation (extensionShape p) witness) := by
        exact (Finset.mem_filter.mp
          (extensionCode_some_mem a (extensionShape p) hcodeA)).2
      have hqb : freimanRelationHolds b
          (extensionRelation (extensionShape p) witness) := by
        exact (Finset.mem_filter.mp
          (extensionCode_some_mem b (extensionShape p) hcodeB)).2
      have hshape : extensionShape p =
          extensionShape (extensionRelation (extensionShape p) witness) := by
        rw [extensionShape_extensionRelation]
      have hcomparison := freimanRelationHolds_extensionComparison i₀ a p
        (extensionRelation (extensionShape p) witness) hshape hp hqa
      exact (freimanRelationHolds_iff_of_same_extensionShape i₀ b p
        (extensionRelation (extensionShape p) witness) hshape
        ((hbase (extensionComparison i₀ p
          (extensionRelation (extensionShape p) witness))).mp hcomparison)).mpr hqb
  constructor
  · exact forward hcode hbase
  · exact forward hcode.symm fun r ↦ (hbase r).symm

private lemma card_image_le_fintype_of_eq_imp_eq {α β γ : Type*}
    [DecidableEq β] [Fintype γ] (S : Finset α) (f : α → β) (g : α → γ)
    (hfactor : ∀ x ∈ S, ∀ y ∈ S, g x = g y → f x = f y) :
    (S.image f).card ≤ Fintype.card γ := by
  classical
  let pick (z : ↑(S.image f)) : α := Classical.choose (Finset.mem_image.mp z.2)
  have pick_mem (z : ↑(S.image f)) : pick z ∈ S :=
    (Classical.choose_spec (Finset.mem_image.mp z.2)).1
  have f_pick (z : ↑(S.image f)) : f (pick z) = z :=
    (Classical.choose_spec (Finset.mem_image.mp z.2)).2
  have hinjective : Function.Injective (fun z : ↑(S.image f) ↦ g (pick z)) := by
    intro z w hzw
    apply Subtype.ext
    rw [← f_pick z, ← f_pick w]
    exact hfactor (pick z) (pick_mem z) (pick w) (pick_mem w) hzw
  simpa using Fintype.card_le_of_injective (fun z ↦ g (pick z)) hinjective

/-- Green's extension lemma for labeled tuples: once the base `4`-relation system is fixed,
the full `2`-relation system has at most `(1+l^4)^((d+1)^4)` possibilities. -/
private def pairSumTuple {l u : ℕ} (a : Fin l → ℕ)
    (representation : Fin u → Fin l × Fin l) : Fin u → ℕ :=
  fun i ↦ a (representation i).1 + a (representation i).2

private def pairSumRelation {l u : ℕ} (representation : Fin u → Fin l × Fin l)
    (p : FreimanRelationIndex 4 u) : FreimanRelationIndex 8 l :=
  (fun j ↦ match finSumFinEquiv.symm j with
    | Sum.inl k => (representation (p.1 k)).1
    | Sum.inr k => (representation (p.1 k)).2,
   fun j ↦ match finSumFinEquiv.symm j with
    | Sum.inl k => (representation (p.2 k)).1
    | Sum.inr k => (representation (p.2 k)).2)

private lemma pairSumTuple_relation_iff {l u : ℕ} (a : Fin l → ℕ)
    (representation : Fin u → Fin l × Fin l) (p : FreimanRelationIndex 4 u) :
    freimanRelationHolds (pairSumTuple a representation) p ↔
      freimanRelationHolds a (pairSumRelation representation p) := by
  unfold freimanRelationHolds pairSumTuple
  simp_rw [Finset.sum_add_distrib]
  unfold pairSumRelation
  rw [← Equiv.sum_comp (@finSumFinEquiv 4 4)]
  rw [← Equiv.sum_comp (@finSumFinEquiv 4 4)]
  simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type]

private lemma pairSumTuple_relations_iff {l u : ℕ} {a b : Fin l → ℕ}
    (hcore : ∀ p : FreimanRelationIndex 8 l,
      freimanRelationHolds a p ↔ freimanRelationHolds b p)
    (representation : Fin u → Fin l × Fin l) (p : FreimanRelationIndex 4 u) :
    freimanRelationHolds (pairSumTuple a representation) p ↔
      freimanRelationHolds (pairSumTuple b representation) p := by
  rw [pairSumTuple_relation_iff, pairSumTuple_relation_iff]
  exact hcore (pairSumRelation representation p)

private noncomputable def chosenRestrictedRepresentation (A : Finset ℕ) {x : ℕ}
    (hx : x ∈ restrictedSumset A) : ℕ × ℕ :=
  Classical.choose (mem_restrictedSumset_iff_representationPairs_nonempty.mp hx)

private lemma chosenRestrictedRepresentation_mem (A : Finset ℕ) {x : ℕ}
    (hx : x ∈ restrictedSumset A) :
    chosenRestrictedRepresentation A hx ∈ restrictedRepresentationPairs A x :=
  Classical.choose_spec (mem_restrictedSumset_iff_representationPairs_nonempty.mp hx)

private noncomputable def restrictedSumRepresentation {l u : ℕ}
    (A B : Finset ℕ) (hA : A.card = l) (hB : B.card = u)
    (hBA : B ⊆ restrictedSumset A) : Fin u → Fin l × Fin l :=
  fun i ↦
    let p := chosenRestrictedRepresentation A (hBA ((B.orderIsoOfFin hB i).2))
    ((A.orderIsoOfFin hA).symm
      ⟨p.1, (mem_restrictedRepresentationPairs.mp
        (chosenRestrictedRepresentation_mem A (hBA ((B.orderIsoOfFin hB i).2)))).1⟩,
     (A.orderIsoOfFin hA).symm
      ⟨p.2, (mem_restrictedRepresentationPairs.mp
        (chosenRestrictedRepresentation_mem A (hBA ((B.orderIsoOfFin hB i).2)))).2.1⟩)

private lemma restrictedSumRepresentation_ne {l u : ℕ}
    (A B : Finset ℕ) (hA : A.card = l) (hB : B.card = u)
    (hBA : B ⊆ restrictedSumset A) (i : Fin u) :
    (restrictedSumRepresentation A B hA hB hBA i).1 ≠
      (restrictedSumRepresentation A B hA hB hBA i).2 := by
  intro heq
  have hvalues := congrArg (fun j : Fin l ↦ (A.orderIsoOfFin hA j).1) heq
  unfold restrictedSumRepresentation at hvalues
  simp only [OrderIso.apply_symm_apply] at hvalues
  exact (mem_restrictedRepresentationPairs.mp
    (chosenRestrictedRepresentation_mem A
      (hBA ((B.orderIsoOfFin hB i).2)))).2.2.1 hvalues

private lemma pairSumTuple_restrictedSumRepresentation {l u : ℕ}
    (A B : Finset ℕ) (hA : A.card = l) (hB : B.card = u)
    (hBA : B ⊆ restrictedSumset A) :
    pairSumTuple (fun i ↦ (A.orderIsoOfFin hA i).1)
        (restrictedSumRepresentation A B hA hB hBA) =
      fun i ↦ (B.orderIsoOfFin hB i).1 := by
  funext i
  unfold pairSumTuple restrictedSumRepresentation
  simp only [OrderIso.apply_symm_apply]
  exact (mem_restrictedRepresentationPairs.mp
    (chosenRestrictedRepresentation_mem A
      (hBA ((B.orderIsoOfFin hB i).2)))).2.2.2

private lemma injective_of_four_relations_iff {u : ℕ} {a b : Fin u → ℕ}
    (ha : Function.Injective a)
    (hrelations : ∀ p : FreimanRelationIndex 4 u,
      freimanRelationHolds a p ↔ freimanRelationHolds b p) :
    Function.Injective b := by
  intro i j hij
  let p : FreimanRelationIndex 4 u := (fun _ ↦ i, fun _ ↦ j)
  have hp : freimanRelationHolds b p := by
    unfold freimanRelationHolds p
    simp [hij]
  have hpA := (hrelations p).mpr hp
  unfold freimanRelationHolds p at hpA
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hpA
  exact ha (by omega)

private def pairSumRange {l u : ℕ} (b : Fin l → ℕ)
    (representation : Fin u → Fin l × Fin l) : Finset ℕ :=
  Finset.univ.image (pairSumTuple b representation)

private lemma pairSumRange_subset_restrictedSumset {l u : ℕ} (b : Fin l → ℕ)
    (hb : Function.Injective b) (representation : Fin u → Fin l × Fin l)
    (hne : ∀ i, (representation i).1 ≠ (representation i).2) :
    pairSumRange b representation ⊆ restrictedSumset (Finset.univ.image b) := by
  intro x hx
  rw [pairSumRange, Finset.mem_image] at hx
  obtain ⟨i, -, rfl⟩ := hx
  rw [restrictedSumset, Finset.mem_image]
  refine ⟨(b (representation i).1, b (representation i).2), ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨by simp, by simp⟩, hb.ne (hne i)⟩

/-! ### Freiman dimension and determining coordinates -/

abbrev RelationIndex (t : ℕ) :=
  Fin t × Fin t × Fin t × Fin t

/-- The coefficient vector of `aᵢ + aⱼ = aₖ + aₗ`. -/
private def relationVector {t : ℕ} (p : RelationIndex t) : Fin t →₀ ℚ :=
  Finsupp.single p.1 1 + Finsupp.single p.2.1 1 -
    Finsupp.single p.2.2.1 1 - Finsupp.single p.2.2.2 1

def relationHolds {t : ℕ} (a : Fin t → ℕ) (p : RelationIndex t) : Prop :=
  a p.1 + a p.2.1 = a p.2.2.1 + a p.2.2.2

private def tupleEval {t : ℕ} (a : Fin t → ℕ) : (Fin t →₀ ℚ) →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ fun i ↦ (a i : ℚ)

private def coefficientSum (t : ℕ) : (Fin t →₀ ℚ) →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ fun _ ↦ 1

private def zeroSumSpace (t : ℕ) : Submodule ℚ (Fin t →₀ ℚ) :=
  LinearMap.ker (coefficientSum t)

private lemma tupleEval_relationVector {t : ℕ} (a : Fin t → ℕ) (p : RelationIndex t) :
    tupleEval a (relationVector p) =
      (a p.1 : ℚ) + a p.2.1 - a p.2.2.1 - a p.2.2.2 := by
  simp only [tupleEval, relationVector, map_sub, map_add,
    Finsupp.linearCombination_single, one_smul]

private lemma relationVector_mem_ker_iff {t : ℕ} (a : Fin t → ℕ) (p : RelationIndex t) :
    relationVector p ∈ LinearMap.ker (tupleEval a) ↔ relationHolds a p := by
  rw [LinearMap.mem_ker, tupleEval_relationVector]
  unfold relationHolds
  constructor <;> intro h
  · exact_mod_cast (by linarith :
      (a p.1 : ℚ) + a p.2.1 = a p.2.2.1 + a p.2.2.2)
  · have h' : (a p.1 : ℚ) + a p.2.1 = a p.2.2.1 + a p.2.2.2 := by
      exact_mod_cast h
    linarith

private lemma coefficientSum_relationVector {t : ℕ} (p : RelationIndex t) :
    coefficientSum t (relationVector p) = 0 := by
  simp only [coefficientSum, relationVector, map_sub, map_add,
    Finsupp.linearCombination_single, one_smul]
  ring

/-- The rational span of the additive relations satisfied by an enumerated set. -/
private def relationSpace {t : ℕ} (a : Fin t → ℕ) : Submodule ℚ (Fin t →₀ ℚ) :=
  Submodule.span ℚ (relationVector '' {p | relationHolds a p})

private lemma relationSpace_le_zeroSumSpace {t : ℕ} (a : Fin t → ℕ) :
    relationSpace a ≤ zeroSumSpace t := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, -, rfl⟩
  exact coefficientSum_relationVector p

private def relationSpaceInZeroSum {t : ℕ} (a : Fin t → ℕ) :
    Submodule ℚ (zeroSumSpace t) :=
  (relationSpace a).comap (zeroSumSpace t).subtype

private lemma finrank_relationSpaceInZeroSum {t : ℕ} (a : Fin t → ℕ) :
    Module.finrank ℚ (relationSpaceInZeroSum a) = Module.finrank ℚ (relationSpace a) := by
  rw [← Submodule.finrank_map_subtype_eq (zeroSumSpace t) (relationSpaceInZeroSum a)]
  unfold relationSpaceInZeroSum
  rw [Submodule.map_comap_subtype]
  exact congrArg (fun S : Submodule ℚ (Fin t →₀ ℚ) ↦ Module.finrank ℚ S)
    (inf_eq_right.mpr (relationSpace_le_zeroSumSpace a))

def relationModelDim {t : ℕ} (a : Fin t → ℕ) : ℕ :=
  Module.finrank ℚ (zeroSumSpace t ⧸ relationSpaceInZeroSum a)

private lemma coefficientSum_surjective {t : ℕ} (ht : 0 < t) :
    Function.Surjective (coefficientSum t) := by
  intro x
  let i : Fin t := ⟨0, ht⟩
  refine ⟨Finsupp.single i x, ?_⟩
  simp [coefficientSum]

private lemma finrank_zeroSumSpace {t : ℕ} (ht : 0 < t) :
    Module.finrank ℚ (zeroSumSpace t) = t - 1 := by
  change Module.finrank ℚ (LinearMap.ker (coefficientSum t)) = t - 1
  have hrange : LinearMap.range (coefficientSum t) = ⊤ :=
    LinearMap.range_eq_top.mpr (coefficientSum_surjective ht)
  have h := LinearMap.finrank_range_add_finrank_ker (coefficientSum t)
  rw [hrange, finrank_top] at h
  have h' : 1 + Module.finrank ℚ (LinearMap.ker (coefficientSum t)) = t := by
    simpa only [Module.finrank_self,
      Module.finrank_finsupp_self, Fintype.card_fin] using h
  omega

private lemma relationModelDim_add_relationRank {t : ℕ} (ht : 0 < t) (a : Fin t → ℕ) :
    relationModelDim a + Module.finrank ℚ (relationSpace a) = t - 1 := by
  rw [relationModelDim, ← finrank_relationSpaceInZeroSum]
  exact (Submodule.finrank_quotient_add_finrank (relationSpaceInZeroSum a)).trans
    (finrank_zeroSumSpace ht)

private lemma relation_iff_mem_relationSpace {t : ℕ} (a : Fin t → ℕ)
    (p : RelationIndex t) :
    relationHolds a p ↔ relationVector p ∈ relationSpace a := by
  constructor
  · intro hp
    exact Submodule.subset_span ⟨p, hp, rfl⟩
  · intro hp
    rw [← relationVector_mem_ker_iff]
    exact (Submodule.span_le.mpr fun _ h ↦ by
      obtain ⟨q, hq, rfl⟩ := h
      exact relationVector_mem_ker_iff a q |>.mpr hq) hp

private lemma finrank_relationSpace_le {t : ℕ} (a : Fin t → ℕ) :
    Module.finrank ℚ (relationSpace a) ≤ t := by
  refine (relationSpace a).finrank_le.trans_eq ?_
  simp

/-- At most `t` four-term relations span all relations of a `t`-tuple. The function is padded by
the zero relation so that its type has exactly `t` entries, which is what yields `t^(4t)` codes. -/
private lemma exists_relation_code {t : ℕ} (ht : 0 < t) (a : Fin t → ℕ) :
    ∃ code : Fin t → RelationIndex t,
      Submodule.span ℚ (relationVector '' Set.range code) = relationSpace a := by
  let relations : Set (Fin t →₀ ℚ) := relationVector '' {p | relationHolds a p}
  obtain ⟨basis, hbasis_mem, hbasis_span, -⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ relations
  let d := Module.finrank ℚ (Submodule.span ℚ relations)
  have hdt : d ≤ t := by
    change Module.finrank ℚ (relationSpace a) ≤ t
    exact finrank_relationSpace_le a
  let index : Fin d → RelationIndex t := fun i ↦ Classical.choose (hbasis_mem i)
  have hindex (i : Fin d) : relationVector (index i) = basis i := by
    exact Classical.choose_spec (hbasis_mem i) |>.2
  let zeroIndex : RelationIndex t :=
    (⟨0, ht⟩, ⟨0, ht⟩, ⟨0, ht⟩, ⟨0, ht⟩)
  have hzero : relationVector zeroIndex = 0 := by
    dsimp [zeroIndex, relationVector]
    abel
  let code : Fin t → RelationIndex t := fun i ↦
    if hi : i.val < d then index ⟨i.val, hi⟩ else zeroIndex
  refine ⟨code, ?_⟩
  change Submodule.span ℚ (relationVector '' Set.range code) = Submodule.span ℚ relations
  rw [← hbasis_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    by_cases hi : i.val < d
    · dsimp only [code]
      rw [dif_pos hi, hindex]
      exact Submodule.subset_span ⟨⟨i.val, hi⟩, rfl⟩
    · dsimp only [code]
      rw [dif_neg hi, hzero]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    let j : Fin t := ⟨i.val, lt_of_lt_of_le i.isLt hdt⟩
    rw [← hindex]
    refine Submodule.subset_span ⟨index i, ⟨j, ?_⟩, rfl⟩
    have hj : j.val < d := by
      dsimp [j, d]
      exact i.isLt
    simp [code, hj, j]

private noncomputable def relationCode {t : ℕ} (ht : 0 < t) (a : Fin t → ℕ) :
    Fin t → RelationIndex t :=
  Classical.choose (exists_relation_code ht a)

private lemma relationCode_span {t : ℕ} (ht : 0 < t) (a : Fin t → ℕ) :
    Submodule.span ℚ (relationVector '' Set.range (relationCode ht a)) = relationSpace a :=
  Classical.choose_spec (exists_relation_code ht a)

private lemma relations_iff_of_relationCode_eq {t : ℕ} (ht : 0 < t)
    {a b : Fin t → ℕ} (hcode : relationCode ht a = relationCode ht b)
    (p : RelationIndex t) :
    relationHolds a p ↔ relationHolds b p := by
  rw [relation_iff_mem_relationSpace, relation_iff_mem_relationSpace,
    ← relationCode_span ht a, ← relationCode_span ht b, hcode]

private def baseDifference {t : ℕ} (i₀ i : Fin t) : zeroSumSpace t :=
  ⟨Finsupp.single i 1 - Finsupp.single i₀ 1, by
    simp [zeroSumSpace, coefficientSum]⟩

private noncomputable def relationModelEquiv {t : ℕ} (a : Fin t → ℕ) :
    (zeroSumSpace t ⧸ relationSpaceInZeroSum a) ≃ₗ[ℚ]
      (Fin (relationModelDim a) → ℚ) :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_fin_fun]
    rfl)

private noncomputable def relationModel {t : ℕ} (a : Fin t → ℕ) (i₀ i : Fin t) :
    Fin (relationModelDim a) → ℚ :=
  relationModelEquiv a ((relationSpaceInZeroSum a).mkQ (baseDifference i₀ i))

private lemma relationVector_eq_baseDifferences {t : ℕ} (i₀ : Fin t)
    (p : RelationIndex t) :
    relationVector p =
      (baseDifference i₀ p.1 : Fin t →₀ ℚ) + baseDifference i₀ p.2.1 -
        baseDifference i₀ p.2.2.1 - baseDifference i₀ p.2.2.2 := by
  unfold relationVector baseDifference
  ext j
  simp
  ring

private lemma relationModel_add_eq_add_iff {t : ℕ} (a : Fin t → ℕ) (i₀ : Fin t)
    (p : RelationIndex t) :
    relationModel a i₀ p.1 + relationModel a i₀ p.2.1 =
        relationModel a i₀ p.2.2.1 + relationModel a i₀ p.2.2.2 ↔
      relationHolds a p := by
  rw [relation_iff_mem_relationSpace]
  unfold relationModel
  constructor
  · intro h
    have hzero : (relationSpaceInZeroSum a).mkQ
        (baseDifference i₀ p.1 + baseDifference i₀ p.2.1 -
          baseDifference i₀ p.2.2.1 - baseDifference i₀ p.2.2.2) = 0 := by
      apply (relationModelEquiv a).injective
      simp only [map_add, map_sub, map_zero]
      rw [sub_sub, sub_eq_zero]
      exact h
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hzero
    change ((baseDifference i₀ p.1 : Fin t →₀ ℚ) + baseDifference i₀ p.2.1 -
      baseDifference i₀ p.2.2.1 - baseDifference i₀ p.2.2.2) ∈ relationSpace a at hzero
    rwa [← relationVector_eq_baseDifferences i₀] at hzero
  · intro h
    have hmem : baseDifference i₀ p.1 + baseDifference i₀ p.2.1 -
        baseDifference i₀ p.2.2.1 - baseDifference i₀ p.2.2.2 ∈
        relationSpaceInZeroSum a := by
      change ((baseDifference i₀ p.1 : Fin t →₀ ℚ) + baseDifference i₀ p.2.1 -
        baseDifference i₀ p.2.2.1 - baseDifference i₀ p.2.2.2) ∈ relationSpace a
      rwa [← relationVector_eq_baseDifferences i₀]
    have hzero : (relationSpaceInZeroSum a).mkQ
        (baseDifference i₀ p.1 + baseDifference i₀ p.2.1 -
          baseDifference i₀ p.2.2.1 - baseDifference i₀ p.2.2.2) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hmem
    have hout := congrArg (relationModelEquiv a) hzero
    simp only [map_add, map_sub, map_zero] at hout
    rw [← sub_eq_zero]
    simpa only [sub_sub] using hout

private lemma span_baseDifferences {t : ℕ} (i₀ : Fin t) :
    Submodule.span ℚ (Set.range (baseDifference i₀)) = ⊤ := by
  apply top_unique
  intro x _
  have hsum : ∑ i, (x.1 i : ℚ) = 0 := by
    have hx : coefficientSum t x.1 = 0 := x.2
    unfold coefficientSum at hx
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_fintype _ _ (fun _ ↦ zero_smul ℚ 1)] at hx
    simpa only [smul_eq_mul, mul_one] using hx
  have hmem : (∑ i, (x.1 i : ℚ) • baseDifference i₀ i) ∈
      Submodule.span ℚ (Set.range (baseDifference i₀)) := by
    exact Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  convert hmem using 1
  · apply Subtype.ext
    ext j
    have hcoord : ∑ i, (x.1 i : ℚ) * (Finsupp.single i 1 : Fin t →₀ ℚ) j = x.1 j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [hij]
      · simp
    simp [baseDifference, mul_sub, ← Finset.sum_mul, hsum, hcoord]

private lemma span_relationModel {t : ℕ} (a : Fin t → ℕ) (i₀ : Fin t) :
    Submodule.span ℚ (Set.range (relationModel a i₀)) = ⊤ := by
  let L : zeroSumSpace t →ₗ[ℚ] (Fin (relationModelDim a) → ℚ) :=
    (relationModelEquiv a).toLinearMap.comp (relationSpaceInZeroSum a).mkQ
  have hRange : Set.range (relationModel a i₀) = L '' Set.range (baseDifference i₀) := by
    ext v
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨baseDifference i₀ i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [hRange]
  rw [← Submodule.map_span, span_baseDifferences, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr
    ((relationModelEquiv a).surjective.comp (relationSpaceInZeroSum a).mkQ_surjective)

private lemma real_span_of_rational_span {d t : ℕ} (v : Fin t → (Fin d → ℚ))
    (hspan : Submodule.span ℚ (Set.range v) = ⊤) :
    Submodule.span ℝ (Set.range (rationalVectorToReal ∘ v)) = ⊤ := by
  apply top_unique
  intro y _
  convert
    (Submodule.sum_mem (Submodule.span ℝ (Set.range (rationalVectorToReal ∘ v))) ?_ :
      (∑ j, y j • rationalVectorToReal (Pi.single j 1 : Fin d → ℚ)) ∈
        Submodule.span ℝ (Set.range (rationalVectorToReal ∘ v))) using 1
  · ext j
    have hcoord : ∑ i, y i * (Pi.single i 1 : Fin d → ℚ) j = y j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [hij]
      · simp
    simpa [rationalVectorToReal] using hcoord.symm
  · intro j _
    apply Submodule.smul_mem
    have hq : (Pi.single j 1 : Fin d → ℚ) ∈ Submodule.span ℚ (Set.range v) := by
      rw [hspan]
      exact Submodule.mem_top
    have hcast (x : Fin d → ℚ) (hx : x ∈ Submodule.span ℚ (Set.range v)) :
        rationalVectorToReal x ∈
          Submodule.span ℝ (Set.range (rationalVectorToReal ∘ v)) := by
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨i, rfl⟩ := hx
          exact Submodule.subset_span ⟨i, rfl⟩
      | zero =>
          convert Submodule.zero_mem
            (Submodule.span ℝ (Set.range (rationalVectorToReal ∘ v))) using 1
          ext i
          simp [rationalVectorToReal]
      | add x y _ _ hx hy =>
          convert Submodule.add_mem
            (Submodule.span ℝ (Set.range (rationalVectorToReal ∘ v))) hx hy using 1
          ext i
          simp [rationalVectorToReal]
      | smul q x _ hx =>
          convert Submodule.smul_mem
            (Submodule.span ℝ (Set.range (rationalVectorToReal ∘ v))) (q : ℝ) hx using 1
          ext i
          simp [rationalVectorToReal]
    exact hcast _ hq

private lemma relationModel_zero {t : ℕ} (a : Fin t → ℕ) (i₀ : Fin t) :
    relationModel a i₀ i₀ = 0 := by
  have hbase : baseDifference i₀ i₀ = 0 := by
    apply Subtype.ext
    simp [baseDifference]
  unfold relationModel
  rw [hbase, map_zero, map_zero]

private lemma relationModel_affineDim {t : ℕ} (a : Fin t → ℕ) (i₀ : Fin t) :
    finsetAffineDim (((Finset.univ.image (relationModel a i₀)).image
      rationalVectorToReal)) = relationModelDim a := by
  unfold finsetAffineDim
  rw [direction_affineSpan]
  have hset : (((Finset.univ.image (relationModel a i₀)).image
      rationalVectorToReal : Finset (Fin (relationModelDim a) → ℝ)) :
      Set (Fin (relationModelDim a) → ℝ)) =
      Set.range (rationalVectorToReal ∘ relationModel a i₀) := by
    ext x
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_image,
      Set.mem_range, Function.comp_apply]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨relationModel a i₀ i, ⟨i, rfl⟩, rfl⟩
  rw [hset, vectorSpan_eq_span_vsub_set_right ℝ (p := 0)]
  · have htranslate : ((fun x ↦ x -ᵥ (0 : Fin (relationModelDim a) → ℝ)) ''
        Set.range (rationalVectorToReal ∘ relationModel a i₀)) =
        Set.range (rationalVectorToReal ∘ relationModel a i₀) := by
      simp
    rw [htranslate]
    rw [real_span_of_rational_span _ (span_relationModel a i₀), finrank_top,
      Module.finrank_fin_fun]
  · refine ⟨i₀, ?_⟩
    rw [Function.comp_apply, relationModel_zero]
    ext i
    simp [rationalVectorToReal]

private lemma card_relation_codes (t : ℕ) :
    Fintype.card (Fin t → RelationIndex t) = t ^ (4 * t) := by
  simp only [RelationIndex, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
  have hbase : t * (t * (t * t)) = t ^ 4 := by ring
  rw [hbase]
  rw [pow_mul]

/-! ### Unlabeled finite-set relation classes -/

def finsetTuple {t : ℕ} (X : Finset ℕ) (hX : X.card = t) : Fin t → ℕ :=
  fun i ↦ X.orderIsoOfFin hX i

lemma finsetTuple_injective {t : ℕ} (X : Finset ℕ) (hX : X.card = t) :
    Function.Injective (finsetTuple X hX) := by
  intro i j hij
  exact (X.orderIsoOfFin hX).injective (Subtype.ext hij)

lemma range_finsetTuple {t : ℕ} (X : Finset ℕ) (hX : X.card = t) :
    Set.range (finsetTuple X hX) = X := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact (X.orderIsoOfFin hX i).2
  · intro hx
    refine ⟨(X.orderIsoOfFin hX).symm ⟨x, hx⟩, ?_⟩
    exact congr_arg Subtype.val ((X.orderIsoOfFin hX).apply_symm_apply ⟨x, hx⟩)

abbrev SizedNatFinset (t : ℕ) :=
  {X : Finset ℕ // X.card = t}

def permutedFinsetTuple {t : ℕ} (X : SizedNatFinset t)
    (e : Equiv.Perm (Fin t)) :
    Fin t → ℕ :=
  finsetTuple X.1 X.2 ∘ e

lemma permutedFinsetTuple_injective {t : ℕ} (X : SizedNatFinset t)
    (e : Equiv.Perm (Fin t)) : Function.Injective (permutedFinsetTuple X e) :=
  (finsetTuple_injective X.1 X.2).comp e.injective

lemma range_permutedFinsetTuple {t : ℕ} (X : SizedNatFinset t)
    (e : Equiv.Perm (Fin t)) : Set.range (permutedFinsetTuple X e) = X.1 := by
  rw [permutedFinsetTuple, Set.range_comp, e.surjective.range_eq, Set.image_univ,
    range_finsetTuple X.1 X.2]

private def tupleRange {t : ℕ} (a : Fin t → ℕ) : Finset ℕ :=
  Finset.univ.image a

private lemma card_tupleRange {t : ℕ} (a : Fin t → ℕ) (ha : Function.Injective a) :
    (tupleRange a).card = t := by
  rw [tupleRange, Finset.card_image_of_injective _ ha, Finset.card_univ,
    Fintype.card_fin]

private lemma tupleRange_finsetTuple {t : ℕ} (X : Finset ℕ) (hX : X.card = t) :
    tupleRange (finsetTuple X hX) = X := by
  apply Finset.coe_injective
  simp only [tupleRange, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [range_finsetTuple]

private def tupleRangeSized {t : ℕ} (a : Fin t → ℕ) (ha : Function.Injective a) :
    SizedNatFinset t :=
  ⟨tupleRange a, card_tupleRange a ha⟩

private noncomputable def tupleRangePermutation {t : ℕ} (a : Fin t → ℕ)
    (ha : Function.Injective a) : Equiv.Perm (Fin t) := by
  let index : Fin t → Fin t := fun i ↦
    ((tupleRange a).orderIsoOfFin (card_tupleRange a ha)).symm
      ⟨a i, by simp [tupleRange]⟩
  have hinjective : Function.Injective index := by
    intro i j hij
    apply ha
    exact congrArg Subtype.val
      (((tupleRange a).orderIsoOfFin (card_tupleRange a ha)).symm.injective hij)
  exact Equiv.ofBijective index
    ((Fintype.bijective_iff_injective_and_card index).mpr ⟨hinjective, rfl⟩)

private lemma permutedFinsetTuple_tupleRangePermutation {t : ℕ} (a : Fin t → ℕ)
    (ha : Function.Injective a) :
    permutedFinsetTuple (tupleRangeSized a ha) (tupleRangePermutation a ha) = a := by
  funext i
  unfold permutedFinsetTuple finsetTuple tupleRangePermutation
  simp only [Function.comp_apply, Equiv.ofBijective_apply]
  exact congrArg Subtype.val
    ((tupleRange a).orderIsoOfFin (card_tupleRange a ha) |>.apply_symm_apply
      ⟨a i, by simp [tupleRange]⟩)

def permuteFreimanRelation {s t : ℕ} (e : Equiv.Perm (Fin t))
    (p : FreimanRelationIndex s t) : FreimanRelationIndex s t :=
  (e ∘ p.1, e ∘ p.2)

lemma freimanRelationHolds_comp_perm {s t : ℕ} (a : Fin t → ℕ)
    (e : Equiv.Perm (Fin t)) (p : FreimanRelationIndex s t) :
    freimanRelationHolds (a ∘ e) p ↔
      freimanRelationHolds a (permuteFreimanRelation e p) := by
  rfl

/-- Two finite sets have the same unlabeled `s`-relation system. This is Green's notion of
`s`-isomorphism, expressed using the increasing enumerations of the sets. -/
def FreimanRelationEquivalent {s t : ℕ} (X Y : SizedNatFinset t) : Prop :=
  ∃ e : Equiv.Perm (Fin t),
    ∀ p : FreimanRelationIndex s t,
      freimanRelationHolds (finsetTuple X.1 X.2) p ↔
        freimanRelationHolds (permutedFinsetTuple Y e) p

private lemma freimanRelationEquivalent_tupleRange {s t : ℕ} {a b : Fin t → ℕ}
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hrelations : ∀ p : FreimanRelationIndex s t,
      freimanRelationHolds a p ↔ freimanRelationHolds b p) :
    FreimanRelationEquivalent (s := s) (tupleRangeSized a ha) (tupleRangeSized b hb) := by
  let ea := tupleRangePermutation a ha
  let eb := tupleRangePermutation b hb
  have hea : permutedFinsetTuple (tupleRangeSized a ha) ea = a :=
    permutedFinsetTuple_tupleRangePermutation a ha
  have heb : permutedFinsetTuple (tupleRangeSized b hb) eb = b :=
    permutedFinsetTuple_tupleRangePermutation b hb
  refine ⟨ea.symm.trans eb, ?_⟩
  intro p
  have hleft : finsetTuple (tupleRangeSized a ha).1 (tupleRangeSized a ha).2 =
      a ∘ ea.symm := by
    funext i
    have hi := congrFun hea (ea.symm i)
    simpa [permutedFinsetTuple, Function.comp_def] using hi
  have hright : permutedFinsetTuple (tupleRangeSized b hb) (ea.symm.trans eb) =
      b ∘ ea.symm := by
    funext i
    have hi := congrFun heb (ea.symm i)
    simpa [permutedFinsetTuple, Function.comp_def, Equiv.trans_apply] using hi
  rw [hleft, hright, freimanRelationHolds_comp_perm,
    freimanRelationHolds_comp_perm]
  exact hrelations (permuteFreimanRelation ea.symm p)

private def finsetFreimanRelationCodes {s t : ℕ} (ht : 0 < t)
    (X : SizedNatFinset t) : Finset (Fin t → FreimanRelationIndex s t) :=
  Finset.univ.image fun e : Equiv.Perm (Fin t) ↦
    freimanRelationCode (s := s) ht (permutedFinsetTuple X e)

private lemma finsetFreimanRelationCodes_nonempty {s t : ℕ} (ht : 0 < t)
    (X : SizedNatFinset t) : (finsetFreimanRelationCodes (s := s) ht X).Nonempty := by
  refine ⟨freimanRelationCode (s := s) ht
    (permutedFinsetTuple X (Equiv.refl (Fin t))), ?_⟩
  simp [finsetFreimanRelationCodes]

private lemma finsetFreimanRelationCodes_eq_of_equivalent {s t : ℕ} (ht : 0 < t)
    {X Y : SizedNatFinset t} (hXY : FreimanRelationEquivalent (s := s) X Y) :
    finsetFreimanRelationCodes (s := s) ht X =
      finsetFreimanRelationCodes (s := s) ht Y := by
  obtain ⟨e, he⟩ := hXY
  ext code
  simp only [finsetFreimanRelationCodes, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨pX, rfl⟩
    refine ⟨pX.trans e, ?_⟩
    apply freimanRelationCode_eq_of_relations_iff
    intro p
    unfold permutedFinsetTuple
    rw [freimanRelationHolds_comp_perm, freimanRelationHolds_comp_perm]
    simpa only [permutedFinsetTuple, freimanRelationHolds_comp_perm,
      freimanRelationHolds, permuteFreimanRelation, Equiv.coe_trans,
      Function.comp_def] using
      (he (permuteFreimanRelation pX p)).symm
  · rintro ⟨pY, rfl⟩
    refine ⟨pY.trans e.symm, ?_⟩
    apply freimanRelationCode_eq_of_relations_iff
    intro p
    unfold permutedFinsetTuple
    rw [freimanRelationHolds_comp_perm, freimanRelationHolds_comp_perm]
    simpa only [permutedFinsetTuple, freimanRelationHolds_comp_perm,
      freimanRelationHolds, permuteFreimanRelation, Equiv.coe_trans, Function.comp_def,
      Equiv.apply_symm_apply] using
      he (permuteFreimanRelation (pY.trans e.symm) p)

noncomputable def canonicalFreimanRelationCode {s t : ℕ} (ht : 0 < t)
    (X : SizedNatFinset t) : Fin t → FreimanRelationIndex s t :=
  (finsetFreimanRelationCodes (s := s) ht X).min'
    (finsetFreimanRelationCodes_nonempty (s := s) ht X)

lemma canonicalFreimanRelationCode_mem {s t : ℕ} (ht : 0 < t)
    (X : SizedNatFinset t) :
    canonicalFreimanRelationCode (s := s) ht X ∈
      finsetFreimanRelationCodes (s := s) ht X :=
  Finset.min'_mem _ _

lemma canonicalFreimanRelationCode_eq_of_equivalent {s t : ℕ} (ht : 0 < t)
    {X Y : SizedNatFinset t} (hXY : FreimanRelationEquivalent (s := s) X Y) :
    canonicalFreimanRelationCode (s := s) ht X =
      canonicalFreimanRelationCode (s := s) ht Y := by
  letI : LinearOrder (Fin t → FreimanRelationIndex s t) :=
    freimanRelationCodeLinearOrder s t
  unfold canonicalFreimanRelationCode
  apply (Finset.min'_eq_iff
    (s := finsetFreimanRelationCodes (s := s) ht X)
    (H := finsetFreimanRelationCodes_nonempty (s := s) ht X)
    ((finsetFreimanRelationCodes (s := s) ht Y).min'
      (finsetFreimanRelationCodes_nonempty (s := s) ht Y))).mpr
  refine ⟨?_, ?_⟩
  · rw [finsetFreimanRelationCodes_eq_of_equivalent ht hXY]
    exact Finset.min'_mem _ _
  · intro code hcode
    apply Finset.min'_le
    rwa [← finsetFreimanRelationCodes_eq_of_equivalent ht hXY]

lemma card_canonicalFreimanRelationCode_image_of_fixed_extensionBase
    {α : Type*} {l d : ℕ} (hl : 0 < l) (S : Finset α)
    (full : α → SizedNatFinset (l + d)) (label : α → Fin (l + d) → ℕ)
    (hlabelInjective : ∀ x ∈ S, Function.Injective (label x))
    (hlabelRange : ∀ x ∈ S, Set.range (label x) = (full x).1)
    (hbase : ∀ x ∈ S, ∀ y ∈ S, ∀ p : FreimanRelationIndex 4 l,
      freimanRelationHolds (extensionBaseTuple (label x)) p ↔
        freimanRelationHolds (extensionBaseTuple (label y)) p) :
    (S.image fun x ↦ canonicalFreimanRelationCode (s := 2) (by omega : 0 < l + d)
      (full x)).card ≤ (1 + l ^ 4) ^ ((d + 1) ^ 4) := by
  rw [← card_extensionCodeType]
  apply card_image_le_fintype_of_eq_imp_eq S
    (fun x ↦ canonicalFreimanRelationCode (s := 2) (by omega : 0 < l + d) (full x))
    (fun x ↦ extensionCode (label x))
  intro x hx y hy hcode
  have hrelations := freimanRelations_iff_of_extensionCode_eq ⟨0, hl⟩
    (label x) (label y) hcode (hbase x hx y hy)
  have hequivalent := freimanRelationEquivalent_tupleRange
    (hlabelInjective x hx) (hlabelInjective y hy) hrelations
  have hcanonical := canonicalFreimanRelationCode_eq_of_equivalent
    (by omega : 0 < l + d) hequivalent
  have hxRange : tupleRangeSized (label x) (hlabelInjective x hx) = full x := by
    apply Subtype.ext
    apply Finset.coe_injective
    simpa [tupleRangeSized, tupleRange] using hlabelRange x hx
  have hyRange : tupleRangeSized (label y) (hlabelInjective y hy) = full y := by
    apply Subtype.ext
    apply Finset.coe_injective
    simpa [tupleRangeSized, tupleRange] using hlabelRange y hy
  rwa [hxRange, hyRange] at hcanonical

lemma exists_canonicalLabeling {s t : ℕ} (ht : 0 < t)
    (X : SizedNatFinset t) :
    ∃ e : Equiv.Perm (Fin t),
      freimanRelationCode (s := s) ht (permutedFinsetTuple X e) =
        canonicalFreimanRelationCode (s := s) ht X := by
  simpa [finsetFreimanRelationCodes] using
    canonicalFreimanRelationCode_mem (s := s) ht X

private noncomputable def canonicalLabeling {s t : ℕ} (ht : 0 < t)
    (X : SizedNatFinset t) : Equiv.Perm (Fin t) :=
  Classical.choose (exists_canonicalLabeling (s := s) ht X)

private lemma canonicalLabeling_code {s t : ℕ} (ht : 0 < t)
    (X : SizedNatFinset t) :
    freimanRelationCode (s := s) ht
      (permutedFinsetTuple X (canonicalLabeling (s := s) ht X)) =
      canonicalFreimanRelationCode (s := s) ht X :=
  Classical.choose_spec (exists_canonicalLabeling (s := s) ht X)

private lemma canonicalLabelings_relations_iff {s t : ℕ} (ht : 0 < t)
    (X Y : SizedNatFinset t)
    (hcode : canonicalFreimanRelationCode (s := s) ht X =
      canonicalFreimanRelationCode (s := s) ht Y)
    (p : FreimanRelationIndex s t) :
    freimanRelationHolds
        (permutedFinsetTuple X (canonicalLabeling (s := s) ht X)) p ↔
      freimanRelationHolds
        (permutedFinsetTuple Y (canonicalLabeling (s := s) ht Y)) p := by
  refine freimanRelations_iff_of_code_eq ht ?_ p
  rw [canonicalLabeling_code, canonicalLabeling_code, hcode]

private def permutedRestrictedSumRepresentation {l u : ℕ}
    (A B : Finset ℕ) (hA : A.card = l) (hB : B.card = u)
    (hBA : B ⊆ restrictedSumset A) (e : Equiv.Perm (Fin l)) :
    Fin u → Fin l × Fin l :=
  fun i ↦ (e.symm (restrictedSumRepresentation A B hA hB hBA i).1,
    e.symm (restrictedSumRepresentation A B hA hB hBA i).2)

private lemma pairSumTuple_permutedRestrictedSumRepresentation {l u : ℕ}
    (A B : Finset ℕ) (hA : A.card = l) (hB : B.card = u)
    (hBA : B ⊆ restrictedSumset A) (e : Equiv.Perm (Fin l)) :
    pairSumTuple (permutedFinsetTuple ⟨A, hA⟩ e)
        (permutedRestrictedSumRepresentation A B hA hB hBA e) =
      finsetTuple B hB := by
  change pairSumTuple (permutedFinsetTuple ⟨A, hA⟩ e)
      (permutedRestrictedSumRepresentation A B hA hB hBA e) =
    fun i ↦ (B.orderIsoOfFin hB i).1
  rw [← pairSumTuple_restrictedSumRepresentation A B hA hB hBA]
  funext i
  simp [pairSumTuple, permutedFinsetTuple, permutedRestrictedSumRepresentation,
    finsetTuple]

private lemma permutedRestrictedSumRepresentation_ne {l u : ℕ}
    (A B : Finset ℕ) (hA : A.card = l) (hB : B.card = u)
    (hBA : B ⊆ restrictedSumset A) (e : Equiv.Perm (Fin l)) (i : Fin u) :
    (permutedRestrictedSumRepresentation A B hA hB hBA e i).1 ≠
      (permutedRestrictedSumRepresentation A B hA hB hBA e i).2 := by
  unfold permutedRestrictedSumRepresentation
  exact e.symm.injective.ne (restrictedSumRepresentation_ne A B hA hB hBA i)

def extensionFinsetTuple {u d : ℕ} (A A₁ : Finset ℕ)
    (hA₁ : A₁.card = u) (hZ : (A \ A₁).card = d) (e : Equiv.Perm (Fin u)) :
    Fin (u + d) → ℕ :=
  fun i ↦ match finSumFinEquiv.symm i with
  | Sum.inl j => permutedFinsetTuple ⟨A₁, hA₁⟩ e j
  | Sum.inr j => finsetTuple (A \ A₁) hZ j

private lemma extensionFinsetTuple_left {u d : ℕ} (A A₁ : Finset ℕ)
    (hA₁ : A₁.card = u) (hZ : (A \ A₁).card = d) (e : Equiv.Perm (Fin u))
    (i : Fin u) :
    extensionFinsetTuple A A₁ hA₁ hZ e (finSumFinEquiv (Sum.inl i)) =
      permutedFinsetTuple ⟨A₁, hA₁⟩ e i := by
  simp [extensionFinsetTuple]

private lemma extensionFinsetTuple_right {u d : ℕ} (A A₁ : Finset ℕ)
    (hA₁ : A₁.card = u) (hZ : (A \ A₁).card = d) (e : Equiv.Perm (Fin u))
    (i : Fin d) :
    extensionFinsetTuple A A₁ hA₁ hZ e (finSumFinEquiv (Sum.inr i)) =
      finsetTuple (A \ A₁) hZ i := by
  simp [extensionFinsetTuple]

lemma extensionBaseTuple_extensionFinsetTuple {u d : ℕ} (A A₁ : Finset ℕ)
    (hA₁ : A₁.card = u) (hZ : (A \ A₁).card = d) (e : Equiv.Perm (Fin u)) :
    extensionBaseTuple (extensionFinsetTuple A A₁ hA₁ hZ e) =
      permutedFinsetTuple ⟨A₁, hA₁⟩ e := by
  funext i
  simp [extensionBaseTuple, extensionFinsetTuple]

lemma extensionFinsetTuple_injective {u d : ℕ} {A A₁ : Finset ℕ}
    (hA₁ : A₁.card = u) (hZ : (A \ A₁).card = d)
    (e : Equiv.Perm (Fin u)) :
    Function.Injective (extensionFinsetTuple A A₁ hA₁ hZ e) := by
  intro i j hij
  obtain ⟨si, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨sj, rfl⟩ := finSumFinEquiv.surjective j
  obtain i' | i' := si <;> obtain j' | j' := sj
  · exact congrArg finSumFinEquiv (congrArg Sum.inl
      ((permutedFinsetTuple_injective ⟨A₁, hA₁⟩ e) (by
        simpa only [extensionFinsetTuple_left] using hij)))
  · have hleft : permutedFinsetTuple ⟨A₁, hA₁⟩ e i' ∈ A₁ := by
      simp [permutedFinsetTuple, finsetTuple]
    have hright : finsetTuple (A \ A₁) hZ j' ∈ A \ A₁ :=
      ((A \ A₁).orderIsoOfFin hZ j').2
    exact ((Finset.mem_sdiff.mp hright).2
      ((by simpa only [extensionFinsetTuple_left, extensionFinsetTuple_right]
        using hij) ▸ hleft)).elim
  · have hleft : finsetTuple (A \ A₁) hZ i' ∈ A \ A₁ :=
      ((A \ A₁).orderIsoOfFin hZ i').2
    have hright : permutedFinsetTuple ⟨A₁, hA₁⟩ e j' ∈ A₁ := by
      simp [permutedFinsetTuple, finsetTuple]
    exact ((Finset.mem_sdiff.mp hleft).2
      ((by simpa only [extensionFinsetTuple_left, extensionFinsetTuple_right]
        using hij.symm) ▸ hright)).elim
  · exact congrArg finSumFinEquiv (congrArg Sum.inr
      ((finsetTuple_injective (A \ A₁) hZ) (by
        simpa only [extensionFinsetTuple_right] using hij)))

lemma range_extensionFinsetTuple {u d : ℕ} {A A₁ : Finset ℕ}
    (hA₁A : A₁ ⊆ A) (hA₁ : A₁.card = u) (hZ : (A \ A₁).card = d)
    (e : Equiv.Perm (Fin u)) :
    Set.range (extensionFinsetTuple A A₁ hA₁ hZ e) = A := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨si, rfl⟩ := finSumFinEquiv.surjective i
    obtain i | i := si
    · apply hA₁A
      rw [extensionFinsetTuple_left]
      simp [permutedFinsetTuple, finsetTuple]
    · rw [extensionFinsetTuple_right]
      exact (Finset.mem_sdiff.mp ((A \ A₁).orderIsoOfFin hZ i |>.2)).1
  · intro hx
    by_cases hxA₁ : x ∈ A₁
    · have hxRange : x ∈ Set.range (permutedFinsetTuple ⟨A₁, hA₁⟩ e) := by
        rw [range_permutedFinsetTuple]
        exact hxA₁
      obtain ⟨i, hi⟩ := hxRange
      refine ⟨finSumFinEquiv (Sum.inl i), ?_⟩
      rw [extensionFinsetTuple_left]
      exact hi
    · let i := ((A \ A₁).orderIsoOfFin hZ).symm ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxA₁⟩⟩
      refine ⟨finSumFinEquiv (Sum.inr i), ?_⟩
      rw [extensionFinsetTuple_right]
      exact congrArg Subtype.val
        ((A \ A₁).orderIsoOfFin hZ |>.apply_symm_apply
          ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxA₁⟩⟩)

/-- Green's Lemma 36 in the form needed for class counting. A subset of the restricted sumset of
one core transports to an equal-sized subset of the restricted sumset of any core in the same
`8`-relation class, while preserving its unlabeled `4`-relation class. -/
lemma exists_restrictedSumset_subset_equivalent {l u : ℕ}
    (hl : 0 < l) (hu : 0 < u) (A C : SizedNatFinset l) (B : SizedNatFinset u)
    (hBA : B.1 ⊆ restrictedSumset A.1)
    (hcoreCode : canonicalFreimanRelationCode (s := 8) hl A =
      canonicalFreimanRelationCode (s := 8) hl C) :
    ∃ D : SizedNatFinset u, D.1 ⊆ restrictedSumset C.1 ∧
      canonicalFreimanRelationCode (s := 4) hu B =
        canonicalFreimanRelationCode (s := 4) hu D := by
  let eA := canonicalLabeling (s := 8) hl A
  let eC := canonicalLabeling (s := 8) hl C
  let representation := permutedRestrictedSumRepresentation
    A.1 B.1 A.2 B.2 hBA eA
  let a := permutedFinsetTuple A eA
  let c := permutedFinsetTuple C eC
  let d := pairSumTuple c representation
  have haB : pairSumTuple a representation = finsetTuple B.1 B.2 :=
    pairSumTuple_permutedRestrictedSumRepresentation A.1 B.1 A.2 B.2 hBA eA
  have hcore (p : FreimanRelationIndex 8 l) :
      freimanRelationHolds a p ↔ freimanRelationHolds c p :=
    canonicalLabelings_relations_iff hl A C hcoreCode p
  have hrelations (p : FreimanRelationIndex 4 u) :
      freimanRelationHolds (finsetTuple B.1 B.2) p ↔
        freimanRelationHolds d p := by
    rw [← haB]
    exact pairSumTuple_relations_iff hcore representation p
  have hdInjective : Function.Injective d :=
    injective_of_four_relations_iff (finsetTuple_injective B.1 B.2) hrelations
  let D := tupleRangeSized d hdInjective
  refine ⟨D, ?_, ?_⟩
  · change tupleRange d ⊆ restrictedSumset C.1
    have hsubset := pairSumRange_subset_restrictedSumset c
      (permutedFinsetTuple_injective C eC) representation
      (permutedRestrictedSumRepresentation_ne A.1 B.1 A.2 B.2 hBA eA)
    change tupleRange d ⊆ restrictedSumset (Finset.univ.image c) at hsubset
    have hc_range : Finset.univ.image c = C.1 := by
      apply Finset.coe_injective
      simpa [Finset.coe_image] using range_permutedFinsetTuple C eC
    rw [hc_range] at hsubset
    exact hsubset
  · have hequivalent := freimanRelationEquivalent_tupleRange
      (finsetTuple_injective B.1 B.2) hdInjective hrelations
    have hcanonical := canonicalFreimanRelationCode_eq_of_equivalent hu hequivalent
    have hBRange : tupleRangeSized (finsetTuple B.1 B.2)
        (finsetTuple_injective B.1 B.2) = B := by
      apply Subtype.ext
      exact tupleRange_finsetTuple B.1 B.2
    rw [hBRange] at hcanonical
    exact hcanonical

/-- Green's Lemma 12 in the form used below: the canonical `s`-relation identifiers of any
family of `t`-sets have cardinality at most `t^(2*s*t)`. -/
lemma ncard_restrictedSumset_subset_class_image_le {l u : ℕ}
    (hl : 0 < l) (hu : 0 < u) (C : SizedNatFinset l)
    (family : Set (SizedNatFinset u))
    (hfamily : ∀ B ∈ family, ∃ A : SizedNatFinset l,
      B.1 ⊆ restrictedSumset A.1 ∧
        canonicalFreimanRelationCode (s := 8) hl A =
          canonicalFreimanRelationCode (s := 8) hl C) :
    (canonicalFreimanRelationCode (s := 4) hu '' family).ncard ≤
      (restrictedSumset C.1).card.choose u := by
  let subsets := (restrictedSumset C.1).powersetCard u
  let encode : ↑subsets → (Fin u → FreimanRelationIndex 4 u) := fun D ↦
    canonicalFreimanRelationCode (s := 4) hu
      ⟨D.1, (Finset.mem_powersetCard.mp D.2).2⟩
  have hinclusion : canonicalFreimanRelationCode (s := 4) hu '' family ⊆
      Set.range encode := by
    rintro _ ⟨B, hB, rfl⟩
    obtain ⟨A, hBA, hcode⟩ := hfamily B hB
    obtain ⟨D, hDC, hBD⟩ :=
      exists_restrictedSumset_subset_equivalent hl hu A C B hBA hcode
    have hDmem : D.1 ∈ subsets := by
      change D.1 ∈ (restrictedSumset C.1).powersetCard u
      rw [Finset.mem_powersetCard]
      exact ⟨hDC, D.2⟩
    refine ⟨⟨D.1, hDmem⟩, ?_⟩
    exact hBD.symm
  refine (Set.ncard_le_ncard hinclusion (ht := Set.toFinite _)).trans ?_
  rw [← Set.image_univ]
  refine (Set.ncard_image_le (s := Set.univ)).trans_eq ?_
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_coe]
  unfold subsets
  exact Finset.card_powersetCard _ _

private noncomputable def finsetRelationCode {t : ℕ} (ht : 0 < t)
    (X : {X : Finset ℕ // X.card = t}) : Fin t → RelationIndex t :=
  relationCode ht (finsetTuple X X.2)

lemma tuple_freimanIso {t : ℕ} {G H : Type*} [AddCommMonoid G] [AddCommMonoid H]
    {a : Fin t → G} {b : Fin t → H} (ht : 0 < t)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hrelations : ∀ i j k l, a i + a j = a k + a l ↔ b i + b j = b k + b l) :
    ∃ f : G → H, IsAddFreimanIso 2 (Set.range a) (Set.range b) f := by
  classical
  letI : Nonempty (Fin t) := ⟨⟨0, ht⟩⟩
  let f : G → H := fun x ↦ b (Function.invFun a x)
  have hf (i : Fin t) : f (a i) = b i := by
    dsimp only [f]
    rw [Function.leftInverse_invFun ha]
  refine ⟨f, isAddFreimanIso_two.mpr ⟨?_, ?_⟩⟩
  · refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨i, (hf i).symm⟩
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
      rw [hf i, hf j] at hij
      exact congr_arg a (hb hij)
    · rintro _ ⟨i, rfl⟩
      exact ⟨a i, ⟨i, rfl⟩, hf i⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
    rw [hf i, hf j, hf k, hf l]
    exact (hrelations i j k l).symm

private lemma relationModel_injective {t : ℕ} (a : Fin t → ℕ)
    (ha : Function.Injective a) (i₀ : Fin t) :
    Function.Injective (relationModel a i₀) := by
  intro i j hij
  have hadd : relationModel a i₀ i + relationModel a i₀ i₀ =
      relationModel a i₀ j + relationModel a i₀ i₀ := congrArg
    (fun x ↦ x + relationModel a i₀ i₀) hij
  have haij : a i + a i₀ = a j + a i₀ :=
    (relationModel_add_eq_add_iff a i₀ (i, i₀, j, i₀)).mp hadd
  exact ha (Nat.add_right_cancel haij)

private lemma freimanModelDim_relationModel {t : ℕ} (ht : 0 < t)
    (X : {X : Finset ℕ // X.card = t}) :
    freimanModelDim X.1 (relationModelDim (finsetTuple X X.2)) := by
  let a := finsetTuple X X.2
  let i₀ : Fin t := ⟨0, ht⟩
  let b := relationModel a i₀
  obtain ⟨f, hf⟩ := tuple_freimanIso ht (finsetTuple_injective X X.2)
    (relationModel_injective a (finsetTuple_injective X X.2) i₀)
    (fun i j k l ↦ (relationModel_add_eq_add_iff a i₀ (i, j, k, l)).symm)
  have hA : (X.1 : Set ℕ) = Set.range a := by
    exact (range_finsetTuple X X.2).symm
  have hB : (X.1.image f : Set (Fin (relationModelDim a) → ℚ)) = Set.range b := by
    rw [Finset.coe_image, hA]
    exact hf.bijOn.image_eq
  refine ⟨f, ?_, ?_⟩
  · rwa [hA, hB]
  · have htupleRange : X.1.image f = Finset.univ.image b := by
      apply Finset.coe_injective
      rw [hB]
      ext y
      simp
    rw [htupleRange]
    exact relationModel_affineDim a i₀

lemma relationModelDim_le_freimanDim {t : ℕ} (ht : 0 < t)
    (X : {X : Finset ℕ // X.card = t}) :
    relationModelDim (finsetTuple X X.2) ≤ freimanDim X.1 := by
  classical
  unfold freimanDim
  apply Nat.le_findGreatest
  · rw [X.2]
    refine (Nat.le_add_right _
      (Module.finrank ℚ (relationSpace (finsetTuple X X.2)))).trans ?_
    rw [relationModelDim_add_relationRank ht]
    exact Nat.sub_le t 1
  · exact freimanModelDim_relationModel ht X

def coordinateClass {t : ℕ} (a : Fin t → ℕ) (i : Fin t) :
    (Fin t →₀ ℚ) ⧸ relationSpace a :=
  (relationSpace a).mkQ (Finsupp.single i 1)

private lemma finrank_relationQuotient {t : ℕ} (ht : 0 < t) (a : Fin t → ℕ) :
    Module.finrank ℚ ((Fin t →₀ ℚ) ⧸ relationSpace a) = relationModelDim a + 1 := by
  rw [← @add_right_cancel_iff _ _ _ (Module.finrank ℚ (relationSpace a)),
    Submodule.finrank_quotient_add_finrank, Module.finrank_finsupp_self,
    Fintype.card_fin]
  rw [add_assoc, add_comm 1, ← add_assoc, relationModelDim_add_relationRank ht]
  omega

private lemma span_coordinateClass {t : ℕ} (a : Fin t → ℕ) :
    Submodule.span ℚ (Set.range (coordinateClass a)) = ⊤ := by
  have hsingle : Submodule.span ℚ
      (Set.range fun i : Fin t ↦ (Finsupp.single i 1 : Fin t →₀ ℚ)) = ⊤ := by
    apply top_unique
    intro x _
    have hdecompose : x = ∑ i, x i • (Finsupp.single i 1 : Fin t →₀ ℚ) := by
      ext j
      have hcoord : ∑ i, x i * (Finsupp.single i 1 : Fin t →₀ ℚ) j = x j := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro i _ hij
          simp [hij]
        · simp
      rw [Finsupp.finsetSum_apply]
      simpa only [Finsupp.smul_apply, smul_eq_mul] using hcoord.symm
    rw [hdecompose]
    exact Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hrange : Set.range (coordinateClass a) =
      (relationSpace a).mkQ ''
        Set.range (fun i : Fin t ↦ (Finsupp.single i 1 : Fin t →₀ ℚ)) := by
    ext x
    simp [coordinateClass]
  rw [hrange]
  rw [← Submodule.map_span, hsingle, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (relationSpace a).mkQ_surjective

lemma exists_determiningCoordinates {t r : ℕ} (ht : 0 < t) (a : Fin t → ℕ)
    (hdr : relationModelDim a ≤ r) :
    ∃ anchor : Fin (r + 1) → Fin t,
      Submodule.span ℚ (Set.range (coordinateClass a ∘ anchor)) = ⊤ := by
  let d := relationModelDim a
  obtain ⟨basis, hbasis_mem, hbasis_span, -⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range (coordinateClass a))
  have hdomain : Module.finrank ℚ
      (Submodule.span ℚ (Set.range (coordinateClass a))) = d + 1 := by
    rw [span_coordinateClass, finrank_top, finrank_relationQuotient ht]
  let index : Fin (Module.finrank ℚ
      (Submodule.span ℚ (Set.range (coordinateClass a)))) → Fin t :=
    fun i ↦ Classical.choose (hbasis_mem i)
  have hindex (i : Fin (Module.finrank ℚ
      (Submodule.span ℚ (Set.range (coordinateClass a))))) :
      coordinateClass a (index i) = basis i := by
    exact Classical.choose_spec (hbasis_mem i)
  have hrank : Module.finrank ℚ
      (Submodule.span ℚ (Set.range (coordinateClass a))) ≤ r + 1 := by
    rw [hdomain]
    exact Nat.add_le_add_right hdr 1
  let i₀ : Fin t := ⟨0, ht⟩
  let anchor : Fin (r + 1) → Fin t := fun i ↦
    if hi : i.val < Module.finrank ℚ
        (Submodule.span ℚ (Set.range (coordinateClass a))) then
      index ⟨i.val, hi⟩ else i₀
  refine ⟨anchor, ?_⟩
  have hbasis_top : Submodule.span ℚ (Set.range basis) = ⊤ :=
    hbasis_span.trans (span_coordinateClass a)
  apply top_unique
  rw [← hbasis_top]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  let j : Fin (r + 1) := Fin.castLE hrank i
  refine ⟨j, ?_⟩
  change coordinateClass a (anchor j) = basis i
  have hj : j.val < Module.finrank ℚ
      (Submodule.span ℚ (Set.range (coordinateClass a))) := i.isLt
  have hanchor : anchor j = index i := by
    dsimp only [anchor]
    rw [dif_pos hj]
    apply congrArg index
    exact Fin.ext rfl
  rw [hanchor, hindex]

lemma tuple_eq_of_relations_of_determiningCoordinates {t r : ℕ}
    (a b c : Fin t → ℕ) (anchor : Fin (r + 1) → Fin t)
    (hspan : Submodule.span ℚ (Set.range (coordinateClass a ∘ anchor)) = ⊤)
    (hb : ∀ p, relationHolds a p ↔ relationHolds b p)
    (hc : ∀ p, relationHolds a p ↔ relationHolds c p)
    (hanchor : ∀ i, b (anchor i) = c (anchor i)) : b = c := by
  have hbker : relationSpace a ≤ LinearMap.ker (tupleEval b) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    exact (relationVector_mem_ker_iff b p).mpr ((hb p).mp hp)
  have hcker : relationSpace a ≤ LinearMap.ker (tupleEval c) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    exact (relationVector_mem_ker_iff c p).mpr ((hc p).mp hp)
  let fb : ((Fin t →₀ ℚ) ⧸ relationSpace a) →ₗ[ℚ] ℚ :=
    (relationSpace a).liftQ (tupleEval b) hbker
  let fc : ((Fin t →₀ ℚ) ⧸ relationSpace a) →ₗ[ℚ] ℚ :=
    (relationSpace a).liftQ (tupleEval c) hcker
  have hf : fb = fc := by
    apply LinearMap.ext_on hspan
    rintro _ ⟨i, rfl⟩
    dsimp only [Function.comp_apply, coordinateClass, fb, fc]
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, tupleEval,
      Finsupp.linearCombination_single, one_smul]
    exact_mod_cast hanchor i
  funext i
  have hi := LinearMap.congr_fun hf (coordinateClass a i)
  dsimp only [coordinateClass, fb, fc] at hi
  simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, tupleEval,
    Finsupp.linearCombination_single, one_smul] at hi
  exact_mod_cast hi

/-! ### Counting bounded-dimension realizations -/

/-- Sets `X ⊆ [n]` of size `t` and Freiman dimension at most `r`. -/
def boundedFreimanDimSets (n r t : ℕ) : Set (Finset ℕ) :=
  {X : Finset ℕ | X ⊆ interval n ∧ X.card = t ∧ freimanDim X ≤ r}

/-- Sets in `boundedFreimanDimSets` whose self-sumset has cardinality at most `s`. -/
def smallSumsetFreimanDimSets (n r s t : ℕ) : Set (Finset ℕ) :=
  {X : Finset ℕ |
    X ⊆ interval n ∧ X.card = t ∧ freimanDim X ≤ r ∧ (X + X).card ≤ s}

private abbrev BoundedFreimanDimMember (n r t : ℕ) :=
  {X : Finset ℕ // X ∈ boundedFreimanDimSets n r t}

private def boundedFreimanDimMemberSized {n r t : ℕ} (X : BoundedFreimanDimMember n r t) :
    {X : Finset ℕ // X.card = t} :=
  ⟨X.1, X.2.2.1⟩

private def freimanClassCode {n r t : ℕ} (ht : 0 < t) (X : BoundedFreimanDimMember n r t) :
    Fin t → RelationIndex t :=
  finsetRelationCode ht (boundedFreimanDimMemberSized X)

private def HasFreimanClassCode (n r t : ℕ) (ht : 0 < t)
    (code : Fin t → RelationIndex t) : Prop :=
  ∃ X : BoundedFreimanDimMember n r t, freimanClassCode ht X = code

private noncomputable def classRepresentativeTuple (n r t : ℕ) (ht : 0 < t)
    (code : Fin t → RelationIndex t) : Fin t → ℕ := by
  classical
  exact if h : HasFreimanClassCode n r t ht code then
    finsetTuple (boundedFreimanDimMemberSized (Classical.choose h))
      (boundedFreimanDimMemberSized (Classical.choose h)).2
  else fun _ ↦ 0

private lemma classRepresentativeTuple_code {n r t : ℕ} (ht : 0 < t)
    (code : Fin t → RelationIndex t) (hcode : HasFreimanClassCode n r t ht code) :
    relationCode ht (classRepresentativeTuple n r t ht code) = code := by
  classical
  rw [classRepresentativeTuple, dif_pos hcode]
  exact Classical.choose_spec hcode

private lemma classRepresentativeTuple_dim_le {n r t : ℕ} (ht : 0 < t)
    (code : Fin t → RelationIndex t) (hcode : HasFreimanClassCode n r t ht code) :
    relationModelDim (classRepresentativeTuple n r t ht code) ≤ r := by
  classical
  rw [classRepresentativeTuple, dif_pos hcode]
  exact (relationModelDim_le_freimanDim ht
    (boundedFreimanDimMemberSized (Classical.choose hcode))).trans
      (Classical.choose hcode).2.2.2

private noncomputable def classAnchor (n r t : ℕ) (ht : 0 < t)
    (code : Fin t → RelationIndex t) : Fin (r + 1) → Fin t := by
  classical
  exact if h : HasFreimanClassCode n r t ht code then
    Classical.choose (exists_determiningCoordinates ht
      (classRepresentativeTuple n r t ht code)
      (classRepresentativeTuple_dim_le ht code h))
  else fun _ ↦ ⟨0, ht⟩

private lemma classAnchor_span {n r t : ℕ} (ht : 0 < t)
    (code : Fin t → RelationIndex t) (hcode : HasFreimanClassCode n r t ht code) :
    Submodule.span ℚ (Set.range (coordinateClass
      (classRepresentativeTuple n r t ht code) ∘ classAnchor n r t ht code)) = ⊤ := by
  classical
  rw [classAnchor, dif_pos hcode]
  exact Classical.choose_spec (exists_determiningCoordinates ht
    (classRepresentativeTuple n r t ht code)
    (classRepresentativeTuple_dim_le ht code hcode))

private noncomputable def freimanClassEncoding (n r t : ℕ) (ht : 0 < t)
    (X : BoundedFreimanDimMember n r t) :
    (Fin t → RelationIndex t) × (Fin (r + 1) → ↑(interval n)) :=
  (freimanClassCode ht X, fun i ↦
    ⟨finsetTuple (boundedFreimanDimMemberSized X) (boundedFreimanDimMemberSized X).2
        (classAnchor n r t ht (freimanClassCode ht X) i),
      X.2.1 ((X.1.orderIsoOfFin X.2.2.1
        (classAnchor n r t ht (freimanClassCode ht X) i)).2)⟩)

private lemma freimanClassEncoding_injective (n r t : ℕ) (ht : 0 < t) :
    Function.Injective (freimanClassEncoding n r t ht) := by
  classical
  intro X Y hXY
  let code := freimanClassCode ht X
  have hcode : freimanClassCode ht X = freimanClassCode ht Y := congrArg Prod.fst hXY
  have hhas : HasFreimanClassCode n r t ht code := ⟨X, rfl⟩
  have hvalues := congrArg Prod.snd hXY
  change (fun i ↦
      (⟨finsetTuple (boundedFreimanDimMemberSized X) (boundedFreimanDimMemberSized X).2
          (classAnchor n r t ht (freimanClassCode ht X) i),
        X.2.1 ((X.1.orderIsoOfFin X.2.2.1
          (classAnchor n r t ht (freimanClassCode ht X) i)).2)⟩ : ↑(interval n))) =
    (fun i ↦
      (⟨finsetTuple (boundedFreimanDimMemberSized Y) (boundedFreimanDimMemberSized Y).2
          (classAnchor n r t ht (freimanClassCode ht Y) i),
        Y.2.1 ((Y.1.orderIsoOfFin Y.2.2.1
          (classAnchor n r t ht (freimanClassCode ht Y) i)).2)⟩ : ↑(interval n))) at hvalues
  rw [← hcode] at hvalues
  have hanchor (i : Fin (r + 1)) :
      finsetTuple (boundedFreimanDimMemberSized X) (boundedFreimanDimMemberSized X).2
          (classAnchor n r t ht code i) =
        finsetTuple (boundedFreimanDimMemberSized Y) (boundedFreimanDimMemberSized Y).2
          (classAnchor n r t ht code i) := by
    exact congrArg (fun f ↦ (f i).1) hvalues
  have hrepX : relationCode ht (classRepresentativeTuple n r t ht code) =
      relationCode ht
        (finsetTuple (boundedFreimanDimMemberSized X) (boundedFreimanDimMemberSized X).2) := by
    simpa [code, freimanClassCode, finsetRelationCode] using
      classRepresentativeTuple_code ht code hhas
  have hrepY : relationCode ht (classRepresentativeTuple n r t ht code) =
      relationCode ht
        (finsetTuple (boundedFreimanDimMemberSized Y) (boundedFreimanDimMemberSized Y).2) := by
    rw [classRepresentativeTuple_code ht code hhas]
    simpa [code, freimanClassCode, finsetRelationCode] using hcode
  have htuple := tuple_eq_of_relations_of_determiningCoordinates
    (classRepresentativeTuple n r t ht code)
    (finsetTuple (boundedFreimanDimMemberSized X) (boundedFreimanDimMemberSized X).2)
    (finsetTuple (boundedFreimanDimMemberSized Y) (boundedFreimanDimMemberSized Y).2)
    (classAnchor n r t ht code) (classAnchor_span ht code hhas)
    (fun p ↦ relations_iff_of_relationCode_eq ht hrepX p)
    (fun p ↦ relations_iff_of_relationCode_eq ht hrepY p) hanchor
  have hrange := congrArg Set.range htuple
  rw [range_finsetTuple (boundedFreimanDimMemberSized X).1
      (boundedFreimanDimMemberSized X).2,
    range_finsetTuple (boundedFreimanDimMemberSized Y).1
      (boundedFreimanDimMemberSized Y).2] at hrange
  apply Subtype.ext
  exact Finset.coe_injective hrange

private theorem card_boundedFreimanDimSets_nat (n r t : ℕ) (ht : 0 < t) :
    (boundedFreimanDimSets n r t).ncard ≤ n ^ (r + 1) * t ^ (4 * t) := by
  classical
  have hfinite : (boundedFreimanDimSets n r t).Finite := by
    apply (interval n).powerset.finite_toSet.subset
    intro X hX
    rw [Finset.mem_coe, Finset.mem_powerset]
    exact hX.1
  letI : Fintype (BoundedFreimanDimMember n r t) := hfinite.fintype
  have hcard := Fintype.card_le_of_injective (freimanClassEncoding n r t ht)
    (freimanClassEncoding_injective n r t ht)
  rw [Set.fintypeCard_eq_ncard] at hcard
  rw [Fintype.card_prod, card_relation_codes, Fintype.card_fun,
    Fintype.card_coe] at hcard
  simpa [interval, mul_comm] using hcard

/-- Green's relation-class bound for `t`-subsets of the integer interval `[1,n]`. -/
theorem card_boundedFreimanDimSets (n r t : ℕ) (ht : 0 < t) :
    ((boundedFreimanDimSets n r t).ncard : ℝ) ≤
      (n : ℝ) ^ (r + 1) * (t : ℝ) ^ (4 * t) := by
  exact_mod_cast card_boundedFreimanDimSets_nat n r t ht

end

end DenseSetsWithoutLargeSumsets
