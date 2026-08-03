/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.FreimanIsomorphismClasses.RelationAndExtensionCodes

/-!
# Freiman dimension and bounded-dimension classes

This submodule develops relation models, passes from labeled tuples to finite-set classes, and
counts bounded-dimension realizations.
-/

namespace DenseSetsWithoutLargeSumsets

open scoped Pointwise

noncomputable section

/-! ### Freiman dimension and determining coordinates -/

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
  apply (relationSpace a).finrank_le.trans_eq
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
  use code
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
  constructor
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
  apply (Set.ncard_le_ncard hinclusion (ht := Set.toFinite _)).trans
  rw [← Set.image_univ]
  apply (Set.ncard_image_le (s := Set.univ)).trans_eq
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
    apply (Nat.le_add_right _
      (Module.finrank ℚ (relationSpace (finsetTuple X X.2)))).trans
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
