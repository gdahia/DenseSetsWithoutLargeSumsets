/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.BipartiteFreimanDimension
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.FreimanIsomorphismClasses.DimensionAndCounting

/-!
# Counting pairs using bipartite Freiman dimension

This file encodes the cross-relations of a labeled pair by at most `2 * k` relations and then
uses determining coordinates in its bipartite Freiman-homomorphism space.
-/

namespace DenseSetsWithoutLargeSumsets

open scoped BigOperators Pointwise

noncomputable section

/-- An equality between two entries of a `k` by `k` cross-addition table. -/
abbrev BipartiteRelationIndex (k : ℕ) := (Fin k × Fin k) × (Fin k × Fin k)

/-- The coefficient vector of a cross-relation. -/
private def bipartiteRelationVector {k : ℕ} (p : BipartiteRelationIndex k) :
    Sum (Fin k) (Fin k) →₀ ℝ :=
  Finsupp.single (Sum.inl p.1.1) 1 + Finsupp.single (Sum.inr p.1.2) 1 -
    Finsupp.single (Sum.inl p.2.1) 1 - Finsupp.single (Sum.inr p.2.2) 1

/-- Whether a labeled pair satisfies a cross-relation. -/
def bipartiteRelationHolds {k : ℕ} (a b : Fin k → ℕ)
    (p : BipartiteRelationIndex k) : Prop :=
  a p.1.1 + b p.1.2 = a p.2.1 + b p.2.2

/-- The real span of all cross-relations satisfied by a labeled pair. -/
private def bipartiteRelationSpace {k : ℕ} (a b : Fin k → ℕ) :
    Submodule ℝ (Sum (Fin k) (Fin k) →₀ ℝ) :=
  Submodule.span ℝ (bipartiteRelationVector ''
    {p : BipartiteRelationIndex k | bipartiteRelationHolds a b p})

private def bipartiteTupleEval {k : ℕ} (a b : Fin k → ℕ) :
    (Sum (Fin k) (Fin k) →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (Sum.elim (fun i ↦ (a i : ℝ)) (fun j ↦ (b j : ℝ)))

private lemma bipartiteTupleEval_relationVector {k : ℕ} (a b : Fin k → ℕ)
    (p : BipartiteRelationIndex k) :
    bipartiteTupleEval a b (bipartiteRelationVector p) =
      (a p.1.1 : ℝ) + b p.1.2 - a p.2.1 - b p.2.2 := by
  simp [bipartiteTupleEval, bipartiteRelationVector]

private lemma bipartiteRelationVector_mem_ker_iff {k : ℕ} (a b : Fin k → ℕ)
    (p : BipartiteRelationIndex k) :
    bipartiteRelationVector p ∈ LinearMap.ker (bipartiteTupleEval a b) ↔
      bipartiteRelationHolds a b p := by
  rw [LinearMap.mem_ker, bipartiteTupleEval_relationVector]
  unfold bipartiteRelationHolds
  constructor
  · intro h
    exact_mod_cast (by linarith :
      (a p.1.1 : ℝ) + b p.1.2 = a p.2.1 + b p.2.2)
  · intro h
    have h' : (a p.1.1 : ℝ) + b p.1.2 = a p.2.1 + b p.2.2 := by
      exact_mod_cast h
    linarith

private lemma bipartiteRelation_iff_mem_space {k : ℕ} (a b : Fin k → ℕ)
    (p : BipartiteRelationIndex k) :
    bipartiteRelationHolds a b p ↔ bipartiteRelationVector p ∈ bipartiteRelationSpace a b := by
  constructor
  · intro hp
    exact Submodule.subset_span ⟨p, hp, rfl⟩
  · intro hp
    rw [← bipartiteRelationVector_mem_ker_iff]
    exact (Submodule.span_le.mpr fun _ h ↦ by
      obtain ⟨q, hq, rfl⟩ := h
      exact (bipartiteRelationVector_mem_ker_iff a b q).mpr hq) hp

private lemma finrank_bipartiteRelationSpace_le {k : ℕ} (a b : Fin k → ℕ) :
    Module.finrank ℝ (bipartiteRelationSpace a b) ≤ 2 * k := by
  apply (bipartiteRelationSpace a b).finrank_le.trans_eq
  simp
  omega

/-- At most `2k` cross-relations span all cross-relations of a labeled pair. -/
private lemma exists_bipartiteRelationCode {k : ℕ} (hk : 0 < k) (a b : Fin k → ℕ) :
    ∃ code : Fin (2 * k) → BipartiteRelationIndex k,
      Submodule.span ℝ (bipartiteRelationVector '' Set.range code) =
        bipartiteRelationSpace a b := by
  let relations : Set (Sum (Fin k) (Fin k) →₀ ℝ) := bipartiteRelationVector ''
    {p | bipartiteRelationHolds a b p}
  obtain ⟨basis, hbasis_mem, hbasis_span, -⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ relations
  let d := Module.finrank ℝ (Submodule.span ℝ relations)
  have hd : d ≤ 2 * k := by
    change Module.finrank ℝ (bipartiteRelationSpace a b) ≤ 2 * k
    exact finrank_bipartiteRelationSpace_le a b
  let index : Fin d → BipartiteRelationIndex k := fun i ↦ Classical.choose (hbasis_mem i)
  have hindex (i : Fin d) : bipartiteRelationVector (index i) = basis i :=
    (Classical.choose_spec (hbasis_mem i)).2
  let i₀ : Fin k := ⟨0, hk⟩
  let zeroIndex : BipartiteRelationIndex k := ((i₀, i₀), (i₀, i₀))
  have hzero : bipartiteRelationVector zeroIndex = 0 := by
    dsimp [zeroIndex, bipartiteRelationVector]
    abel
  let code : Fin (2 * k) → BipartiteRelationIndex k := fun i ↦
    if hi : i.val < d then index ⟨i.val, hi⟩ else zeroIndex
  refine ⟨code, ?_⟩
  change Submodule.span ℝ (bipartiteRelationVector '' Set.range code) =
    Submodule.span ℝ relations
  rw [← hbasis_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    by_cases hi : i.val < d
    · rw [show code i = index ⟨i.val, hi⟩ by simp [code, hi], hindex]
      exact Submodule.subset_span ⟨⟨i.val, hi⟩, rfl⟩
    · rw [show code i = zeroIndex by simp [code, hi], hzero]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    let j : Fin (2 * k) := ⟨i.val, lt_of_lt_of_le i.isLt hd⟩
    rw [← hindex]
    apply Submodule.subset_span
    refine ⟨index i, ⟨j, ?_⟩, rfl⟩
    have hj : j.val < d := i.isLt
    simp only [code, dite_eq_left hj]
    congr

private noncomputable def bipartiteRelationCode {k : ℕ} (hk : 0 < k)
    (a b : Fin k → ℕ) : Fin (2 * k) → BipartiteRelationIndex k :=
  Classical.choose (exists_bipartiteRelationCode hk a b)

private lemma bipartiteRelationCode_span {k : ℕ} (hk : 0 < k) (a b : Fin k → ℕ) :
    Submodule.span ℝ (bipartiteRelationVector '' Set.range
      (bipartiteRelationCode hk a b)) = bipartiteRelationSpace a b :=
  Classical.choose_spec (exists_bipartiteRelationCode hk a b)

private lemma bipartiteRelations_iff_of_code_eq {k : ℕ} (hk : 0 < k)
    {a b a' b' : Fin k → ℕ}
    (hcode : bipartiteRelationCode hk a b = bipartiteRelationCode hk a' b')
    (p : BipartiteRelationIndex k) :
    bipartiteRelationHolds a b p ↔ bipartiteRelationHolds a' b' p := by
  rw [bipartiteRelation_iff_mem_space, bipartiteRelation_iff_mem_space,
    ← bipartiteRelationCode_span hk a b, ← bipartiteRelationCode_span hk a' b', hcode]

lemma card_bipartiteRelationCodes (k : ℕ) :
    Fintype.card (Fin (2 * k) → BipartiteRelationIndex k) = k ^ (8 * k) := by
  simp only [BipartiteRelationIndex, Fintype.card_fun, Fintype.card_prod,
    Fintype.card_fin]
  calc
    (k * k * (k * k)) ^ (2 * k) = (k ^ 4) ^ (2 * k) := by ring
    _ = k ^ (4 * (2 * k)) := (pow_mul k 4 (2 * k)).symm
    _ = k ^ (8 * k) := by ring

/-! ### Determining coordinates -/

private def bipartiteCoordinateEval (A B : Finset ℝ) :
    Sum A B → Module.Dual ℝ (bipartiteFreimanHom A B)
  | Sum.inl a => bipartiteEvalLeft A B a
  | Sum.inr b => bipartiteEvalRight A B b

private lemma span_bipartiteCoordinateEval (A B : Finset ℝ) :
    Submodule.span ℝ (Set.range (bipartiteCoordinateEval A B)) = ⊤ := by
  let W := Submodule.span ℝ (Set.range (bipartiteCoordinateEval A B))
  have hcoann : W.dualCoannihilator = ⊥ := by
    ext f
    constructor
    · intro hf
      rw [Submodule.mem_dualCoannihilator] at hf
      rw [Submodule.mem_bot]
      apply Subtype.ext
      apply Prod.ext
      · funext a
        have heval : bipartiteCoordinateEval A B (Sum.inl a) ∈ W :=
          Submodule.subset_span (Set.mem_range_self (Sum.inl a))
        have := hf _ heval
        change f.1.1 a = 0
        change f.1.1 a = 0 at this
        exact this
      · funext b
        have heval : bipartiteCoordinateEval A B (Sum.inr b) ∈ W :=
          Submodule.subset_span (Set.mem_range_self (Sum.inr b))
        have := hf _ heval
        change f.1.2 b = 0
        change f.1.2 b = 0 at this
        exact this
    · rintro rfl
      exact Submodule.zero_mem _
  apply Submodule.eq_top_of_finrank_eq
  change Module.finrank ℝ W = Module.finrank ℝ (Module.Dual ℝ (bipartiteFreimanHom A B))
  have hfin := Subspace.finrank_add_finrank_dualCoannihilator_eq W
  rw [hcoann, finrank_bot, add_zero] at hfin
  exact hfin.trans Subspace.dual_finrank_eq.symm

private lemma exists_bipartiteDeterminingCoordinates (A B : Finset ℝ) :
    ∃ anchor : Fin (bipartiteFreimanHomDim A B) → Sum A B,
      Submodule.span ℝ (Set.range (bipartiteCoordinateEval A B ∘ anchor)) = ⊤ := by
  let coordinates := Set.range (bipartiteCoordinateEval A B)
  obtain ⟨basis, hbasis_mem, hbasis_span, -⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ coordinates
  have hrank : Module.finrank ℝ (Submodule.span ℝ coordinates) =
      bipartiteFreimanHomDim A B := by
    rw [span_bipartiteCoordinateEval, finrank_top]
    exact Subspace.dual_finrank_eq
  let index : Fin (Module.finrank ℝ (Submodule.span ℝ coordinates)) → Sum A B :=
    fun i ↦ Classical.choose (hbasis_mem i)
  have hindex (i) : bipartiteCoordinateEval A B (index i) = basis i :=
    Classical.choose_spec (hbasis_mem i)
  let anchor : Fin (bipartiteFreimanHomDim A B) → Sum A B :=
    fun i ↦ index (Fin.cast hrank.symm i)
  refine ⟨anchor, ?_⟩
  rw [← span_bipartiteCoordinateEval A B, ← hbasis_span]
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨Fin.cast hrank.symm i, by simp [anchor, Function.comp_apply, hindex]⟩
  · apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    let j : Fin (bipartiteFreimanHomDim A B) := Fin.cast hrank i
    refine ⟨j, ?_⟩
    simp [anchor, j, Function.comp_apply, hindex]

private noncomputable def bipartiteDeterminingCoordinates (A B : Finset ℝ) :
    Fin (bipartiteFreimanHomDim A B) → Sum A B :=
  Classical.choose (exists_bipartiteDeterminingCoordinates A B)

private lemma bipartiteDeterminingCoordinates_span (A B : Finset ℝ) :
    Submodule.span ℝ (Set.range (bipartiteCoordinateEval A B ∘
      bipartiteDeterminingCoordinates A B)) = ⊤ :=
  Classical.choose_spec (exists_bipartiteDeterminingCoordinates A B)

private lemma bipartiteHom_ext_of_determiningCoordinates (A B : Finset ℝ)
    (f g : bipartiteFreimanHom A B)
    (h : ∀ i, bipartiteCoordinateEval A B (bipartiteDeterminingCoordinates A B i) f =
      bipartiteCoordinateEval A B (bipartiteDeterminingCoordinates A B i) g) :
    f = g := by
  let annihilated : Submodule ℝ (Module.Dual ℝ (bipartiteFreimanHom A B)) :=
    LinearMap.ker (Module.Dual.eval ℝ (bipartiteFreimanHom A B) (f - g))
  have hspan : Submodule.span ℝ (Set.range (bipartiteCoordinateEval A B ∘
      bipartiteDeterminingCoordinates A B)) ≤ annihilated := by
    apply Submodule.span_le.mpr
    rintro φ ⟨i, rfl⟩
    change (bipartiteCoordinateEval A B ∘ bipartiteDeterminingCoordinates A B) i ∈
      LinearMap.ker (Module.Dual.eval ℝ (bipartiteFreimanHom A B) (f - g))
    rw [LinearMap.mem_ker]
    simpa [annihilated, Function.comp_apply] using sub_eq_zero.mpr (h i)
  rw [bipartiteDeterminingCoordinates_span] at hspan
  have hall (φ : Module.Dual ℝ (bipartiteFreimanHom A B)) : φ f = φ g := by
    have hφ : φ ∈ annihilated := hspan (Submodule.mem_top)
    rw [LinearMap.mem_ker] at hφ
    have hzero : φ f - φ g = 0 := by simpa [annihilated] using hφ
    exact sub_eq_zero.mp hzero
  apply Subtype.ext
  apply Prod.ext
  · funext a
    exact hall (bipartiteEvalLeft A B a)
  · funext b
    exact hall (bipartiteEvalRight A B b)

/-! ### Encoding bounded-sumset pairs -/

/-- Ordered pairs of `k`-sets in `[n]` whose mixed sumset has cardinality at most `m`. -/
def boundedBipartiteSumsetPairs (n k m : ℕ) : Set (Finset ℕ × Finset ℕ) :=
  {P | P.1 ⊆ interval n ∧ P.2 ⊆ interval n ∧
    P.1.card = k ∧ P.2.card = k ∧ (P.1 + P.2).card ≤ m}

private abbrev BoundedBipartitePair (n k m : ℕ) :=
  {P : Finset ℕ × Finset ℕ // P ∈ boundedBipartiteSumsetPairs n k m}

private def boundedPairLeftTuple {n k m : ℕ} (P : BoundedBipartitePair n k m) :
    Fin k → ℕ := finsetTuple P.1.1 P.2.2.2.1

private def boundedPairRightTuple {n k m : ℕ} (P : BoundedBipartitePair n k m) :
    Fin k → ℕ := finsetTuple P.1.2 P.2.2.2.2.1

private def boundedPairCode {n k m : ℕ} (hk : 0 < k) (P : BoundedBipartitePair n k m) :
    Fin (2 * k) → BipartiteRelationIndex k :=
  bipartiteRelationCode hk (boundedPairLeftTuple P) (boundedPairRightTuple P)

private def HasBoundedPairCode (n k m : ℕ) (hk : 0 < k)
    (code : Fin (2 * k) → BipartiteRelationIndex k) : Prop :=
  ∃ P : BoundedBipartitePair n k m, boundedPairCode hk P = code

private noncomputable def boundedPairRepresentativeLeftTuple (n k m : ℕ) (hk : 0 < k)
    (code : Fin (2 * k) → BipartiteRelationIndex k) : Fin k → ℕ := by
  classical
  exact if h : HasBoundedPairCode n k m hk code then
    boundedPairLeftTuple (Classical.choose h) else fun _ ↦ 0

private noncomputable def boundedPairRepresentativeRightTuple (n k m : ℕ) (hk : 0 < k)
    (code : Fin (2 * k) → BipartiteRelationIndex k) : Fin k → ℕ := by
  classical
  exact if h : HasBoundedPairCode n k m hk code then
    boundedPairRightTuple (Classical.choose h) else fun _ ↦ 0

private lemma boundedPairRepresentative_code {n k m : ℕ} (hk : 0 < k)
    (code : Fin (2 * k) → BipartiteRelationIndex k)
    (hcode : HasBoundedPairCode n k m hk code) :
    bipartiteRelationCode hk (boundedPairRepresentativeLeftTuple n k m hk code)
      (boundedPairRepresentativeRightTuple n k m hk code) = code := by
  rw [boundedPairRepresentativeLeftTuple, boundedPairRepresentativeRightTuple,
    dite_eq_left hcode, dite_eq_left hcode]
  exact Classical.choose_spec hcode

private def tupleRealImage {k : ℕ} (a : Fin k → ℕ) : Finset ℝ := by
  classical
  exact Finset.univ.image (fun i ↦ (a i : ℝ))

private lemma card_tupleRealImage {k : ℕ} {a : Fin k → ℕ} (ha : Function.Injective a) :
    (tupleRealImage a).card = k := by
  classical
  rw [tupleRealImage, Finset.card_image_of_injective]
  · simp
  · intro i j hij
    apply ha
    have hij' : (a i : ℝ) = (a j : ℝ) := hij
    exact_mod_cast hij'

private def tupleRealEquiv {k : ℕ} (a : Fin k → ℕ) (ha : Function.Injective a) :
    Fin k ≃ tupleRealImage a := by
  classical
  apply Equiv.ofBijective (fun i ↦ ⟨(a i : ℝ), by
    rw [tupleRealImage, Finset.mem_image]
    exact ⟨i, Finset.mem_univ _, rfl⟩⟩)
  constructor
  · intro i j hij
    apply ha
    have hij' : (a i : ℝ) = (a j : ℝ) := congrArg Subtype.val hij
    exact_mod_cast hij'
  · rintro ⟨x, hx⟩
    change x ∈ Finset.univ.image (fun i ↦ (a i : ℝ)) at hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, _, hi⟩ := hx
    exact ⟨i, Subtype.ext hi⟩

private lemma tupleRealEquiv_coe {k : ℕ} (a : Fin k → ℕ) (ha : Function.Injective a)
    (i : Fin k) : ((tupleRealEquiv a ha i : tupleRealImage a) : ℝ) = a i := rfl

private def representativeLeftReal (n k m : ℕ) (hk : 0 < k)
    (code : Fin (2 * k) → BipartiteRelationIndex k) : Finset ℝ :=
  tupleRealImage (boundedPairRepresentativeLeftTuple n k m hk code)

private def representativeRightReal (n k m : ℕ) (hk : 0 < k)
    (code : Fin (2 * k) → BipartiteRelationIndex k) : Finset ℝ :=
  tupleRealImage (boundedPairRepresentativeRightTuple n k m hk code)

private lemma card_add_tupleRealImage {k : ℕ} (a b : Fin k → ℕ) :
    (tupleRealImage a + tupleRealImage b).card =
      (Finset.univ.image fun p : Fin k × Fin k ↦ a p.1 + b p.2).card := by
  classical
  let P : Finset (Fin k × Fin k) := Finset.univ
  let f : Fin k × Fin k → ℕ := fun p ↦ a p.1 + b p.2
  let g : Fin k × Fin k → ℝ := fun p ↦ (a p.1 : ℝ) + b p.2
  have hsum : tupleRealImage a + tupleRealImage b = P.image g := by
    ext x
    simp only [tupleRealImage, Finset.mem_add, Finset.mem_image, Finset.mem_univ,
      true_and, P, g]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
      exact ⟨(i, j), rfl⟩
    · rintro ⟨⟨i, j⟩, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
  rw [hsum]
  apply card_image_eq_of_kernel_iff
  intro x _ y _
  dsimp [g, f]
  exact_mod_cast Iff.rfl

private lemma card_pair_add_eq_tableImage {n k m : ℕ} (P : BoundedBipartitePair n k m) :
    (P.1.1 + P.1.2).card =
      (Finset.univ.image fun p : Fin k × Fin k ↦
        boundedPairLeftTuple P p.1 + boundedPairRightTuple P p.2).card := by
  classical
  let pairs : Finset (P.1.1 × P.1.2) := Finset.univ
  let ep : Fin k × Fin k ≃ P.1.1 × P.1.2 :=
    (P.1.1.orderIsoOfFin P.2.2.2.1).toEquiv.prodCongr
      (P.1.2.orderIsoOfFin P.2.2.2.2.1).toEquiv
  have himage : (Finset.univ.image fun p : Fin k × Fin k ↦
      boundedPairLeftTuple P p.1 + boundedPairRightTuple P p.2) =
      pairs.image (fun p ↦ (p.1 : ℕ) + p.2) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, pairs]
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨ep p, by simp [ep, boundedPairLeftTuple, boundedPairRightTuple, finsetTuple]⟩
    · rintro ⟨p, rfl⟩
      refine ⟨ep.symm p, ?_⟩
      simp [ep, boundedPairLeftTuple, boundedPairRightTuple, finsetTuple]
  rw [himage]
  have horig : P.1.1 + P.1.2 = pairs.image (fun p ↦ (p.1 : ℕ) + p.2) := by
    ext x
    simp only [Finset.mem_add, Finset.mem_image, Finset.mem_univ, true_and, pairs]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩
  rw [horig]

private lemma representativeTuples_injective {n k m : ℕ} (hk : 0 < k)
    (code : Fin (2 * k) → BipartiteRelationIndex k)
    (hcode : HasBoundedPairCode n k m hk code) :
    Function.Injective (boundedPairRepresentativeLeftTuple n k m hk code) ∧
      Function.Injective (boundedPairRepresentativeRightTuple n k m hk code) := by
  rw [boundedPairRepresentativeLeftTuple, boundedPairRepresentativeRightTuple,
    dite_eq_left hcode, dite_eq_left hcode]
  exact ⟨finsetTuple_injective _ _, finsetTuple_injective _ _⟩

private lemma representativeHomDim_le {n k m : ℕ} (hk : 0 < k)
    (code : Fin (2 * k) → BipartiteRelationIndex k)
    (hcode : HasBoundedPairCode n k m hk code) :
    bipartiteFreimanHomDim (representativeLeftReal n k m hk code)
      (representativeRightReal n k m hk code) ≤ 2 * m / k := by
  let a := boundedPairRepresentativeLeftTuple n k m hk code
  let b := boundedPairRepresentativeRightTuple n k m hk code
  have hinj := representativeTuples_injective hk code hcode
  have hleft : (representativeLeftReal n k m hk code).card = k :=
    card_tupleRealImage hinj.1
  have hright : (representativeRightReal n k m hk code).card = k :=
    card_tupleRealImage hinj.2
  have hnonleft : (representativeLeftReal n k m hk code).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hnonright : (representativeRightReal n k m hk code).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hdim := bipartiteFreimanHomDim_mul_card_le_two_mul_card_add
    (representativeLeftReal n k m hk code) (representativeRightReal n k m hk code)
    hnonleft hnonright (hleft.trans hright.symm)
  have hsum : (representativeLeftReal n k m hk code +
      representativeRightReal n k m hk code).card ≤ m := by
    rw [representativeLeftReal, representativeRightReal, card_add_tupleRealImage]
    rw [boundedPairRepresentativeLeftTuple, boundedPairRepresentativeRightTuple,
      dite_eq_left hcode, dite_eq_left hcode, ← card_pair_add_eq_tableImage]
    exact (Classical.choose hcode).2.2.2.2.2
  rw [hleft] at hdim
  apply (Nat.le_div_iff_mul_le hk).2
  rw [mul_comm]
  exact hdim.trans (Nat.mul_le_mul_left 2 hsum)

private def realAnchorToIndex {k : ℕ} {a b : Fin k → ℕ}
    (ha : Function.Injective a) (hb : Function.Injective b)
    (x : Sum (tupleRealImage a) (tupleRealImage b)) : Sum (Fin k) (Fin k) :=
  match x with
  | Sum.inl x => Sum.inl ((tupleRealEquiv a ha).symm x)
  | Sum.inr y => Sum.inr ((tupleRealEquiv b hb).symm y)

private noncomputable def boundedPairAnchor (n k m : ℕ) (hk : 0 < k)
    (code : Fin (2 * k) → BipartiteRelationIndex k) :
    Fin (2 * m / k) → Sum (Fin k) (Fin k) := by
  classical
  exact if hcode : HasBoundedPairCode n k m hk code then
    let a := boundedPairRepresentativeLeftTuple n k m hk code
    let b := boundedPairRepresentativeRightTuple n k m hk code
    let hinj := representativeTuples_injective hk code hcode
    let q := bipartiteFreimanHomDim (tupleRealImage a) (tupleRealImage b)
    let anchor := bipartiteDeterminingCoordinates (tupleRealImage a) (tupleRealImage b)
    fun i ↦ if hi : i.val < q then
      realAnchorToIndex hinj.1 hinj.2 (anchor ⟨i.val, hi⟩)
    else Sum.inl ⟨0, hk⟩
  else fun _ ↦ Sum.inl ⟨0, hk⟩

private lemma boundedPairAnchor_castLE {n k m : ℕ} (hk : 0 < k)
    (code : Fin (2 * k) → BipartiteRelationIndex k)
    (hcode : HasBoundedPairCode n k m hk code)
    (i : Fin (bipartiteFreimanHomDim
      (tupleRealImage (boundedPairRepresentativeLeftTuple n k m hk code))
      (tupleRealImage (boundedPairRepresentativeRightTuple n k m hk code)))) :
    boundedPairAnchor n k m hk code
        (Fin.castLE (representativeHomDim_le hk code hcode) i) =
      realAnchorToIndex (representativeTuples_injective hk code hcode).1
        (representativeTuples_injective hk code hcode).2
        (bipartiteDeterminingCoordinates
          (tupleRealImage (boundedPairRepresentativeLeftTuple n k m hk code))
          (tupleRealImage (boundedPairRepresentativeRightTuple n k m hk code)) i) := by
  classical
  rw [boundedPairAnchor, dite_eq_left hcode]
  have hi : (Fin.castLE (representativeHomDim_le hk code hcode) i).val <
      bipartiteFreimanHomDim
        (tupleRealImage (boundedPairRepresentativeLeftTuple n k m hk code))
        (tupleRealImage (boundedPairRepresentativeRightTuple n k m hk code)) := i.isLt
  rw [dite_eq_left hi]

private def tupleValueAtIndex {k : ℕ} (a b : Fin k → ℕ) :
    Sum (Fin k) (Fin k) → ℕ
  | Sum.inl i => a i
  | Sum.inr j => b j

private lemma boundedPairTuple_mem_interval {n k m : ℕ} (P : BoundedBipartitePair n k m)
    (i : Sum (Fin k) (Fin k)) :
    tupleValueAtIndex (boundedPairLeftTuple P) (boundedPairRightTuple P) i ∈ interval n := by
  rcases i with i | i
  · exact P.2.1 ((P.1.1.orderIsoOfFin P.2.2.2.1 i).2)
  · exact P.2.2.1 ((P.1.2.orderIsoOfFin P.2.2.2.2.1 i).2)

private def boundedPairEncoding (n k m : ℕ) (hk : 0 < k)
    (P : BoundedBipartitePair n k m) :
    (Fin (2 * k) → BipartiteRelationIndex k) × (Fin (2 * m / k) → interval n) :=
  let code := boundedPairCode hk P
  (code, fun i ↦
    ⟨tupleValueAtIndex (boundedPairLeftTuple P) (boundedPairRightTuple P)
      (boundedPairAnchor n k m hk code i),
      boundedPairTuple_mem_interval P _⟩)

end

end DenseSetsWithoutLargeSumsets
