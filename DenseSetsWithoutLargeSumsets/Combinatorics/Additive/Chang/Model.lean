/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.FreimanDimension
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.Chang.Lattice

/-! # The full-rank Freiman model of a 2-proper GAP's subset

This file constructs the full-dimensional rational Freiman model used in Appendix A of
Campos–Dahia–Marciano. Given a 2-proper GAP `P` in an abelian group and a finite set `X` contained
in its carrier, the coordinate map of `P`, followed by a translation, the saturated-lattice basis
coordinates, and the rational cast, is a Freiman 2-isomorphism from `X` onto a full-dimensional
subset of `ℚ^r`, where `r` is the dimension of the real span of the translated coordinate set.
Consequently `r ≤ freimanDim X`.
-/

namespace DenseSetsWithoutLargeSumsets

open scoped Pointwise

noncomputable section

variable {d : ℕ} (S : Finset (Fin d → ℤ))

/-- The lattice domain associated with a finite set of integer vectors: the integer vectors lying
in the real span of `S`. -/
def latticeDomain : Set (Fin d → ℤ) :=
  {y | intVectorToReal y ∈ integerGeneratedSubspace S}

lemma add_mem_latticeDomain {a b : Fin d → ℤ}
    (ha : a ∈ latticeDomain S) (hb : b ∈ latticeDomain S) :
    a + b ∈ latticeDomain S := by
  change intVectorToReal (a + b) ∈ integerGeneratedSubspace S
  rw [intVectorToReal_add]
  exact (integerGeneratedSubspace S).add_mem ha hb

/-- The embedding of the lattice domain into the saturated lattice of the span. -/
noncomputable def latticeEmbed :
    latticeDomain S → subspaceIntegerLattice (integerGeneratedSubspace S) :=
  fun y ↦ ⟨⟨intVectorToReal y.1, y.2⟩, intVectorToReal_mem_standardIntegerLattice y.1⟩

lemma latticeEmbed_injective : Function.Injective (latticeEmbed S) := by
  intro a b h
  apply Subtype.ext
  apply intVectorToReal_injective
  exact congr_arg (fun x ↦ x.1.1) h

lemma latticeEmbed_add (a b : latticeDomain S) :
    latticeEmbed S ⟨a.1 + b.1, add_mem_latticeDomain S a.2 b.2⟩ =
      latticeEmbed S a + latticeEmbed S b := by
  apply Subtype.ext
  apply Subtype.ext
  exact intVectorToReal_add a.1 b.1

/-- The model map on the lattice domain: integer-lattice coordinates followed by the rational
cast. -/
noncomputable def modelMapOnLattice :
    latticeDomain S →
      (Fin (Module.finrank ℝ (integerGeneratedSubspace S)) → ℚ) :=
  fun y ↦ ratCoordHom (integerGeneratedLatticeCoordHom S (latticeEmbed S y))

lemma modelMapOnLattice_injective : Function.Injective (modelMapOnLattice S) := by
  intro a b h
  apply latticeEmbed_injective S
  apply integerGeneratedLatticeCoordHom_injective S
  apply ratCoordHom_injective
  exact h

lemma modelMapOnLattice_add (a b : latticeDomain S) :
    modelMapOnLattice S ⟨a.1 + b.1, add_mem_latticeDomain S a.2 b.2⟩ =
      modelMapOnLattice S a + modelMapOnLattice S b := by
  unfold modelMapOnLattice
  rw [latticeEmbed_add]
  ext i
  simp only [map_add, Pi.add_apply]

open Classical in
/-- The model map as a total function on integer vectors. It agrees with `modelMapOnLattice` on
the lattice domain. -/
noncomputable def latticeModelMap (y : Fin d → ℤ) :
    Fin (Module.finrank ℝ (integerGeneratedSubspace S)) → ℚ :=
  if hy : y ∈ latticeDomain S then
    modelMapOnLattice S ⟨y, hy⟩
  else 0

lemma latticeModelMap_eq_on {y : Fin d → ℤ} (hy : y ∈ latticeDomain S) :
    latticeModelMap S y = modelMapOnLattice S ⟨y, hy⟩ := by
  unfold latticeModelMap
  rw [dite_eq_left hy]

lemma latticeModelMap_injective_on :
    Set.InjOn (latticeModelMap S) (latticeDomain S) := by
  intro a ha b hb h
  rw [latticeModelMap_eq_on S ha, latticeModelMap_eq_on S hb] at h
  exact congr_arg Subtype.val (modelMapOnLattice_injective S h)

lemma latticeModelMap_add_on {a b : Fin d → ℤ}
    (ha : a ∈ latticeDomain S) (hb : b ∈ latticeDomain S) :
    latticeModelMap S (a + b) = latticeModelMap S a + latticeModelMap S b := by
  rw [latticeModelMap_eq_on S (add_mem_latticeDomain S ha hb),
    latticeModelMap_eq_on S ha, latticeModelMap_eq_on S hb]
  exact modelMapOnLattice_add S ⟨a, ha⟩ ⟨b, hb⟩

lemma mem_latticeDomain_of_mem {y : Fin d → ℤ} (hy : y ∈ S) :
    y ∈ latticeDomain S := by
  apply Submodule.subset_span
  exact ⟨y, hy, rfl⟩

lemma zero_mem_latticeDomain : 0 ∈ latticeDomain S := by
  change intVectorToReal (0 : Fin d → ℤ) ∈ integerGeneratedSubspace S
  rw [intVectorToReal_zero]
  exact Submodule.zero_mem _

lemma latticeEmbed_zero :
    latticeEmbed S ⟨0, zero_mem_latticeDomain S⟩ = 0 := by
  apply Subtype.ext_iff.mpr
  apply Subtype.ext_iff.mpr
  exact intVectorToReal_zero

/-- The model map restricted to `S` is a Freiman 2-isomorphism onto its image. -/
lemma latticeModelMap_isAddFreimanIso :
    IsAddFreimanIso 2 (S : Set (Fin d → ℤ))
      (latticeModelMap S '' (S : Set (Fin d → ℤ))) (latticeModelMap S) := by
  refine isAddFreimanIso_two.mpr ⟨?_, ?_⟩
  · constructor
    · intro x hx
      exact ⟨x, hx, rfl⟩
    · constructor
      · intro a ha b hb h
        exact latticeModelMap_injective_on S (mem_latticeDomain_of_mem S ha)
          (mem_latticeDomain_of_mem S hb) h
      · intro y hy
        exact hy
  · intro a ha b hb c hc d hd
    constructor
    · intro h
      have hab := latticeModelMap_add_on S (mem_latticeDomain_of_mem S ha)
        (mem_latticeDomain_of_mem S hb)
      have hcd := latticeModelMap_add_on S (mem_latticeDomain_of_mem S hc)
        (mem_latticeDomain_of_mem S hd)
      rw [← hab, ← hcd] at h
      exact latticeModelMap_injective_on S
        (add_mem_latticeDomain S (mem_latticeDomain_of_mem S ha)
          (mem_latticeDomain_of_mem S hb))
        (add_mem_latticeDomain S (mem_latticeDomain_of_mem S hc)
          (mem_latticeDomain_of_mem S hd)) h
    · intro h
      rw [← latticeModelMap_add_on S (mem_latticeDomain_of_mem S ha)
          (mem_latticeDomain_of_mem S hb),
        ← latticeModelMap_add_on S (mem_latticeDomain_of_mem S hc)
          (mem_latticeDomain_of_mem S hd), h]

lemma latticeModelMap_zero : latticeModelMap S 0 = 0 := by
  rw [latticeModelMap_eq_on S (zero_mem_latticeDomain S), modelMapOnLattice]
  rw [latticeEmbed_zero, map_zero, map_zero]

lemma rationalVectorToReal_zero : rationalVectorToReal (0 : Fin d → ℚ) = 0 := by
  ext i
  simp [rationalVectorToReal]

lemma rationalVectorToReal_latticeModelMap {y : Fin d → ℤ}
    (hy : y ∈ latticeDomain S) :
    rationalVectorToReal (latticeModelMap S y) =
      integerGeneratedCoordinateEquiv S (latticeEmbed S ⟨y, hy⟩) := by
  rw [latticeModelMap_eq_on S hy, modelMapOnLattice]
  ext i
  rw [rationalVectorToReal, integerGeneratedCoordinateEquiv_apply_lattice]
  dsimp only [ratCoordHom]
  exact_mod_cast rfl

/-- Translation by a constant is a Freiman isomorphism of order two in an abelian group. -/
lemma isAddFreimanIso_sub_const {G : Type*} [AddCommGroup G] (A : Set G) (c : G) :
    IsAddFreimanIso 2 A ((fun y ↦ y - c) '' A) (fun y ↦ y - c) := by
  refine isAddFreimanIso_two.mpr ⟨?_, ?_⟩
  · constructor
    · intro x hx
      exact ⟨x, hx, rfl⟩
    · constructor
      · intro a _ b _ h
        exact sub_left_injective h
      · intro y hy
        exact hy
  · intro a _ b _ c' _ d' _
    constructor
    · intro h
      calc a + b = (a - c) + (b - c) + (c + c) := by abel
      _ = (c' - c) + (d' - c) + (c + c) := by rw [h]
      _ = c' + d' := by abel
    · intro h
      calc (a - c) + (b - c) = a + b - (c + c) := by abel
      _ = c' + d' - (c + c) := by rw [h]
      _ = (c' - c) + (d' - c) := by abel

variable {G : Type*} [AddCommGroup G]

/-! ## Composing the model with a 2-proper GAP's coordinate map -/

variable [DecidableEq G]

/-- The translated coordinate set of `X` with respect to a basepoint `x₀`. -/
@[reducible]
def translatedCoords (P : GAP G) (X : Finset G) (x₀ : G) : Finset (Fin P.dim → ℤ) :=
  X.image (fun x ↦ P.coordinateMap x - P.coordinateMap x₀)

/-- The model dimension: the real rank of the span of the translated coordinate set. -/
@[reducible]
def modelDim (P : GAP G) (X : Finset G) (x₀ : G) : ℕ :=
  Module.finrank ℝ (integerGeneratedSubspace (translatedCoords P X x₀))

/-- The composed model map into `ℚ^r`. -/
@[reducible]
noncomputable def modelFn (P : GAP G) (X : Finset G) (x₀ : G) :
    G → Fin (modelDim P X x₀) → ℚ :=
  fun x ↦ latticeModelMap (translatedCoords P X x₀)
    (P.coordinateMap x - P.coordinateMap x₀)

lemma coordinateMap_isAddFreimanIso_on (P : GAP G) (hP : P.TwoProper)
    (X : Finset G) (hXP : X ⊆ P.carrier) :
    IsAddFreimanIso 2 (X : Set G)
      (P.coordinateMap '' (X : Set G)) P.coordinateMap := by
  apply IsAddFreimanIso.subset (Finset.coe_subset.mpr hXP)
    (P.coordinateMap_isAddFreimanIso hP)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact ⟨x, hx, rfl⟩
  · exact (P.coordinateMap_injective_on (GAP.twoProper_proper P hP)).mono
      (Finset.coe_subset.mpr hXP)
  · intro y hy
    exact hy

lemma modelFn_isAddFreimanIso (P : GAP G) (hP : P.TwoProper)
    (X : Finset G) (_hX : X.Nonempty) (hXP : X ⊆ P.carrier) (x₀ : G) (_hx₀ : x₀ ∈ X) :
    IsAddFreimanIso 2 (X : Set G)
      (modelFn P X x₀ '' (X : Set G)) (modelFn P X x₀) := by
  -- Step 1: coordinate map is a Freiman 2-iso on X
  have hf1 : IsAddFreimanIso 2 (X : Set G)
      (P.coordinateMap '' (X : Set G)) P.coordinateMap :=
    coordinateMap_isAddFreimanIso_on P hP X hXP
  -- Step 2: translation by the basepoint's coordinate is a Freiman 2-iso
  have hf2 : IsAddFreimanIso 2 (P.coordinateMap '' (X : Set G))
      ((fun y ↦ y - P.coordinateMap x₀) '' (P.coordinateMap '' (X : Set G)))
      (fun y ↦ y - P.coordinateMap x₀) :=
    isAddFreimanIso_sub_const _ _
  -- Compose steps 1 and 2
  have hf12 : IsAddFreimanIso 2 (X : Set G)
      ((fun y ↦ y - P.coordinateMap x₀) '' (P.coordinateMap '' (X : Set G)))
      ((fun y ↦ y - P.coordinateMap x₀) ∘ P.coordinateMap) :=
    hf2.comp hf1
  -- Step 3: the lattice model map is a Freiman 2-iso on the translated set
  have hf3 : IsAddFreimanIso 2 (translatedCoords P X x₀ : Set (Fin P.dim → ℤ))
      (latticeModelMap (translatedCoords P X x₀) '' (translatedCoords P X x₀ : Set _))
      (latticeModelMap (translatedCoords P X x₀)) :=
    latticeModelMap_isAddFreimanIso _
  -- Unify the intermediate set with the translated coords
  have htarget : ((fun y ↦ y - P.coordinateMap x₀) '' (P.coordinateMap '' (X : Set G)))
      = (translatedCoords P X x₀ : Set (Fin P.dim → ℤ)) := by
    simp only [Set.image_image, translatedCoords, Finset.coe_image]
  rw [htarget] at hf12
  -- Fully compose
  have hf123 : IsAddFreimanIso 2 (X : Set G)
      (latticeModelMap (translatedCoords P X x₀) '' (translatedCoords P X x₀ : Set _))
      (latticeModelMap (translatedCoords P X x₀) ∘
        ((fun y ↦ y - P.coordinateMap x₀) ∘ P.coordinateMap)) :=
    hf3.comp hf12
  -- Rewrite the target set and function to match the goal
  have htgt : (latticeModelMap (translatedCoords P X x₀) '' (translatedCoords P X x₀ : Set _)) =
      modelFn P X x₀ '' (X : Set G) := by
    simp only [translatedCoords, Finset.coe_image, Set.image_image]
  have hfn : latticeModelMap (translatedCoords P X x₀) ∘
      ((fun y ↦ y - P.coordinateMap x₀) ∘ P.coordinateMap) = modelFn P X x₀ := by
    rfl
  rw [← htgt, ← hfn]
  exact hf123

lemma modelFn_mem_contains_zero (P : GAP G) (X : Finset G) (x₀ : G) (hx₀ : x₀ ∈ X) :
    (0 : Fin (modelDim P X x₀) → ℝ) ∈
      ((X.image (modelFn P X x₀)).image rationalVectorToReal :
        Set (Fin (modelDim P X x₀) → ℝ)) := by
  refine Finset.mem_image.mpr ⟨modelFn P X x₀ x₀, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨x₀, hx₀, rfl⟩
  · change rationalVectorToReal
      (latticeModelMap (translatedCoords P X x₀) (P.coordinateMap x₀ - P.coordinateMap x₀)) = 0
    rw [sub_self, latticeModelMap_zero, rationalVectorToReal_zero]

lemma latticeModelMap_modelFn_rfl (P : GAP G) (X : Finset G) (x₀ y : G) :
    latticeModelMap (translatedCoords P X x₀)
        (P.coordinateMap y - P.coordinateMap x₀) =
      modelFn P X x₀ y := rfl

lemma modelFn_affineDim (P : GAP G) (_hP : P.TwoProper)
    (X : Finset G) (_hX : X.Nonempty) (_hXP : X ⊆ P.carrier) (x₀ : G) (hx₀ : x₀ ∈ X) :
    finsetAffineDim ((X.image (modelFn P X x₀)).image rationalVectorToReal) =
      modelDim P X x₀ := by
  let Y := translatedCoords P X x₀
  let r := modelDim P X x₀
  let H : Submodule ℝ (Fin P.dim → ℝ) := integerGeneratedSubspace Y
  let e : H ≃ₗ[ℝ] Fin r → ℝ := integerGeneratedCoordinateEquiv Y
  set T : Finset (Fin r → ℝ) :=
    (X.image (modelFn P X x₀)).image rationalVectorToReal with hTdef
  have h0 : (0 : Fin r → ℝ) ∈ (T : Set (Fin r → ℝ)) := modelFn_mem_contains_zero P X x₀ hx₀
  set Z : Set H := {p : H | ∃ y ∈ (Y : Set (Fin P.dim → ℤ)), ↑p = intVectorToReal y}
  have hT_eq : (T : Set (Fin r → ℝ)) = e '' Z := by
    ext x
    constructor
    · intro hx
      rw [hTdef, Finset.coe_image, Finset.coe_image] at hx
      rw [Set.mem_image] at hx
      obtain ⟨w, hw_mem, rfl⟩ := hx
      rw [Set.mem_image] at hw_mem
      obtain ⟨y, hyX, rfl⟩ := hw_mem
      set y_vec : Fin P.dim → ℤ := P.coordinateMap y - P.coordinateMap x₀
      have hyY : y_vec ∈ ↑Y := Finset.mem_image.mpr ⟨y, hyX, rfl⟩
      refine ⟨⟨intVectorToReal y_vec,
        mem_latticeDomain_of_mem Y hyY⟩,
        ⟨y_vec, hyY, rfl⟩, ?_⟩
      rw [← latticeModelMap_modelFn_rfl P X x₀ y,
        rationalVectorToReal_latticeModelMap (translatedCoords P X x₀)
        (mem_latticeDomain_of_mem Y hyY)]
      rfl
    · rintro ⟨p, hpZ, rfl⟩
      obtain ⟨y_vec, hyY, hp⟩ := hpZ
      obtain ⟨y_orig, hyX, hyeq⟩ := Finset.mem_image.mp hyY
      rw [hTdef, Finset.coe_image, Finset.coe_image]
      rw [Set.mem_image]
      refine ⟨modelFn P X x₀ y_orig, ⟨y_orig, hyX, rfl⟩, ?_⟩
      rw [← latticeModelMap_modelFn_rfl P X x₀ y_orig, hyeq]
      rw [rationalVectorToReal_latticeModelMap
        (translatedCoords P X x₀) (mem_latticeDomain_of_mem Y hyY)]
      congr 1
      apply Subtype.ext
      exact hp.symm
  have hsubtype_image : H.subtype '' Z = intVectorToReal '' (Y : Set (Fin P.dim → ℤ)) := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨y, hyY, hpy⟩ := hp
      exact ⟨y, hyY, hpy.symm⟩
    · rintro ⟨y, hyY, rfl⟩
      refine ⟨⟨intVectorToReal y, mem_latticeDomain_of_mem Y hyY⟩,
        ⟨y, hyY, rfl⟩, rfl⟩
  have hspanZ : Submodule.span ℝ Z = ⊤ := by
    apply Submodule.map_injective_of_injective H.subtype_injective
    rw [Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_span, hsubtype_image]
    rfl
  have hspanT : Submodule.span ℝ (T : Set (Fin r → ℝ)) = ⊤ := by
    rw [hT_eq]
    have hmap : Submodule.span ℝ (e '' Z) =
        Submodule.map e.toLinearMap (Submodule.span ℝ Z) :=
      (Submodule.map_span e.toLinearMap Z).symm
    rw [hmap, hspanZ, Submodule.map_top, LinearEquiv.range e]
  have hvspan : vectorSpan ℝ (T : Set (Fin r → ℝ)) = ⊤ := by
    rw [vectorSpan_eq_span_vsub_set_right _ h0]
    have hsub1 : (· -ᵥ (0 : Fin r → ℝ)) '' (T : Set (Fin r → ℝ)) ⊆
        (T : Set (Fin r → ℝ)) := by
      rintro _ ⟨y, hy, rfl⟩
      change (y -ᵥ (0 : Fin r → ℝ)) ∈ ↑T
      rw [vsub_eq_sub, sub_zero]
      exact hy
    have hsub2 : (T : Set (Fin r → ℝ)) ⊆
        (· -ᵥ (0 : Fin r → ℝ)) '' (T : Set (Fin r → ℝ)) := by
      intro x hx
      refine ⟨x, hx, ?_⟩
      change x -ᵥ (0 : Fin r → ℝ) = x
      rw [vsub_eq_sub, sub_zero]
    have heqt : Submodule.span ℝ
        ((· -ᵥ (0 : Fin r → ℝ)) '' (T : Set (Fin r → ℝ))) =
        Submodule.span ℝ (T : Set (Fin r → ℝ)) :=
      le_antisymm (Submodule.span_mono hsub1) (Submodule.span_mono hsub2)
    rw [heqt, hspanT]
  rw [show finsetAffineDim T =
      Module.finrank ℝ (affineSpan ℝ (T : Set (Fin r → ℝ))).direction from rfl,
    direction_affineSpan, hvspan]
  exact (finrank_top ℝ (Fin r → ℝ)).trans (Module.finrank_fin_fun ℝ)

/-- Appendix A's main dimension bound: the lattice-coordinate model gives a full-dimensional
Freiman model, so `modelDim ≤ freimanDim X`. -/
theorem freimanDim_le_of_twoProper_container (P : GAP G) (hP : P.TwoProper)
    (X : Finset G) (hX : X.Nonempty) (hXP : X ⊆ P.carrier) {x₀ : G} (hx₀ : x₀ ∈ X) :
    modelDim P X x₀ ≤ freimanDim X := by
  have hmodel : freimanModelDim X (modelDim P X x₀) := by
    refine ⟨modelFn P X x₀, ?_, ?_⟩
    · have hiso := modelFn_isAddFreimanIso P hP X hX hXP x₀ hx₀
      have hset : (X.image (modelFn P X x₀) : Set (Fin (modelDim P X x₀) → ℚ)) =
        modelFn P X x₀ '' (X : Set G) := Finset.coe_image
      rwa [hset]
    · exact modelFn_affineDim P hP X hX hXP x₀ hx₀
  have hcard : modelDim P X x₀ ≤ X.card := by
    have h := finsetAffineDim_le_card ((X.image (modelFn P X x₀)).image rationalVectorToReal)
    rw [modelFn_affineDim P hP X hX hXP x₀ hx₀] at h
    exact h.trans
      ((Finset.card_image_le (f := rationalVectorToReal)).trans
        (Finset.card_image_le (f := modelFn P X x₀)))
  exact le_freimanDim_of_model X hcard hmodel

end

end DenseSetsWithoutLargeSumsets
