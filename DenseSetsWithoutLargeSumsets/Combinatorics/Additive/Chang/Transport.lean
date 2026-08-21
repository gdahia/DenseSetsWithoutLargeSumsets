/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import Mathlib.Data.Pi.Interval
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.Chang.Model
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.Chang.Properization
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.Chang.Reboxing.EffectiveLattice

/-! # The coordinate-and-lattice transport of Appendix A

Given a finite set `X` inside the carrier of a 2-proper GAP `P`, this file replaces `P` by a
2-proper GAP whose dimension is at most `freimanDim X`, at a cost that depends only on `P.dim`.

The construction translates the coefficient vectors of `X` so that a chosen basepoint sits at the
origin, restricts the symmetric coefficient box to the rational subspace spanned by the translated
coefficients, reads that slice in a basis of the saturated lattice, reboxes the resulting lattice
points, and pushes the progression back into the ambient group.

Reboxing is supplied by the proved box-slice specialization under `Chang.Reboxing`, after the
effective-coordinate construction in this module identifies the full-rank lattice slice.
-/

namespace DenseSetsWithoutLargeSumsets

open scoped Pointwise Topology

noncomputable section

variable {d : ℕ} (S : Finset (Fin d → ℤ))

/-! ## Integral lattice coordinates -/

open Classical in
/-- The integer lattice coordinates of an integer vector lying in the span of `S`. -/
noncomputable def latticeIntMap (y : Fin d → ℤ) :
    Fin (Module.finrank ℝ (integerGeneratedSubspace S)) → ℤ :=
  if hy : y ∈ latticeDomain S then
    integerGeneratedLatticeCoordHom S (latticeEmbed S ⟨y, hy⟩)
  else 0

lemma latticeIntMap_eq_on {y : Fin d → ℤ} (hy : y ∈ latticeDomain S) :
    latticeIntMap S y = integerGeneratedLatticeCoordHom S (latticeEmbed S ⟨y, hy⟩) := by
  unfold latticeIntMap
  rw [dite_eq_left hy]

lemma latticeIntMap_injective_on : Set.InjOn (latticeIntMap S) (latticeDomain S) := by
  intro a ha b hb h
  rw [latticeIntMap_eq_on S ha, latticeIntMap_eq_on S hb] at h
  exact congr_arg Subtype.val (latticeEmbed_injective S
    (integerGeneratedLatticeCoordHom_injective S h))

lemma intVectorToReal_latticeIntMap {y : Fin d → ℤ} (hy : y ∈ latticeDomain S) :
    intVectorToReal (latticeIntMap S y) =
      integerGeneratedCoordinateEquiv S (latticeEmbed S ⟨y, hy⟩) := by
  rw [latticeIntMap_eq_on S hy]
  ext i
  rw [intVectorToReal, integerGeneratedCoordinateEquiv_apply_lattice,
    integerGeneratedLatticeCoordHom_apply]

/-- The lattice point of the saturated lattice with prescribed integer coordinates. -/
noncomputable def latticePoint
    (v : Fin (Module.finrank ℝ (integerGeneratedSubspace S)) → ℤ) :
    subspaceIntegerLattice (integerGeneratedSubspace S) :=
  ∑ i, v i • integerGeneratedLatticeBasis S i

/-- The integer vector of `ℤ^d` with prescribed lattice coordinates. -/
noncomputable def latticeVector
    (v : Fin (Module.finrank ℝ (integerGeneratedSubspace S)) → ℤ) : Fin d → ℤ :=
  ∑ i, v i • latticeBasisIntVector S i

lemma intVectorToReal_latticeVector
    (v : Fin (Module.finrank ℝ (integerGeneratedSubspace S)) → ℤ) :
    intVectorToReal (latticeVector S v) =
      ((latticePoint S v : integerGeneratedSubspace S) : Fin d → ℝ) := by
  rw [latticeVector, intVectorToReal_sum, latticePoint]
  push_cast
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [intVectorToReal_zsmul, intVectorToReal_latticeBasisIntVector]

lemma latticeVector_mem_latticeDomain
    (v : Fin (Module.finrank ℝ (integerGeneratedSubspace S)) → ℤ) :
    latticeVector S v ∈ latticeDomain S := by
  change intVectorToReal (latticeVector S v) ∈ integerGeneratedSubspace S
  rw [intVectorToReal_latticeVector]
  exact (latticePoint S v : integerGeneratedSubspace S).2

lemma latticeEmbed_latticeVector
    (v : Fin (Module.finrank ℝ (integerGeneratedSubspace S)) → ℤ) :
    latticeEmbed S ⟨latticeVector S v, latticeVector_mem_latticeDomain S v⟩ =
      latticePoint S v := by
  refine Subtype.ext (Subtype.ext ?_)
  exact intVectorToReal_latticeVector S v

lemma latticeIntMap_latticeVector
    (v : Fin (Module.finrank ℝ (integerGeneratedSubspace S)) → ℤ) :
    latticeIntMap S (latticeVector S v) = v := by
  rw [latticeIntMap_eq_on S (latticeVector_mem_latticeDomain S v), latticeEmbed_latticeVector]
  funext i
  rw [integerGeneratedLatticeCoordHom_apply]
  unfold integerGeneratedLatticeCoordinates latticePoint
  rw [(integerGeneratedLatticeBasis S).repr_sum_self]

lemma latticeVector_latticeIntMap {y : Fin d → ℤ} (hy : y ∈ latticeDomain S) :
    latticeVector S (latticeIntMap S y) = y := by
  apply latticeIntMap_injective_on S (latticeVector_mem_latticeDomain S _) hy
  rw [latticeIntMap_latticeVector]

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-! ## The lattice coordinates of the symmetric box -/

/-- The lattice coordinates of the symmetric box of `P`, a finite subset of `ℤ^r`. -/
noncomputable def sliceCoords (P : GAP G) (S : Finset (Fin P.dim → ℤ)) :
    Finset (Fin (Module.finrank ℝ (integerGeneratedSubspace S)) → ℤ) :=
  (symBox P).image (latticeIntMap S)

lemma card_sliceCoords_le (P : GAP G) (S : Finset (Fin P.dim → ℤ)) :
    (sliceCoords P S).card ≤ 2 ^ P.dim * ∏ i, P.length i :=
  Finset.card_image_le.trans (card_symBox P)

lemma mem_sliceCoords_of_mem_symBox {P : GAP G} {S : Finset (Fin P.dim → ℤ)}
    {v : Fin P.dim → ℤ} (hv : v ∈ symBox P) : latticeIntMap S v ∈ sliceCoords P S :=
  Finset.mem_image_of_mem _ hv

/-! ## The symmetric convex body cut out by the span -/

/-- The real symmetric box associated with the lengths of a GAP. -/
def realSymBox (P : GAP G) : Set (Fin P.dim → ℝ) :=
  {x | ∀ i, |x i| ≤ (P.length i : ℝ) - 1}

lemma realSymBox_eq_realBox (P : GAP G) :
    realSymBox P = BoxLattice.realBox P.halfWidth := by
  ext x
  constructor
  · intro hx i
    have hpos := P.length_pos i
    rw [GAP.halfWidth, Nat.cast_sub (by omega)]
    simpa only [Nat.cast_one] using hx i
  · intro hx i
    have hpos := P.length_pos i
    have hxi := hx i
    rw [GAP.halfWidth, Nat.cast_sub (by omega)] at hxi
    simpa only [Nat.cast_one] using hxi

lemma convex_realSymBox (P : GAP G) : Convex ℝ (realSymBox P) := by
  intro x hx y hy a b ha hb hab i
  apply (abs_add_le _ _).trans
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, abs_mul, abs_mul,
    abs_of_nonneg ha, abs_of_nonneg hb]
  nlinarith [hx i, hy i, abs_nonneg (x i), abs_nonneg (y i)]

lemma zero_mem_realSymBox (P : GAP G) : (0 : Fin P.dim → ℝ) ∈ realSymBox P := by
  intro i
  have hpos : 1 ≤ (P.length i : ℝ) := by exact_mod_cast P.length_pos i
  simp only [Pi.zero_apply, abs_zero]
  linarith

lemma neg_mem_realSymBox {P : GAP G} {x : Fin P.dim → ℝ} (hx : x ∈ realSymBox P) :
    -x ∈ realSymBox P := by
  intro i
  rw [Pi.neg_apply, abs_neg]
  exact hx i

/-- The slice of the real symmetric box by the span of `S`, read in lattice coordinates. -/
def sliceBody (P : GAP G) (S : Finset (Fin P.dim → ℤ)) :
    Set (Fin (Module.finrank ℝ (integerGeneratedSubspace S)) → ℝ) :=
  integerGeneratedCoordinateEquiv S ''
    {p : integerGeneratedSubspace S | (p : Fin P.dim → ℝ) ∈ realSymBox P}

lemma convex_sliceBody (P : GAP G) (S : Finset (Fin P.dim → ℤ)) :
    Convex ℝ (sliceBody P S) := by
  refine Convex.linear_image ?_ (integerGeneratedCoordinateEquiv S).toLinearMap
  intro x hx y hy a b ha hb hab
  exact convex_realSymBox P hx hy ha hb hab

lemma neg_mem_sliceBody {P : GAP G} {S : Finset (Fin P.dim → ℤ)}
    {x : Fin (Module.finrank ℝ (integerGeneratedSubspace S)) → ℝ} (hx : x ∈ sliceBody P S) :
    -x ∈ sliceBody P S := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨-p, neg_mem_realSymBox hp, map_neg _ p⟩

lemma zero_mem_sliceBody (P : GAP G) (S : Finset (Fin P.dim → ℤ)) :
    (0 : Fin (Module.finrank ℝ (integerGeneratedSubspace S)) → ℝ) ∈ sliceBody P S :=
  ⟨0, zero_mem_realSymBox P, map_zero _⟩

lemma coordinate_eq_zero_of_mem_integerGeneratedSubspace
    {P : GAP G} {S : Finset (Fin P.dim → ℤ)}
    (hSbox : ∀ v ∈ S, v ∈ symBox P)
    (p : integerGeneratedSubspace S) {i : Fin P.dim} (hi : P.length i = 1) :
    (p : Fin P.dim → ℝ) i = 0 := by
  apply Submodule.span_induction (R := ℝ)
      (p := fun x _ ↦ x i = 0) (s := intVectorToReal '' (S : Set (Fin P.dim → ℤ)))
  · rintro x ⟨v, hv, rfl⟩
    have hvbox := mem_symBox.mp (hSbox v hv) i
    have hvi : v i = 0 := by
      rw [hi] at hvbox
      apply abs_eq_zero.mp
      have habs := abs_nonneg (v i)
      omega
    simp only [intVectorToReal, hvi, Int.cast_zero]
  · simp
  · intro x y _ _ hx hy
    simp only [Pi.add_apply, hx, hy, add_zero]
  · intro a x _ hx
    simp only [Pi.smul_apply, smul_eq_mul, hx, mul_zero]
  · exact p.2

lemma sliceSource_mem_nhds (P : GAP G) (S : Finset (Fin P.dim → ℤ))
    (hSbox : ∀ v ∈ S, v ∈ symBox P) :
    {p : integerGeneratedSubspace S | (p : Fin P.dim → ℝ) ∈ realSymBox P} ∈
      𝓝 (0 : integerGeneratedSubspace S) := by
  apply Filter.mem_of_superset (Metric.ball_mem_nhds 0 zero_lt_one)
  intro p hp i
  rw [mem_ball_zero_iff] at hp
  by_cases hi : P.length i = 1
  · rw [coordinate_eq_zero_of_mem_integerGeneratedSubspace hSbox p hi, abs_zero]
    rw [hi]
    norm_num
  · have hlen : 2 ≤ P.length i := by
      have hpos := P.length_pos i
      omega
    have hcoord : |(p : Fin P.dim → ℝ) i| ≤ ‖p‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_le_pi_norm (p : Fin P.dim → ℝ) i
    have hlenR : (2 : ℝ) ≤ (P.length i : ℝ) := by exact_mod_cast hlen
    linarith

lemma isCompact_sliceSource (P : GAP G) (S : Finset (Fin P.dim → ℤ)) :
    IsCompact {p : integerGeneratedSubspace S |
      (p : Fin P.dim → ℝ) ∈ realSymBox P} := by
  rw [realSymBox_eq_realBox]
  apply Metric.isCompact_of_isClosed_isBounded
    ((BoxLattice.isClosed_realBox P.halfWidth).preimage continuous_subtype_val)
  obtain ⟨R, hR⟩ :=
      (BoxLattice.isBounded_realBox P.halfWidth).subset_closedBall
        (0 : Fin P.dim → ℝ)
  rw [Metric.isBounded_iff_subset_closedBall (0 : integerGeneratedSubspace S)]
  refine ⟨R, ?_⟩
  intro p hp
  have hpR := hR hp
  rw [Metric.mem_closedBall, dist_zero_right] at hpR ⊢
  simpa only [Submodule.norm_coe] using hpR

lemma isCompact_sliceBody (P : GAP G) (S : Finset (Fin P.dim → ℤ)) :
    IsCompact (sliceBody P S) := by
  apply (isCompact_sliceSource P S).image
  exact LinearMap.continuous_of_finiteDimensional
    (integerGeneratedCoordinateEquiv S).toLinearMap

lemma isClosed_sliceBody (P : GAP G) (S : Finset (Fin P.dim → ℤ)) :
    IsClosed (sliceBody P S) :=
  (isCompact_sliceBody P S).isClosed

lemma isBounded_sliceBody (P : GAP G) (S : Finset (Fin P.dim → ℤ)) :
    Bornology.IsBounded (sliceBody P S) :=
  (isCompact_sliceBody P S).isBounded

lemma sliceBody_mem_nhds (P : GAP G) (S : Finset (Fin P.dim → ℤ))
    (hSbox : ∀ v ∈ S, v ∈ symBox P) :
    sliceBody P S ∈
      𝓝 (0 : Fin (Module.finrank ℝ (integerGeneratedSubspace S)) → ℝ) := by
  rw [← map_zero (integerGeneratedCoordinateEquiv S)]
  exact (LinearMap.isOpenMap_of_finiteDimensional
      (integerGeneratedCoordinateEquiv S).toLinearMap
      (integerGeneratedCoordinateEquiv S).surjective).image_mem_nhds
    (sliceSource_mem_nhds P S hSbox)

lemma intVectorToReal_mem_realSymBox {P : GAP G} {v : Fin P.dim → ℤ} (hv : v ∈ symBox P) :
    intVectorToReal v ∈ realSymBox P := by
  intro i
  have hi : |v i| ≤ (P.length i : ℤ) - 1 := by
    have := mem_symBox.mp hv i
    omega
  have hcast : (|v i| : ℝ) ≤ ((P.length i : ℤ) - 1 : ℤ) := by exact_mod_cast hi
  push_cast at hcast
  simpa [intVectorToReal] using hcast

lemma mem_symBox_of_intVectorToReal_mem {P : GAP G} {v : Fin P.dim → ℤ}
    (hv : intVectorToReal v ∈ realSymBox P) : v ∈ symBox P := by
  apply mem_symBox.mpr
  intro i
  have hi : ((|v i| : ℤ) : ℝ) ≤ ((P.length i : ℝ) - 1) := by
    simpa [intVectorToReal, abs_of_nonneg] using hv i
  have hi' : (|v i| : ℤ) ≤ (P.length i : ℤ) - 1 := by exact_mod_cast hi
  omega

/-- The lattice coordinates of the symmetric box are exactly the integer points of the slice. -/
lemma mem_sliceCoords_iff {P : GAP G} {S : Finset (Fin P.dim → ℤ)}
    {v : Fin (Module.finrank ℝ (integerGeneratedSubspace S)) → ℤ} :
    v ∈ sliceCoords P S ↔ intVectorToReal v ∈ sliceBody P S := by
  constructor
  · rintro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    by_cases hdom : w ∈ latticeDomain S
    · rw [intVectorToReal_latticeIntMap S hdom]
      exact ⟨latticeEmbed S ⟨w, hdom⟩, intVectorToReal_mem_realSymBox hw, rfl⟩
    · rw [latticeIntMap, dite_eq_right hdom, intVectorToReal_zero]
      exact zero_mem_sliceBody P S
  · rintro ⟨p, hp, hep⟩
    have hcoord : integerGeneratedCoordinateEquiv S (latticePoint S v) = intVectorToReal v := by
      rw [← latticeEmbed_latticeVector,
        ← intVectorToReal_latticeIntMap S (latticeVector_mem_latticeDomain S v),
        latticeIntMap_latticeVector]
    have hmem : latticeVector S v ∈ symBox P := by
      apply mem_symBox_of_intVectorToReal_mem
      rw [intVectorToReal_latticeVector S v,
        (integerGeneratedCoordinateEquiv S).injective (hcoord.trans hep.symm)]
      exact hp
    rw [← latticeIntMap_latticeVector S v]
    exact mem_sliceCoords_of_mem_symBox hmem

lemma span_sliceBody_inter_standardLattice_eq_top
    (P : GAP G) (S : Finset (Fin P.dim → ℤ))
    (hSbox : ∀ v ∈ S, v ∈ symBox P) :
    Submodule.span ℝ
      (sliceBody P S ∩
        ((((⊤ :
          AddSubgroup
            (Fin (Module.finrank ℝ (integerGeneratedSubspace S)) → ℤ)).map
          (BoxLattice.intCastHom :
            (Fin (Module.finrank ℝ (integerGeneratedSubspace S)) → ℤ) →+
              (Fin (Module.finrank ℝ (integerGeneratedSubspace S)) → ℝ)))) :
                Set (Fin (Module.finrank ℝ (integerGeneratedSubspace S)) → ℝ))) = ⊤ := by
  apply top_unique
  rw [← span_intVectorToReal_effectiveLatticeCoords_eq_top S]
  apply Submodule.span_mono
  intro x hx
  rw [Finset.mem_coe, Finset.mem_image] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  rw [effectiveLatticeCoords, Finset.mem_image] at hc
  obtain ⟨v, hvS, rfl⟩ := hc
  constructor
  · rw [← mem_sliceCoords_iff]
    exact mem_sliceCoords_of_mem_symBox (hSbox v hvS)
  · exact AddSubgroup.mem_map.mpr ⟨effectiveLatticeMap S v, Set.mem_univ _, rfl⟩

/-- The integer points of the effective-coordinate slice of a coefficient box admit a proper
centered reboxing with the same explicit rank factor as projected boxes. -/
theorem exists_proper_GAP_reboxing_sliceCoords
    (P : GAP G) (S : Finset (Fin P.dim → ℤ))
    (hSbox : ∀ v ∈ S, v ∈ symBox P) :
    ∃ Q : GAP (Fin (Module.finrank ℝ (integerGeneratedSubspace S)) → ℤ), Q.Proper ∧
      sliceCoords P S ⊆ Q.carrier ∧
      Q.dim = Module.finrank ℝ (integerGeneratedSubspace S) ∧
      Q.carrier.card ≤
        boxReboxingFactor (Module.finrank ℝ (integerGeneratedSubspace S)) *
          (sliceCoords P S).card := by
  let r := Module.finrank ℝ (integerGeneratedSubspace S)
  let L : AddSubgroup (Fin r → ℝ) :=
    (⊤ : AddSubgroup (Fin r → ℤ)).map
      (BoxLattice.intCastHom : (Fin r → ℤ) →+ (Fin r → ℝ))
  let : DiscreteTopology L := BoxLattice.discreteTopology_map ⊤
  have hsymm : ∀ x, x ∈ sliceBody P S ↔ -x ∈ sliceBody P S := by
    intro x
    exact ⟨neg_mem_sliceBody, fun hx ↦ by simpa using neg_mem_sliceBody hx⟩
  let B := Classical.choice <|
    exists_gaugeControlledLatticeBox_aux r L (sliceBody P S) (by simp [r])
      (convex_sliceBody P S) (isClosed_sliceBody P S)
      (sliceBody_mem_nhds P S hSbox) (isBounded_sliceBody P S)
      (fun x hx ↦ (hsymm x).mp hx)
      (span_sliceBody_inter_standardLattice_eq_top P S hSbox)
  obtain ⟨C, hCcard⟩ :=
    B.exists_adaptedLatticeBox (convex_sliceBody P S) (isClosed_sliceBody P S)
      (sliceBody_mem_nhds P S hSbox)
      ((NormedSpace.isVonNBounded_iff ℝ).mpr (isBounded_sliceBody P S))
      hsymm (fun v ↦ mem_sliceCoords_iff) (gaugeReboxingDilation r)
  obtain ⟨Q, hQproper, hDQ, hQdim, hQcard⟩ :=
    C.exists_proper_centeredBoxGAP
  refine ⟨Q, hQproper, hDQ, hQdim, ?_⟩
  rw [hQcard, boxReboxingFactor]
  exact hCcard

/-! ## Pushing lattice coordinates back into the group -/

/-- The homomorphism `ℤ^r →+ ℤ^d` reconstructing integer vectors from lattice coordinates. -/
def latticeVectorHom : (Fin (Module.finrank ℝ (integerGeneratedSubspace S)) → ℤ) →+
    (Fin d → ℤ) where
  toFun := latticeVector S
  map_zero' := by simp [latticeVector]
  map_add' a b := by simp [latticeVector, add_smul, Finset.sum_add_distrib]

/-- The homomorphism `ℤ^r →+ G` reconstructing group elements from lattice coordinates. -/
def latticeStepHom (P : GAP G) (S : Finset (Fin P.dim → ℤ)) :
    (Fin (Module.finrank ℝ (integerGeneratedSubspace S)) → ℤ) →+ G :=
  (stepHom P).comp (latticeVectorHom S)

lemma latticeStepHom_latticeIntMap (P : GAP G) (S : Finset (Fin P.dim → ℤ))
    {y : Fin P.dim → ℤ} (hy : y ∈ latticeDomain S) :
    latticeStepHom P S (latticeIntMap S y) = stepHom P y := by
  rw [latticeStepHom, AddMonoidHom.comp_apply]
  exact congr_arg (stepHom P) (latticeVector_latticeIntMap S hy)

lemma card_shift_le (P : GAP G) (c : G) : (P.shift c).carrier.card ≤ P.carrier.card :=
  Finset.card_image_le

/-! ## The transport theorem -/

/-- The universal cost constant for coordinate reduction. -/
def coordinateReductionConstant : ℝ :=
  properizationConstant + 2

lemma coordinateReductionConstant_pos : 0 < coordinateReductionConstant := by
  rw [coordinateReductionConstant]
  linarith [properizationConstant_pos]

/-- Appendix A's coordinate-and-lattice transport: a finite set inside a 2-proper GAP is also
contained in a 2-proper GAP of dimension at most its Freiman dimension, at a cost depending only
on the dimension of the original progression.

The hypothesis that the transported progression still fits inside `ZMod q` is what the
properization input requires; in the application it follows from the density hypothesis of the
container theorem. -/
theorem chang_coordinate_reduction {q : ℕ} (X : Finset (ZMod q))
    (P : GAP (ZMod q)) (hq : Nat.Prime q) (hX : X.Nonempty)
    (hXP : X ⊆ P.carrier) (hP : P.TwoProper)
    (hroom :
      Real.exp (coordinateReductionConstant * ((P.dim : ℝ) + 2) ^ 4) *
        P.carrier.card ≤ q) :
    ∃ Q : GAP (ZMod q), Q.TwoProper ∧ X ⊆ Q.carrier ∧ Q.dim ≤ freimanDim X ∧
      (∀ i, 1 < Q.length i) ∧
      (Q.carrier.card : ℝ) ≤
        Real.exp (coordinateReductionConstant * ((P.dim : ℝ) + 2) ^ 4) *
          P.carrier.card := by
  obtain ⟨x₀, hx₀⟩ := hX
  set S := translatedCoords P X x₀ with hS
  set r := Module.finrank ℝ (integerGeneratedSubspace S) with hr
  have hrd : r ≤ P.dim := by
    simpa using Submodule.finrank_le (integerGeneratedSubspace S)
  have hSbox : ∀ v ∈ S, v ∈ symBox P := by
    intro v hv
    rw [hS, translatedCoords, Finset.mem_image] at hv
    obtain ⟨x, -, rfl⟩ := hv
    exact sub_coordinateMap_mem_symBox P x x₀
  obtain ⟨P', -, hDP', hP'dim, hP'card⟩ :=
    exists_proper_GAP_reboxing_sliceCoords P S hSbox
  set Q₀ : GAP (ZMod q) := (P'.map (latticeStepHom P S)).shift x₀ with hQ₀
  have hXQ₀ : X ⊆ Q₀.carrier := by
    intro x hxX
    have hSmem : P.coordinateMap x - P.coordinateMap x₀ ∈ S := by
      rw [hS]
      exact Finset.mem_image_of_mem _ hxX
    have hval : latticeStepHom P S
        (latticeIntMap S (P.coordinateMap x - P.coordinateMap x₀)) = x - x₀ := by
      rw [latticeStepHom_latticeIntMap P S (mem_latticeDomain_of_mem S hSmem), map_sub,
        stepHom_coordinateMap P (hXP hxX), stepHom_coordinateMap P (hXP hx₀)]
      abel
    have hmem : x - x₀ ∈ (P'.map (latticeStepHom P S)).carrier :=
      hval ▸ Finset.mem_image_of_mem _
        (hDP' (mem_sliceCoords_of_mem_symBox (sub_coordinateMap_mem_symBox P x x₀)))
    exact Finset.mem_image.mpr ⟨x - x₀, hmem, sub_add_cancel x x₀⟩
  have hQ₀dim : Q₀.dim ≤ P.dim := hP'dim.le.trans hrd
  -- The lattice slice, the reboxed progression, and the symmetric box each cost a factor.
  have hQ₀cardCube : (Q₀.carrier.card : ℝ) ≤
      Real.exp (((P.dim : ℝ) + 2) ^ 3) *
        (2 ^ P.dim * P.carrier.card) := by
    have hslice : ((sliceCoords P S).card : ℝ) ≤ 2 ^ P.dim * P.carrier.card := by
      rw [GAP.card_eq_prod_length P (GAP.twoProper_proper P hP)]
      exact_mod_cast card_sliceCoords_le P S
    have hmapCard :
        (Q₀.carrier.card : ℝ) ≤ P'.carrier.card := by
      exact_mod_cast (card_shift_le _ _).trans
        (P'.card_map_le (latticeStepHom P S))
    have hP'cardR :
        (P'.carrier.card : ℝ) ≤ boxReboxingFactor r * (sliceCoords P S).card := by
      exact_mod_cast hP'card
    refine hmapCard.trans (hP'cardR.trans ?_)
    exact mul_le_mul (boxReboxingFactor_le_exp_cube hrd) hslice
      (by positivity) (by positivity)
  have hQ₀card : (Q₀.carrier.card : ℝ) ≤
      Real.exp (2 * ((P.dim : ℝ) + 2) ^ 4) *
        P.carrier.card := by
    apply hQ₀cardCube.trans
    apply (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (two_pow_le_exp P.dim) (Nat.cast_nonneg _))
      (by positivity)).trans
    rw [← mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (Nat.cast_nonneg _)
    have hpow : ((P.dim : ℝ) + 2) ^ 3 ≤ ((P.dim : ℝ) + 2) ^ 4 := by
      rw [pow_succ]
      nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ (P.dim : ℝ) + 2) 3]
    nlinarith
  have hexp : Real.exp (properizationConstant * ((Q₀.dim : ℝ) + 2) ^ 4) ≤
      Real.exp (properizationConstant * ((P.dim : ℝ) + 2) ^ 4) := by
    refine Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ 4)
        properizationConstant_pos.le)
    have hcast := (Nat.cast_le (α := ℝ)).mpr hQ₀dim
    linarith
  have hchain :
      Real.exp (properizationConstant * ((Q₀.dim : ℝ) + 2) ^ 4) *
          Q₀.carrier.card ≤
      Real.exp (coordinateReductionConstant * ((P.dim : ℝ) + 2) ^ 4) *
        P.carrier.card := by
    apply (mul_le_mul hexp hQ₀card (Nat.cast_nonneg _) (Real.exp_nonneg _)).trans
    rw [← mul_assoc, ← Real.exp_add]
    rw [coordinateReductionConstant]
    ring_nf
    exact le_rfl
  obtain ⟨Q, hQtwo, hQ₀Q, hQlen, hQdim, hQcard⟩ :=
    exists_twoProperGAP_container Q₀ hq (hchain.trans hroom)
  refine ⟨Q, hQtwo, hXQ₀.trans hQ₀Q, ?_, hQlen, hQcard.trans hchain⟩
  refine hQdim.trans (hP'dim.le.trans ?_)
  exact freimanDim_le_of_twoProper_container P hP X ⟨x₀, hx₀⟩ hXP hx₀

end

end DenseSetsWithoutLargeSumsets
