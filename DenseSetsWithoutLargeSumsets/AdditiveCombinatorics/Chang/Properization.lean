/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.Chang.Reboxing.GaugeInduction
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.Chang.BoxLatticePoints
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.Chang.GapToolkit
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.Chang.GeometryOfNumbers
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.Chang.Lattice

/-! # Properization of generalized arithmetic progressions

This file develops the lattice-of-relations description of properness and proves
`exists_twoProperGAP_container` by iterated saturated quotient rank reduction.

The main pieces are:

- `GAP.relations`, the kernel of the step homomorphism, and the characterizations
  `GAP.proper_iff` and `GAP.twoProper_iff` of properness by the absence of short relations;
- `GAP.boxRelations` and `GAP.prod_length_le_card_mul_card_boxRelations`, which bound the total
  size of the coefficient box by the size of the progression times the number of short relations;
- `GAP.exists_ne_zero_mem_relations`, Minkowski's first theorem for a progression, and
  `GAP.card_twoBoxRelations_le_of_proper`, the packing bound: a proper progression has at most
  `6 ^ dim` relations in its doubled box, both read off from `Chang.GeometryOfNumbers`;
- `GAP.ofData` and `GAP.reshape`, which rebuild a progression from prescribed data;
- `GAP.relationMinimum`, the successive minima of the relation lattice with respect to the
  coefficient box, with `GAP.twoProper_of_three_lt_relationMinimum` and
  `GAP.exists_ne_zero_relation_short` reading properness off the first minimum, and
  `GAP.prod_length_le_card_mul_prod_relationMinimum` — the lattice point count of
  `Chang.BoxLatticePoints` read through a progression — providing the size accounting;
- `GAP.single_natCast_mem_relations` and `GAP.exists_hasIndependentShort_dim`: in `ZMod q` the
  relation lattice contains `q ℤ ^ dim`, so it has full rank and all `dim` successive minima are
  defined, monotone and positive, not only `λ₁`. `GAP.prod_length_le_card_mul_pow` is the resulting
  single-minimum form of the size accounting;
- `GAP.exists_primitive_relation_short`: with enough room a relation attaining the first minimum is
  primitive, so the subgroup it generates is saturated in `ℤ ^ dim`, the quotient is free and
  `stepHom` factors through it.

The proof quotients simultaneously by the saturated sublattice spanned by all relations below a
successive-minimum cutoff, reboxes the quotient, and iterates the resulting strict dimension drop.
The cubic cost of each step telescopes into the quartic exponent in the final theorem.

The reboxing step is the proved shortest-direction projection construction under
`Chang.Reboxing`; no external geometric input is used.
-/

namespace DenseSetsWithoutLargeSumsets

open scoped Pointwise Topology

noncomputable section

/-- A surjective real projection of an integral box with positive half-widths is a neighborhood
of the origin. -/
lemma image_realBox_mem_nhds_of_surjective {d s : ℕ} (m : Fin d → ℕ)
    (hm : ∀ i, 0 < m i) (π : (Fin d → ℝ) →ₗ[ℝ] (Fin s → ℝ))
    (hπ : Function.Surjective π) :
    π '' BoxLattice.realBox m ∈ 𝓝 (0 : Fin s → ℝ) := by
  rw [← map_zero π]
  exact (LinearMap.isOpenMap_of_finiteDimensional π hπ).image_mem_nhds
    (BoxLattice.realBox_mem_nhds hm)

/-- The projected standard lattice points of a positive coordinate box span the target of every
surjective integral projection. -/
lemma span_image_realBox_inter_standardLattice_eq_top {d s : ℕ} (m : Fin d → ℕ)
    (hm : ∀ i, 0 < m i)
    (π : (Fin d → ℝ) →ₗ[ℝ] (Fin s → ℝ))
    (πz : (Fin d → ℤ) →+ (Fin s → ℤ))
    (hcast : ∀ v, π (BoxLattice.intCastHom v) = BoxLattice.intCastHom (πz v))
    (hπ : Function.Surjective π) :
    Submodule.span ℝ
      ((π '' BoxLattice.realBox m) ∩
        ((((⊤ : AddSubgroup (Fin s → ℤ)).map
          (BoxLattice.intCastHom : (Fin s → ℤ) →+ (Fin s → ℝ)))) :
            Set (Fin s → ℝ))) = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := hπ y
  rw [← (Pi.basisFun ℝ (Fin d)).sum_repr x, map_sum]
  simp_rw [map_smul]
  refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ ?_
  apply Submodule.subset_span
  refine ⟨⟨(Pi.basisFun ℝ (Fin d)) i, ?_, rfl⟩, ?_⟩
  · rw [BoxLattice.mem_realBox]
    intro j
    by_cases hji : j = i
    · subst j
      have hmi : (1 : ℝ) ≤ m i := by exact_mod_cast hm i
      simpa using hmi
    · simp [Pi.basisFun_apply, hji]
  · refine AddSubgroup.mem_map.mpr
      ⟨πz (Pi.single i 1), Set.mem_univ _, ?_⟩
    rw [← hcast]
    congr 1
    ext j
    simp [Pi.basisFun_apply, Pi.single_apply]

/-- Rebox the integer points of a surjective integral projection of a positive coordinate box.
This is the common projected-box theorem used by one-relation and simultaneous properization. -/
theorem exists_proper_GAP_reboxing_image_realBox {d s : ℕ} (m : Fin d → ℕ)
    (hm : ∀ i, 0 < m i)
    (π : (Fin d → ℝ) →ₗ[ℝ] (Fin s → ℝ))
    (πz : (Fin d → ℤ) →+ (Fin s → ℤ))
    (hcast : ∀ v, π (BoxLattice.intCastHom v) = BoxLattice.intCastHom (πz v))
    (hπ : Function.Surjective π)
    (D : Finset (Fin s → ℤ))
    (hD : ∀ v, v ∈ D ↔ BoxLattice.intCastHom v ∈ π '' BoxLattice.realBox m) :
    ∃ P : GAP (Fin s → ℤ), P.Proper ∧ D ⊆ P.carrier ∧ P.dim = s ∧
      P.carrier.card ≤ boxReboxingFactor s * D.card := by
  let K := π '' BoxLattice.realBox m
  have hcompact : IsCompact K := by
    refine (Metric.isCompact_of_isClosed_isBounded
      (BoxLattice.isClosed_realBox m) (BoxLattice.isBounded_realBox m)).image ?_
    exact LinearMap.continuous_of_finiteDimensional π
  have hsymm : ∀ x, x ∈ K ↔ -x ∈ K := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨-y, BoxLattice.neg_mem_realBox m y hy, map_neg π y⟩
    · rintro ⟨y, hy, hyx⟩
      refine ⟨-y, BoxLattice.neg_mem_realBox m y hy, ?_⟩
      rw [map_neg, hyx, neg_neg]
  let L : AddSubgroup (Fin s → ℝ) :=
    (⊤ : AddSubgroup (Fin s → ℤ)).map
      (BoxLattice.intCastHom : (Fin s → ℤ) →+ (Fin s → ℝ))
  letI : DiscreteTopology L := BoxLattice.discreteTopology_map ⊤
  let B := Classical.choice <|
    exists_gaugeControlledLatticeBox_aux s L K (by simp)
      ((BoxLattice.convex_realBox m).linear_image π) hcompact.isClosed
      (image_realBox_mem_nhds_of_surjective m hm π hπ) hcompact.isBounded
      (fun x hx ↦ (hsymm x).mp hx)
      (span_image_realBox_inter_standardLattice_eq_top m hm π πz hcast hπ)
  obtain ⟨C, hCcard⟩ :=
    B.exists_adaptedLatticeBox ((BoxLattice.convex_realBox m).linear_image π)
      hcompact.isClosed (image_realBox_mem_nhds_of_surjective m hm π hπ)
      ((NormedSpace.isVonNBounded_iff ℝ).mpr hcompact.isBounded) hsymm
      (fun v ↦ by change v ∈ D ↔ BoxLattice.intCastHom v ∈ K; exact hD v)
      (gaugeReboxingDilation s)
  obtain ⟨P, hPproper, hDP, hPdim, hPcard⟩ :=
    C.exists_proper_centeredBoxGAP
  refine ⟨P, hPproper, hDP, hPdim, ?_⟩
  rw [hPcard, boxReboxingFactor]
  exact hCcard

section Steps

variable {G : Type*} [AddCommGroup G]

/-! ## Properness and the lattice of relations -/

/-- The element of a GAP with prescribed coefficients, read through the step homomorphism. -/
lemma gapMap_eq_stepsHom {d : ℕ} (origin : G) (step : Fin d → G) (length : Fin d → ℕ)
    (w : (i : Fin d) → Fin (length i)) :
    gapMap origin step length w = origin + stepsHom step fun i ↦ ((w i : ℕ) : ℤ) := by
  rw [stepsHom_natCast]
  rfl

/-- A progression is proper exactly when its steps admit no nonzero relation whose coefficients
are bounded by the lengths. -/
lemma injective_gapMap_iff {d : ℕ} (origin : G) (step : Fin d → G) (length : Fin d → ℕ) :
    Function.Injective (gapMap origin step length) ↔
      ∀ v : Fin d → ℤ, stepsHom step v = 0 → (∀ i, |v i| < (length i : ℤ)) → v = 0 := by
  constructor
  · intro hinj v hv hlt
    have hpos : ∀ i, (v i).toNat < length i := by
      intro i
      have := abs_lt.mp (hlt i)
      omega
    have hneg : ∀ i, (-v i).toNat < length i := by
      intro i
      have := abs_lt.mp (hlt i)
      omega
    have hcoeff := hinj (a₁ := fun i ↦ ⟨(v i).toNat, hpos i⟩)
      (a₂ := fun i ↦ ⟨(-v i).toNat, hneg i⟩) ?_
    · funext i
      have hi := congr_arg (fun w ↦ (w i : ℕ)) hcoeff
      simp only [Pi.zero_apply] at hi ⊢
      omega
    · rw [gapMap_eq_stepsHom, gapMap_eq_stepsHom, add_right_inj, ← sub_eq_zero, ← map_sub, ← hv]
      refine congr_arg (stepsHom step) (funext fun i ↦ ?_)
      simp only [Pi.sub_apply]
      omega
  · intro hrel w₁ w₂ hw
    have hzero := hrel (fun i ↦ (w₁ i : ℤ) - (w₂ i : ℤ)) ?_ ?_
    · funext i
      refine Fin.ext ?_
      have hi := congr_fun hzero i
      simp only [Pi.zero_apply, sub_eq_zero] at hi
      exact_mod_cast hi
    · rw [gapMap_eq_stepsHom, gapMap_eq_stepsHom, add_right_inj] at hw
      change stepsHom step ((fun i ↦ ((w₁ i : ℕ) : ℤ)) - fun i ↦ ((w₂ i : ℕ) : ℤ)) = 0
      rw [map_sub, sub_eq_zero]
      exact hw
    · intro i
      have := (w₁ i).isLt
      have := (w₂ i).isLt
      rw [abs_lt]
      omega

end Steps

/-! ## Listing the coordinates other than a given one

Dropping a coordinate from a progression needs an enumeration of the remaining ones. `skipCoord j`
is the increasing bijection from `Fin (d - 1)` onto the coordinates other than `j`; it is
`Fin.succAbove` written so that it does not need `d` to be presented as a successor. -/

/-- The coordinates of `Fin d` other than `j`, enumerated by `Fin (d - 1)`. -/
def skipCoord {d : ℕ} (j : Fin d) (i : Fin (d - 1)) : Fin d :=
  ⟨if (i : ℕ) < (j : ℕ) then (i : ℕ) else (i : ℕ) + 1, by
    have h1 := i.isLt
    have h2 := j.isLt
    split <;> omega⟩

lemma skipCoord_ne {d : ℕ} (j : Fin d) (i : Fin (d - 1)) : skipCoord j i ≠ j := by
  intro h
  have h1 := i.isLt
  have h2 := j.isLt
  have h3 := congr_arg Fin.val h
  simp only [skipCoord] at h3
  split at h3 <;> omega

lemma skipCoord_injective {d : ℕ} (j : Fin d) : Function.Injective (skipCoord j) := by
  intro a b hab
  have h1 := a.isLt
  have h2 := b.isLt
  have h3 := j.isLt
  have h4 := congr_arg Fin.val hab
  simp only [skipCoord] at h4
  refine Fin.ext ?_
  split at h4 <;> split at h4 <;> omega

lemma mem_range_skipCoord {d : ℕ} {j i : Fin d} (hij : i ≠ j) : i ∈ Set.range (skipCoord j) := by
  have h1 := i.isLt
  have h2 := j.isLt
  have hne : (i : ℕ) ≠ (j : ℕ) := fun h ↦ hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨⟨(i : ℕ), by omega⟩, Fin.ext (by simp only [skipCoord]; split <;> omega)⟩
  · exact ⟨⟨(i : ℕ) - 1, by omega⟩, Fin.ext (by simp only [skipCoord]; split <;> omega)⟩

/-! ## Quotient coordinates along a primitive vector

The general properization step does not eliminate a coordinate of a relation. It quotients the
coefficient lattice by that relation. The lemmas in this section provide the integral coordinates
for a one-relation quotient. A primitive vector is a member of some basis of `ℤ ^ d`; deleting its
basis coordinate then realizes the quotient as `ℤ ^ (d - 1)`.

The basis-extension statement is obtained from Smith normal form. Its formulation matches
`GAP.exists_primitive_relation_short`: divisibility of every coordinate forces the divisor to be a
unit. -/

/-- A vector whose only common divisors are units is a unit multiple of a member of an integral
basis. -/
theorem exists_basis_eq_unit_smul {d : ℕ} {v : Fin d → ℤ} (hv : v ≠ 0)
    (hprimitive : ∀ k : ℤ, (∀ i, k ∣ v i) → IsUnit k) :
    ∃ (b : Module.Basis (Fin d) ℤ (Fin d → ℤ)) (j : Fin d) (u : ℤ),
      IsUnit u ∧ v = u • b j := by
  let N : Submodule ℤ (Fin d → ℤ) := Submodule.span ℤ {v}
  obtain ⟨n, snf⟩ := N.smithNormalForm (Pi.basisFun ℤ (Fin d))
  have hvN : v ∈ N := Submodule.subset_span (Set.mem_singleton v)
  have hvNne : (⟨v, hvN⟩ : N) ≠ 0 := fun h ↦ hv (congr_arg Subtype.val h)
  have hrank : Module.finrank ℤ N = 1 := by
    refine finrank_eq_one ⟨v, hvN⟩ hvNne fun w ↦ ?_
    have hw : w.1 ∈ Submodule.span ℤ {v} := by simp [N, w.2]
    rw [Submodule.mem_span_singleton] at hw
    obtain ⟨c, hc⟩ := hw
    exact ⟨c, Subtype.ext hc⟩
  have hn : n = 1 := by
    rw [Module.finrank_eq_card_basis snf.bN, Fintype.card_fin] at hrank
    exact hrank
  subst n
  let c : ℤ := snf.bN.repr ⟨v, hvN⟩ 0
  let u : ℤ := c * snf.a 0
  have hvbasis : v = u • snf.bM (snf.f 0) := by
    have hvrepr := snf.bN.sum_repr ⟨v, hvN⟩
    rw [Fin.sum_univ_one] at hvrepr
    change v = u • snf.bM (snf.f 0)
    change v = (c * snf.a 0) • snf.bM (snf.f 0)
    rw [mul_smul, ← snf.snf]
    exact congr_arg Subtype.val hvrepr.symm
  refine ⟨snf.bM, snf.f 0, u, hprimitive u fun i ↦ ?_, hvbasis⟩
  exact ⟨snf.bM (snf.f 0) i, congr_fun hvbasis i⟩

/-- Coordinates on the quotient by the line through `b j`, obtained by deleting the `j`-th basis
coordinate. -/
noncomputable def basisQuotientMap {d : ℕ} (b : Module.Basis (Fin d) ℤ (Fin d → ℤ)) (j : Fin d) :
    (Fin d → ℤ) →+ (Fin (d - 1) → ℤ) where
  toFun x i := b.repr x (skipCoord j i)
  map_zero' := by
    ext i
    simp
  map_add' x y := by
    ext i
    simp

/-- The canonical lift of quotient coordinates with zero `j`-th basis coordinate. -/
noncomputable def basisQuotientLift {d : ℕ} (b : Module.Basis (Fin d) ℤ (Fin d → ℤ)) (j : Fin d)
    (y : Fin (d - 1) → ℤ) : Fin d → ℤ :=
  ∑ i, y i • b (skipCoord j i)

lemma basisQuotientMap_lift {d : ℕ} (b : Module.Basis (Fin d) ℤ (Fin d → ℤ)) (j : Fin d)
    (y : Fin (d - 1) → ℤ) : basisQuotientMap b j (basisQuotientLift b j y) = y := by
  ext i
  have hinj := skipCoord_injective j
  change b.repr (∑ c, y c • b (skipCoord j c)) (skipCoord j i) = y i
  rw [map_sum]
  simp_rw [map_smul, b.repr_self]
  change Finsupp.applyAddHom (skipCoord j i)
    (∑ c, y c • Finsupp.single (skipCoord j c) (1 : ℤ)) = y i
  rw [map_sum]
  simp_rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  refine (Finset.sum_eq_single (s := Finset.univ)
    (f := fun c : Fin (d - 1) ↦ Finsupp.applyAddHom (skipCoord j i)
      (Finsupp.single (skipCoord j c) (y c))) i
    (fun c _ hci ↦ ?_) (fun h ↦ absurd (Finset.mem_univ i) h)).trans ?_
  · rw [Finsupp.applyAddHom_apply, Finsupp.single_apply,
      if_neg fun h ↦ hci (hinj h)]
  · rw [Finsupp.applyAddHom_apply, Finsupp.single_eq_same]

/-- Two integer vectors have the same quotient coordinates exactly when their difference is an
integer multiple of the deleted basis vector. -/
lemma basisQuotientMap_eq_iff {d : ℕ} (b : Module.Basis (Fin d) ℤ (Fin d → ℤ)) (j : Fin d)
    (x y : Fin d → ℤ) :
    basisQuotientMap b j x = basisQuotientMap b j y ↔ ∃ c : ℤ, x - y = c • b j := by
  constructor
  · intro h
    have hzero : basisQuotientMap b j (x - y) = 0 := by
      rw [map_sub, h, sub_self]
    refine ⟨b.repr (x - y) j, ?_⟩
    have hsum := b.sum_repr (x - y)
    rw [Finset.sum_eq_single (s := Finset.univ)
      (f := fun i ↦ b.repr (x - y) i • b i) j (fun i _ hij ↦ by
        have hi : b.repr (x - y) i = 0 := by
          obtain ⟨k, rfl⟩ := mem_range_skipCoord hij
          exact congr_fun hzero k
        rw [hi, zero_smul]) (fun h ↦ absurd (Finset.mem_univ j) h)] at hsum
    exact hsum.symm
  · rintro ⟨c, hxy⟩
    rw [← sub_eq_zero, ← map_sub]
    rw [hxy]
    ext i
    change b.repr (c • b j) (skipCoord j i) = 0
    rw [map_smul, b.repr_self]
    simp [skipCoord_ne]

/-! ### The real quotient map

The temporary reboxing input is the set of integer points of the image of the real coefficient box.
The following base change of an integral basis supplies the real-linear projection whose restriction
to integer vectors is `basisQuotientMap`. -/

/-- An integral basis of `ℤ ^ d`, extended to a real basis of `ℝ ^ d`. -/
noncomputable def basisToReal {d : ℕ} (b : Module.Basis (Fin d) ℤ (Fin d → ℤ)) :
    Module.Basis (Fin d) ℝ (Fin d → ℝ) :=
  (b.baseChange ℝ).map (TensorProduct.piScalarRight ℤ ℝ ℝ (Fin d))

lemma basisToReal_apply {d : ℕ} (b : Module.Basis (Fin d) ℤ (Fin d → ℤ)) (i : Fin d) :
    basisToReal b i = BoxLattice.intCastHom (b i) := by
  ext k
  simp [basisToReal, BoxLattice.intCastHom_apply, Algebra.smul_def]

lemma basisToReal_repr_intCast {d : ℕ} (b : Module.Basis (Fin d) ℤ (Fin d → ℤ))
    (v : Fin d → ℤ) (i : Fin d) :
    (basisToReal b).repr (BoxLattice.intCastHom v) i = (b.repr v i : ℝ) := by
  have hcast : BoxLattice.intCastHom v =
      TensorProduct.piScalarRight ℤ ℝ ℝ (Fin d) (1 ⊗ₜ[ℤ] v) := by
    ext k
    simp [BoxLattice.intCastHom_apply, Algebra.smul_def]
  rw [hcast, basisToReal, Module.Basis.map_repr]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [Module.Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def]

/-- The real-linear extension of `basisQuotientMap`. -/
noncomputable def basisRealQuotientMap {d : ℕ}
    (b : Module.Basis (Fin d) ℤ (Fin d → ℤ)) (j : Fin d) :
    (Fin d → ℝ) →ₗ[ℝ] (Fin (d - 1) → ℝ) :=
  LinearMap.pi fun i ↦ (basisToReal b).coord (skipCoord j i)

lemma basisRealQuotientMap_intCast {d : ℕ}
    (b : Module.Basis (Fin d) ℤ (Fin d → ℤ)) (j : Fin d) (v : Fin d → ℤ) :
    basisRealQuotientMap b j (BoxLattice.intCastHom v) =
      BoxLattice.intCastHom (basisQuotientMap b j v) := by
  ext i
  rw [basisRealQuotientMap, LinearMap.pi_apply]
  change (basisToReal b).repr (BoxLattice.intCastHom v) (skipCoord j i) =
    BoxLattice.intCastHom (basisQuotientMap b j v) i
  rw [basisToReal_repr_intCast]
  rfl

lemma basisRealQuotientMap_surjective {d : ℕ}
    (b : Module.Basis (Fin d) ℤ (Fin d → ℤ)) (j : Fin d) :
    Function.Surjective (basisRealQuotientMap b j) := by
  intro y
  refine ⟨∑ i, y i • basisToReal b (skipCoord j i), ?_⟩
  ext k
  rw [basisRealQuotientMap, LinearMap.pi_apply, map_sum]
  simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
    smul_eq_mul, Finsupp.single_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hik
    rw [if_neg fun h ↦ hik (skipCoord_injective j h), mul_zero]
  · simp

/-! ### Saturated spans of integer vectors

For the full properization step one quotients by all relation directions below a fixed successive
minimum threshold. Their real span meets `ℤ ^ d` in a saturated submodule. Smith normal form has
only unit diagonal entries on such a submodule, so an adapted ambient basis consists of relation
vectors in the eliminated coordinates and honest free quotient coordinates in the remainder. -/

/-- The saturation in `ℤ ^ d` of the submodule generated by `S`: the integer vectors lying in the
real span of `S`. -/
def saturatedSpan {d : ℕ} (S : Finset (Fin d → ℤ)) : Submodule ℤ (Fin d → ℤ) where
  carrier := {v | BoxLattice.intCastHom v ∈ integerGeneratedSubspace S}
  zero_mem' := by
    change BoxLattice.intCastHom 0 ∈ integerGeneratedSubspace S
    rw [map_zero]
    exact Submodule.zero_mem _
  add_mem' {x y} hx hy := by
    change BoxLattice.intCastHom (x + y) ∈ integerGeneratedSubspace S
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  smul_mem' c x hx := by
    change BoxLattice.intCastHom (c • x) ∈ integerGeneratedSubspace S
    rw [BoxLattice.intCastHom_zsmul]
    exact Submodule.smul_mem _ (c : ℝ) hx

lemma mem_saturatedSpan {d : ℕ} {S : Finset (Fin d → ℤ)} {v : Fin d → ℤ} :
    v ∈ saturatedSpan S ↔ BoxLattice.intCastHom v ∈ integerGeneratedSubspace S := Iff.rfl

lemma subset_saturatedSpan {d : ℕ} (S : Finset (Fin d → ℤ)) :
    (S : Set (Fin d → ℤ)) ⊆ saturatedSpan S := by
  intro v hv
  change intVectorToReal v ∈ integerGeneratedSubspace S
  exact Submodule.subset_span ⟨v, hv, rfl⟩

/-- The real span of an independent finite family of integer vectors has the expected
dimension. -/
lemma finrank_integerGeneratedSubspace_image {d r : ℕ} (v : Fin r → (Fin d → ℤ))
    (hv : LinearIndependent ℤ v) :
    Module.finrank ℝ (integerGeneratedSubspace (Finset.univ.image v)) = r := by
  have hvR : LinearIndependent ℝ (fun i ↦ intVectorToReal (v i)) := by
    change LinearIndependent ℝ (fun i j ↦ (v i j : ℝ))
    have h := (linearIndependent_algebraMap_comp_iff
      (R := ℤ) (S := ℝ) (ι' := Fin d)).mpr hv
    change LinearIndependent ℝ (fun i j ↦ algebraMap ℤ ℝ (v i j)) at h
    exact h
  change Module.finrank ℝ
    (Submodule.span ℝ (intVectorToReal '' (↑(Finset.univ.image v) : Set (Fin d → ℤ)))) = r
  have hset :
      intVectorToReal '' (↑(Finset.univ.image v) : Set (Fin d → ℤ)) =
        Set.range fun i ↦ intVectorToReal (v i) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [Finset.mem_coe, Finset.mem_image] at hz
      obtain ⟨i, -, rfl⟩ := hz
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨v i, by simp, rfl⟩
  rw [hset, finrank_span_eq_card hvR, Fintype.card_fin]

/-- The saturated span and the integer lattice in its real span are the same free
`ℤ`-module. -/
noncomputable def saturatedSpanEquivSubspaceIntegerLattice {d : ℕ}
    (S : Finset (Fin d → ℤ)) :
    saturatedSpan S ≃ₗ[ℤ]
      subspaceIntegerLattice (integerGeneratedSubspace S) := by
  let f : saturatedSpan S →ₗ[ℤ]
      subspaceIntegerLattice (integerGeneratedSubspace S) := {
    toFun v :=
      ⟨⟨intVectorToReal v, v.2⟩, by
        change intVectorToReal (v : Fin d → ℤ) ∈ standardIntegerLattice d
        exact intVectorToReal_mem_standardIntegerLattice (v : Fin d → ℤ)⟩
    map_add' x y := by
      apply Subtype.ext
      apply Subtype.ext
      exact intVectorToReal_add (x : Fin d → ℤ) (y : Fin d → ℤ)
    map_smul' c x := by
      apply Subtype.ext
      apply Subtype.ext
      exact intVectorToReal_zsmul c (x : Fin d → ℤ) }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply intVectorToReal_injective
    have hxy' := congr_arg Subtype.val hxy
    exact congr_arg Subtype.val hxy'
  · intro x
    obtain ⟨v, hv⟩ := exists_intVectorToReal_of_mem_standardIntegerLattice
      (mem_standardIntegerLattice_of_mem_subspaceIntegerLattice x.2)
    refine ⟨⟨v, ?_⟩, ?_⟩
    · change intVectorToReal v ∈ integerGeneratedSubspace S
      rw [hv]
      exact x.1.2
    · apply Subtype.ext
      apply Subtype.ext
      exact hv

lemma finrank_saturatedSpan {d : ℕ} (S : Finset (Fin d → ℤ)) :
    Module.finrank ℤ (saturatedSpan S) =
      Module.finrank ℝ (integerGeneratedSubspace S) := by
  rw [(saturatedSpanEquivSubspaceIntegerLattice S).finrank_eq,
    integerGeneratedSubspace_lattice_rank]

/-- Reduction modulo an independent family: every integer point in its real span is congruent
modulo the integer span to a point in the sum of half-open fundamental intervals. The coordinate
bound below is the box form used in the finite-field saturation argument. -/
lemma exists_congr_span_isShort {d r : ℕ} {L : Fin d → ℕ} {t : ℝ}
    (v : Fin r → (Fin d → ℤ)) (hshort : ∀ j, IsShort L t (v j))
    {x : Fin d → ℤ} (hx : x ∈ saturatedSpan (Finset.univ.image v)) :
    ∃ y : Fin d → ℤ,
      x - y ∈ Submodule.span ℤ (Set.range v) ∧
        ∀ i, |(y i : ℝ)| ≤ (r : ℝ) * (t * (L i : ℝ)) := by
  have hspan :
      intVectorToReal x ∈
        Submodule.span ℝ (Set.range fun j ↦ intVectorToReal (v j)) := by
    change intVectorToReal x ∈ integerGeneratedSubspace (Finset.univ.image v) at hx
    change intVectorToReal x ∈
      Submodule.span ℝ
        (intVectorToReal '' (↑(Finset.univ.image v) : Set (Fin d → ℤ))) at hx
    have hset :
        intVectorToReal '' (↑(Finset.univ.image v) : Set (Fin d → ℤ)) =
          Set.range fun j ↦ intVectorToReal (v j) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [Finset.mem_coe, Finset.mem_image] at hw
        obtain ⟨j, -, rfl⟩ := hw
        exact Set.mem_range_self j
      · rintro ⟨j, rfl⟩
        exact ⟨v j, by simp, rfl⟩
    rwa [hset] at hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hspan
  set y : Fin d → ℤ := x - ∑ j, round (c j) • v j with hy
  refine ⟨y, ?_, fun i ↦ ?_⟩
  · rw [hy, sub_sub_cancel]
    refine Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span (Set.mem_range_self j)
  · have hycoord : (y i : ℝ) =
        ∑ j, (c j - (round (c j) : ℝ)) * (v j i : ℝ) := by
      have hci := congr_fun hc i
      change ((y i : ℤ) : ℝ) =
        ∑ j, (c j - (round (c j) : ℝ)) * (v j i : ℝ)
      rw [hy, Pi.sub_apply, Int.cast_sub]
      rw [intVectorToReal, Finset.sum_apply] at hci
      simp only [Pi.smul_apply, smul_eq_mul, intVectorToReal] at hci
      rw [Finset.sum_apply, Int.cast_sum]
      simp_rw [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
      rw [← hci]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hycoord]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun _ ↦ t * (L i : ℝ)) fun j _ ↦ ?_).trans ?_
    · rw [abs_mul]
      have hround : |c j - (round (c j) : ℝ)| ≤ 1 := (abs_sub_round (c j)).trans (by norm_num)
      have hv := hshort j i
      exact (mul_le_mul_of_nonneg_right hround (abs_nonneg (v j i : ℝ))).trans (by
        simpa only [one_mul] using hv)
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact le_rfl

/-- The translated form of `exists_congr_span_isShort`: if an integer vector differs from a real
vector `b` by the real span of the short family, it has an integral congruent representative
whose coordinates exceed those of `b` by at most the fundamental-parallelepiped bound. -/
lemma exists_congr_close_isShort {d r : ℕ} {L : Fin d → ℕ} {t : ℝ}
    (v : Fin r → (Fin d → ℤ)) (hshort : ∀ j, IsShort L t (v j))
    (z : Fin d → ℤ) (b : Fin d → ℝ)
    (hspan : intVectorToReal z - b ∈
      Submodule.span ℝ (Set.range fun j ↦ intVectorToReal (v j))) :
    ∃ y : Fin d → ℤ,
      z - y ∈ Submodule.span ℤ (Set.range v) ∧
        ∀ i, |(y i : ℝ)| ≤ |b i| + (r : ℝ) * (t * (L i : ℝ)) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hspan
  set y : Fin d → ℤ := z - ∑ j, round (c j) • v j with hy
  refine ⟨y, ?_, fun i ↦ ?_⟩
  · rw [hy, sub_sub_cancel]
    refine Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span (Set.mem_range_self j)
  · have hycoord : (y i : ℝ) =
        b i + ∑ j, (c j - (round (c j) : ℝ)) * (v j i : ℝ) := by
      have hci := congr_fun hc i
      change ((y i : ℤ) : ℝ) =
        b i + ∑ j, (c j - (round (c j) : ℝ)) * (v j i : ℝ)
      rw [hy, Pi.sub_apply, Int.cast_sub]
      simp only [Pi.sub_apply, intVectorToReal, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at hci
      rw [Finset.sum_apply, Int.cast_sum]
      simp_rw [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
      have hz : (z i : ℝ) = b i + ∑ j, c j * (v j i : ℝ) := by
        linarith
      rw [hz, add_sub_assoc, ← Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hycoord]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun _ ↦ t * (L i : ℝ)) fun j _ ↦ ?_).trans ?_
    · rw [abs_mul]
      have hround : |c j - (round (c j) : ℝ)| ≤ 1 :=
        (abs_sub_round (c j)).trans (by norm_num)
      exact (mul_le_mul_of_nonneg_right hround (abs_nonneg (v j i : ℝ))).trans (by
        simpa only [one_mul] using hshort j i)
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact le_rfl

/-- Saturation: if a nonzero integer multiple belongs to `saturatedSpan S`, so does the vector. -/
lemma mem_saturatedSpan_of_zsmul_mem {d : ℕ} {S : Finset (Fin d → ℤ)}
    {v : Fin d → ℤ} {c : ℤ} (hc : c ≠ 0) (hcv : c • v ∈ saturatedSpan S) :
    v ∈ saturatedSpan S := by
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hmem := (integerGeneratedSubspace S).smul_mem (c : ℝ)⁻¹ hcv
  rw [BoxLattice.intCastHom_zsmul, inv_smul_smul₀ hcR] at hmem
  exact hmem

/-- Every Smith coefficient of a saturated submodule is a unit. -/
lemma saturatedSpan_smithCoeff_isUnit {d n : ℕ} {S : Finset (Fin d → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin d) n) (i : Fin n) :
    IsUnit (snf.a i) := by
  have ha : snf.a i ≠ 0 := by
    intro hzero
    have h := snf.snf i
    rw [hzero, zero_smul] at h
    exact (snf.bN.ne_zero i) (Subtype.ext h)
  have hbmem : snf.bM (snf.f i) ∈ saturatedSpan S := by
    refine mem_saturatedSpan_of_zsmul_mem ha ?_
    rw [← snf.snf]
    exact (snf.bN i).2
  let y : saturatedSpan S := ⟨snf.bM (snf.f i), hbmem⟩
  have hbasis : snf.bN i = snf.a i • y := by
    exact Subtype.ext (snf.snf i)
  have hcoord := congr_arg (fun x ↦ snf.bN.repr x i) hbasis
  simp only [map_smul, snf.bN.repr_self, Finsupp.single_eq_same] at hcoord
  have hcoord' : 1 = snf.a i * snf.bN.repr y i := by
    simpa only [Finsupp.smul_apply, smul_eq_mul] using hcoord
  exact isUnit_iff_dvd_one.mpr ⟨snf.bN.repr y i, hcoord'⟩

/-- A canonical enumeration of the ambient Smith-basis indices not occupied by the saturated
summand. -/
noncomputable def smithComplementEquiv {d n : ℕ} (f : Fin n ↪ Fin d) :
    Fin (d - n) ≃ {i : Fin d // i ∉ Set.range f} :=
  Fintype.equivOfCardEq (by
    have hrange : Fintype.card {i : Fin d // i ∈ Set.range f} = n := by
      exact (Fintype.card_congr f.toEquivRange).symm.trans (Fintype.card_fin n)
    rw [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_fin, hrange])

lemma smithComplementEquiv_ne_range {d n : ℕ} (f : Fin n ↪ Fin d)
    (k : Fin (d - n)) (i : Fin n) :
    (smithComplementEquiv f k : Fin d) ≠ f i := by
  intro h
  exact (smithComplementEquiv f k).2 ⟨i, h.symm⟩

/-- Quotient coordinates associated with the free complement of a Smith-normal-form basis. -/
noncomputable def smithQuotientMap {d n : ℕ} {S : Finset (Fin d → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin d) n) :
    (Fin d → ℤ) →+ (Fin (d - n) → ℤ) where
  toFun x k := snf.bM.repr x (smithComplementEquiv snf.f k)
  map_zero' := by
    ext k
    simp
  map_add' x y := by
    ext k
    simp

/-- The lift with zero coordinates along the saturated Smith summand. -/
noncomputable def smithQuotientLift {d n : ℕ} {S : Finset (Fin d → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin d) n)
    (y : Fin (d - n) → ℤ) : Fin d → ℤ :=
  ∑ k, y k • snf.bM (smithComplementEquiv snf.f k)

lemma smithQuotientMap_lift {d n : ℕ} {S : Finset (Fin d → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin d) n)
    (y : Fin (d - n) → ℤ) :
    smithQuotientMap snf (smithQuotientLift snf y) = y := by
  ext i
  have hinj := (smithComplementEquiv snf.f).injective
  change snf.bM.repr
    (∑ k, y k • snf.bM (smithComplementEquiv snf.f k))
      (smithComplementEquiv snf.f i) = y i
  rw [map_sum]
  simp_rw [map_smul, snf.bM.repr_self]
  change Finsupp.applyAddHom (↑(smithComplementEquiv snf.f i) : Fin d)
    (∑ k, y k • Finsupp.single (↑(smithComplementEquiv snf.f k) : Fin d) (1 : ℤ)) = y i
  rw [map_sum]
  simp_rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  refine (Finset.sum_eq_single (s := Finset.univ)
    (f := fun k : Fin (d - n) ↦
      Finsupp.applyAddHom (↑(smithComplementEquiv snf.f i) : Fin d)
        (Finsupp.single (↑(smithComplementEquiv snf.f k) : Fin d) (y k))) i
    (fun k _ hki ↦ ?_) (fun h ↦ absurd (Finset.mem_univ i) h)).trans ?_
  · rw [Finsupp.applyAddHom_apply, Finsupp.single_apply,
      if_neg fun h ↦ hki (hinj (Subtype.ext h))]
  · rw [Finsupp.applyAddHom_apply, Finsupp.single_eq_same]

lemma smithQuotientMap_eq_zero_iff {d n : ℕ} {S : Finset (Fin d → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin d) n)
    (x : Fin d → ℤ) :
    smithQuotientMap snf x = 0 ↔ x ∈ saturatedSpan S := by
  constructor
  · intro hzero
    rw [← snf.bM.sum_repr x]
    refine Submodule.sum_mem _ fun k _ ↦ ?_
    rcases em (k ∈ Set.range snf.f) with ⟨i, rfl⟩ | hk
    · refine Submodule.smul_mem _ _ (mem_saturatedSpan_of_zsmul_mem
        (show snf.a i ≠ 0 by
          exact fun h ↦ (saturatedSpan_smithCoeff_isUnit snf i).ne_zero h) ?_)
      rw [← snf.snf]
      exact (snf.bN i).2
    · have hcoeff : snf.bM.repr x k = 0 := by
        obtain ⟨c, hc⟩ := (smithComplementEquiv snf.f).surjective ⟨k, hk⟩
        have hcval := congr_arg Subtype.val hc
        have hc0 := congr_fun hzero c
        change snf.bM.repr x (smithComplementEquiv snf.f c) = 0 at hc0
        rwa [hcval] at hc0
      rw [hcoeff, zero_smul]
      exact Submodule.zero_mem _
  · intro hx
    ext k
    change snf.bM.repr x (smithComplementEquiv snf.f k) = 0
    exact snf.repr_eq_zero_of_notMem_range ⟨x, hx⟩ (smithComplementEquiv snf.f k).2

lemma smithQuotientMap_eq_iff {d n : ℕ} {S : Finset (Fin d → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin d) n)
    (x y : Fin d → ℤ) :
    smithQuotientMap snf x = smithQuotientMap snf y ↔ x - y ∈ saturatedSpan S := by
  rw [← sub_eq_zero, ← map_sub, smithQuotientMap_eq_zero_iff]

/-! ### The real map for a saturated quotient -/

/-- The real-linear quotient map associated with the free complement in Smith normal form. -/
noncomputable def smithRealQuotientMap {d n : ℕ} {S : Finset (Fin d → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin d) n) :
    (Fin d → ℝ) →ₗ[ℝ] (Fin (d - n) → ℝ) :=
  LinearMap.pi fun k ↦ (basisToReal snf.bM).coord (smithComplementEquiv snf.f k)

/-- On integer vectors, the real Smith quotient is the cast of `smithQuotientMap`. -/
lemma smithRealQuotientMap_intCast {d n : ℕ} {S : Finset (Fin d → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin d) n)
    (v : Fin d → ℤ) :
    smithRealQuotientMap snf (BoxLattice.intCastHom v) =
      BoxLattice.intCastHom (smithQuotientMap snf v) := by
  ext k
  rw [smithRealQuotientMap, LinearMap.pi_apply]
  change (basisToReal snf.bM).repr (BoxLattice.intCastHom v)
      (smithComplementEquiv snf.f k) =
    BoxLattice.intCastHom (smithQuotientMap snf v) k
  rw [basisToReal_repr_intCast]
  rfl

lemma smithRealQuotientMap_surjective {d n : ℕ} {S : Finset (Fin d → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin d) n) :
    Function.Surjective (smithRealQuotientMap snf) := by
  intro y
  refine ⟨∑ k, y k • basisToReal snf.bM (smithComplementEquiv snf.f k), ?_⟩
  ext i
  rw [smithRealQuotientMap, LinearMap.pi_apply, map_sum]
  simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
    smul_eq_mul, Finsupp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    rw [if_neg fun h ↦ hki ((smithComplementEquiv snf.f).injective (Subtype.ext h)),
      mul_zero]
  · simp

/-- The kernel of the real Smith quotient is exactly the real span being divided out. -/
lemma smithRealQuotientMap_eq_zero_iff {d n : ℕ} {S : Finset (Fin d → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin d) n)
    (x : Fin d → ℝ) :
    smithRealQuotientMap snf x = 0 ↔ x ∈ integerGeneratedSubspace S := by
  constructor
  · intro hzero
    rw [← (basisToReal snf.bM).sum_repr x]
    refine Submodule.sum_mem _ fun k _ ↦ ?_
    rcases em (k ∈ Set.range snf.f) with ⟨i, rfl⟩ | hk
    · refine Submodule.smul_mem _ _ ?_
      rw [basisToReal_apply]
      change BoxLattice.intCastHom (snf.bM (snf.f i)) ∈ integerGeneratedSubspace S
      refine mem_saturatedSpan_of_zsmul_mem
        (saturatedSpan_smithCoeff_isUnit snf i).ne_zero ?_
      rw [← snf.snf]
      exact (snf.bN i).2
    · have hcoeff : (basisToReal snf.bM).repr x k = 0 := by
        obtain ⟨c, hc⟩ := (smithComplementEquiv snf.f).surjective ⟨k, hk⟩
        have hcval := congr_arg Subtype.val hc
        have hc0 := congr_fun hzero c
        change (basisToReal snf.bM).repr x (smithComplementEquiv snf.f c) = 0 at hc0
        rwa [hcval] at hc0
      rw [hcoeff, zero_smul]
      exact Submodule.zero_mem _
  · intro hx
    have hle : integerGeneratedSubspace S ≤ LinearMap.ker (smithRealQuotientMap snf) := by
      rw [integerGeneratedSubspace]
      refine Submodule.span_le.mpr ?_
      rintro z ⟨v, hv, rfl⟩
      change smithRealQuotientMap snf (BoxLattice.intCastHom v) = 0
      rw [smithRealQuotientMap_intCast]
      have hvSat : v ∈ saturatedSpan S := subset_saturatedSpan S hv
      rw [(smithQuotientMap_eq_zero_iff snf v).mpr hvSat, map_zero]
    exact LinearMap.mem_ker.mp (hle hx)

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- The steps induced on quotient coordinates by an integral basis of the coefficient lattice. -/
noncomputable def basisQuotientStep (P : GAP G)
    (b : Module.Basis (Fin P.dim) ℤ (Fin P.dim → ℤ)) (j : Fin P.dim) :
    Fin (P.dim - 1) → G :=
  fun i ↦ stepHom P (b (skipCoord j i))

/-- If the deleted basis vector is a relation, the original step homomorphism factors through the
quotient-coordinate map. -/
lemma stepHom_basisQuotientMap (P : GAP G)
    (b : Module.Basis (Fin P.dim) ℤ (Fin P.dim → ℤ)) (j : Fin P.dim)
    (hzero : stepHom P (b j) = 0) (x : Fin P.dim → ℤ) :
    stepsHom (basisQuotientStep P b j) (basisQuotientMap b j x) = stepHom P x := by
  have hcoord : basisQuotientMap b j
      (basisQuotientLift b j (basisQuotientMap b j x)) = basisQuotientMap b j x :=
    basisQuotientMap_lift b j _
  obtain ⟨c, hc⟩ := (basisQuotientMap_eq_iff b j _ _).mp hcoord
  have hlift : stepHom P (basisQuotientLift b j (basisQuotientMap b j x)) = stepHom P x := by
    have hmap := congr_arg (stepHom P) hc
    rw [map_sub, map_zsmul, hzero, smul_zero] at hmap
    exact sub_eq_zero.mp hmap
  refine Eq.trans ?_ hlift
  rw [stepsHom_apply]
  unfold basisQuotientLift
  rw [map_sum]
  simp_rw [basisQuotientStep, map_zsmul]

namespace GAP

/-- The lattice of relations among the steps of a GAP. -/
def relations (P : GAP G) : AddSubgroup (Fin P.dim → ℤ) := (stepHom P).ker

lemma mem_relations {P : GAP G} {v : Fin P.dim → ℤ} :
    v ∈ P.relations ↔ ∑ i, v i • P.step i = 0 := Iff.rfl

/-- A unit multiple of a relation is a relation only if the underlying vector is a relation. -/
lemma stepHom_basis_eq_zero_of_unit_smul_mem_relations (P : GAP G)
    {v : Fin P.dim → ℤ} (hv : v ∈ P.relations)
    (b : Module.Basis (Fin P.dim) ℤ (Fin P.dim → ℤ)) (j : Fin P.dim) (u : ℤ)
    (hu : IsUnit u) (hvbasis : v = u • b j) : stepHom P (b j) = 0 := by
  change stepHom P v = 0 at hv
  rw [hvbasis, map_zsmul] at hv
  exact hu.smul_eq_zero.mp hv

/-- In a Smith basis adapted to a saturated submodule of relations, every basis vector belonging
to the saturated summand is itself a relation. -/
lemma stepHom_smithBasis_eq_zero (P : GAP G) {d n : ℕ}
    {S : Finset (Fin d → ℤ)} (hdim : d = P.dim)
    (hrel : (saturatedSpan S).toAddSubgroup ≤ hdim ▸ P.relations)
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin d) n) (i : Fin n) :
    stepHom P (hdim ▸ snf.bM (snf.f i)) = 0 := by
  subst d
  have hmem : snf.a i • snf.bM (snf.f i) ∈ P.relations := by
    rw [← snf.snf]
    exact hrel (snf.bN i).2
  change stepHom P (snf.a i • snf.bM (snf.f i)) = 0 at hmem
  rw [map_zsmul] at hmem
  exact (saturatedSpan_smithCoeff_isUnit snf i).smul_eq_zero.mp hmem

/-- The steps on the free complement of a saturated Smith summand. -/
noncomputable def smithQuotientStep (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    Fin (P.dim - n) → G :=
  fun k ↦ stepHom P (snf.bM (smithComplementEquiv snf.f k))

/-- If the saturated summand consists of relations, the step homomorphism factors through its
Smith quotient coordinates. -/
lemma stepHom_smithQuotientMap (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n)
    (hrel : (saturatedSpan S).toAddSubgroup ≤ P.relations)
    (x : Fin P.dim → ℤ) :
    stepsHom (P.smithQuotientStep snf) (smithQuotientMap snf x) = stepHom P x := by
  have hcoord : smithQuotientMap snf
      (smithQuotientLift snf (smithQuotientMap snf x)) = smithQuotientMap snf x :=
    smithQuotientMap_lift snf _
  have hdiff : smithQuotientLift snf (smithQuotientMap snf x) - x ∈ saturatedSpan S :=
    (smithQuotientMap_eq_iff snf _ _).mp hcoord
  have hlift : stepHom P (smithQuotientLift snf (smithQuotientMap snf x)) = stepHom P x := by
    have hmap : stepHom P
        (smithQuotientLift snf (smithQuotientMap snf x) - x) = 0 := hrel hdiff
    rw [map_sub, sub_eq_zero] at hmap
    exact hmap
  refine Eq.trans ?_ hlift
  rw [stepsHom_apply]
  unfold smithQuotientLift
  rw [map_sum]
  simp_rw [smithQuotientStep, map_zsmul]

/-- If the saturated summand is the full relation lattice, the induced step homomorphism on the
free quotient is injective. -/
lemma injective_stepsHom_smithQuotientStep (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n)
    (hsub : (saturatedSpan S).toAddSubgroup ≤ P.relations)
    (hsup : P.relations ≤ (saturatedSpan S).toAddSubgroup) :
    Function.Injective (stepsHom (P.smithQuotientStep snf)) := by
  intro x y hxy
  have hlift :
      stepHom P (smithQuotientLift snf x) = stepHom P (smithQuotientLift snf y) := by
    rw [← P.stepHom_smithQuotientMap snf hsub, ← P.stepHom_smithQuotientMap snf hsub,
      smithQuotientMap_lift, smithQuotientMap_lift]
    exact hxy
  have hmem : smithQuotientLift snf x - smithQuotientLift snf y ∈ saturatedSpan S := by
    refine hsup ?_
    change stepHom P (smithQuotientLift snf x - smithQuotientLift snf y) = 0
    rw [map_sub, hlift, sub_self]
  have hmaps := (smithQuotientMap_eq_iff snf _ _).mpr hmem
  simpa only [smithQuotientMap_lift] using hmaps

lemma proper_iff (P : GAP G) :
    P.Proper ↔ ∀ v ∈ P.relations, (∀ i, |v i| < (P.length i : ℤ)) → v = 0 :=
  injective_gapMap_iff P.origin P.step P.length

lemma twoProper_iff (P : GAP G) :
    P.TwoProper ↔ ∀ v ∈ P.relations, (∀ i, |v i| < 2 * (P.length i : ℤ)) → v = 0 := by
  rw [TwoProper, injective_gapMap_iff]
  refine forall_congr' fun v ↦ imp_congr Iff.rfl (imp_congr (forall_congr' fun i ↦ ?_) Iff.rfl)
  rw [Nat.cast_mul, Nat.cast_ofNat]

/-! ## Short relations control the size of a progression -/

/-- The relations of `P` whose coefficients are bounded by the lengths of `P`. -/
def boxRelations (P : GAP G) : Finset (Fin P.dim → ℤ) :=
  (symBox P).filter fun v ↦ stepHom P v = 0

lemma mem_boxRelations {P : GAP G} {v : Fin P.dim → ℤ} :
    v ∈ P.boxRelations ↔ (∀ i, |v i| < (P.length i : ℤ)) ∧ ∑ i, v i • P.step i = 0 := by
  rw [boxRelations, Finset.mem_filter, mem_symBox]
  rfl

/-- Every fibre of the coefficient map is a translate of the short relations, so the coefficient
box is no larger than the progression times the number of short relations. -/
lemma prod_length_le_card_mul_card_boxRelations (P : GAP G) :
    ∏ i, P.length i ≤ P.carrier.card * P.boxRelations.card := by
  rw [P.carrier_eq]
  refine le_trans (le_of_eq ?_) (mul_comm P.boxRelations.card _ ▸
    Finset.card_le_mul_card_image (f := gapMap P.origin P.step P.length) Finset.univ
      P.boxRelations.card ?_)
  · rw [Finset.card_univ, Fintype.card_pi]
    simp
  · intro x hx
    obtain ⟨w₀, -, hw₀⟩ := Finset.mem_image.mp hx
    refine Finset.card_le_card_of_injOn (fun w i ↦ (w i : ℤ) - (w₀ i : ℤ)) ?_ ?_
    · intro w hw
      rw [Finset.mem_coe, Finset.mem_filter] at hw
      refine Finset.mem_coe.mpr (mem_boxRelations.mpr ⟨fun i ↦ ?_, ?_⟩)
      · have := (w i).isLt
        have := (w₀ i).isLt
        simp only [abs_lt]
        omega
      · have hxw := hw.2.trans hw₀.symm
        rw [gapMap_eq_stepsHom, gapMap_eq_stepsHom, add_right_inj] at hxw
        change stepsHom P.step ((fun i ↦ ((w i : ℕ) : ℤ)) - fun i ↦ ((w₀ i : ℕ) : ℤ)) = 0
        rw [map_sub, sub_eq_zero]
        exact hxw
    · intro a _ b _ hab
      funext i
      refine Fin.ext ?_
      have hi := congr_fun hab i
      simp only [sub_left_inj] at hi
      exact_mod_cast hi

/-! ## The geometry of numbers of the relation lattice

The two results of this section are the discrete geometry of numbers of
`Chang.GeometryOfNumbers`, read through the coefficient box of a progression. The first is
Minkowski's first theorem: a progression that is smaller than a sub-box of its coefficient box must
have a nonzero relation inside that sub-box. The second is the packing bound: a proper progression
has few relations even in the doubled box, so properness is quantitatively close to 2-properness.
-/

/-- The symmetric coefficient box is the integer box of half-widths `length i - 1`. -/
lemma symBox_eq_intBox (P : GAP G) : symBox P = intBox fun i ↦ P.length i - 1 := by
  refine Finset.ext fun v ↦ ?_
  rw [mem_symBox, mem_intBox]
  refine forall_congr' fun i ↦ ?_
  have := P.length_pos i
  omega

/-- Minkowski's first theorem for a progression: if `P` has fewer elements than a sub-box of its
coefficient box, then its steps admit a nonzero relation inside that sub-box.

This is the pigeonhole principle applied to the coefficient map, which is exactly how Blichfeldt's
lemma enters the proof of Minkowski's first theorem. -/
theorem exists_ne_zero_mem_relations (P : GAP G) {m : Fin P.dim → ℕ}
    (hm : ∀ i, m i < P.length i) (hcard : P.carrier.card < ∏ i, (m i + 1)) :
    ∃ v ∈ P.relations, v ≠ 0 ∧ ∀ i, |v i| ≤ (m i : ℤ) := by
  classical
  refine exists_ne_zero_mem_ker_of_card_lt (stepHom P) (s := P.carrier.image (· - P.origin)) ?_
    (lt_of_le_of_lt Finset.card_image_le hcard)
  intro v hv
  rw [mem_natBox] at hv
  refine Finset.mem_image.mpr ⟨P.origin + stepHom P v, ?_, add_sub_cancel_left _ _⟩
  rw [P.carrier_eq]
  refine Finset.mem_image.mpr ⟨fun i ↦ ⟨(v i).toNat, ?_⟩, Finset.mem_univ _, ?_⟩
  · have := (hv i).2
    have := hm i
    omega
  · rw [gapMap_eq_stepsHom]
    refine congr_arg (P.origin + ·) (congr_arg (stepsHom P.step) (funext fun i ↦ ?_))
    exact Int.toNat_of_nonneg (hv i).1

/-- The relations of `P` whose coefficients are bounded by twice the lengths. A progression is
2-proper exactly when `0` is the only such relation. -/
def twoBoxRelations (P : GAP G) : Finset (Fin P.dim → ℤ) :=
  (intBox fun i ↦ 2 * P.length i - 1).filter fun v ↦ stepHom P v = 0

lemma mem_twoBoxRelations {P : GAP G} {v : Fin P.dim → ℤ} :
    v ∈ P.twoBoxRelations ↔ (∀ i, |v i| < 2 * (P.length i : ℤ)) ∧ v ∈ P.relations := by
  rw [twoBoxRelations, Finset.mem_filter, mem_intBox]
  refine and_congr_left fun _ ↦ forall_congr' fun i ↦ ?_
  have := P.length_pos i
  omega

lemma twoProper_iff_forall_twoBoxRelations (P : GAP G) :
    P.TwoProper ↔ ∀ v ∈ P.twoBoxRelations, v = 0 := by
  rw [P.twoProper_iff]
  exact ⟨fun h v hv ↦ h v (mem_twoBoxRelations.mp hv).2 (mem_twoBoxRelations.mp hv).1,
    fun h v hv hlt ↦ h v (mem_twoBoxRelations.mpr ⟨hlt, hv⟩)⟩

/-- The packing bound for a progression: the relations of a proper progression inside a box of
half-widths `M` are at most `∏ (2 (M i + length i - 1) + 1) / ∏ length i` in number.

Distinct such relations differ by a nonzero relation, which properness keeps out of the coefficient
box; so the translates of the coefficient box by them are disjoint. -/
theorem card_mul_prod_length_le_of_proper (P : GAP G) (hproper : P.Proper)
    {M : Fin P.dim → ℕ} (s : Finset (Fin P.dim → ℤ)) (hs : ∀ v ∈ s, v ∈ P.relations)
    (hM : ∀ v ∈ s, ∀ i, |v i| ≤ (M i : ℤ)) :
    s.card * ∏ i, P.length i ≤ ∏ i, (2 * (M i + (P.length i - 1)) + 1) := by
  refine le_trans (le_of_eq ?_) (card_mul_prod_le_of_eq_zero_of_mem_intBox ?_ s hs hM)
  · refine congr_arg (s.card * ·) (Finset.prod_congr rfl fun i _ ↦ ?_)
    have := P.length_pos i
    omega
  · refine fun v hv hbox ↦ P.proper_iff.mp hproper v hv fun i ↦ ?_
    have := hbox i
    have := P.length_pos i
    omega

/-- A proper progression has at most `6 ^ dim` relations inside the doubled box. Properness is
therefore quantitatively close to 2-properness: only boundedly many relations, in terms of the
dimension alone, have to be removed. -/
theorem card_twoBoxRelations_le_of_proper (P : GAP G) (hproper : P.Proper) :
    P.twoBoxRelations.card ≤ 6 ^ P.dim := by
  refine Nat.le_of_mul_le_mul_right (c := ∏ i, P.length i) ?_
    (Finset.prod_pos fun i _ ↦ P.length_pos i)
  refine le_trans (P.card_mul_prod_length_le_of_proper hproper (M := fun i ↦ 2 * P.length i - 1) _
    (fun v hv ↦ (mem_twoBoxRelations.mp hv).2) fun v hv i ↦ ?_) ?_
  · have := (mem_twoBoxRelations.mp hv).1 i
    have := P.length_pos i
    omega
  · refine le_trans (Finset.prod_le_prod' (g := fun i ↦ 6 * P.length i) fun i _ ↦ ?_) (le_of_eq ?_)
    · have := P.length_pos i
      omega
    · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]

/-! ## Replacing the steps and lengths of a progression -/

/-- The GAP with prescribed dimension, origin, steps and lengths. -/
def ofData (d : ℕ) (origin : G) (step : Fin d → G) (length : Fin d → ℕ)
    (hlength : ∀ i, 0 < length i) : GAP G where
  dim := d
  carrier := Finset.univ.image (gapMap origin step length)
  origin := origin
  step := step
  length := length
  length_pos := hlength
  carrier_eq := rfl

@[simp] lemma ofData_dim (d : ℕ) (origin : G) (step : Fin d → G) (length : Fin d → ℕ)
    (hlength : ∀ i, 0 < length i) : (ofData d origin step length hlength).dim = d := rfl

@[simp] lemma ofData_length (d : ℕ) (origin : G) (step : Fin d → G) (length : Fin d → ℕ)
    (hlength : ∀ i, 0 < length i) : (ofData d origin step length hlength).length = length := rfl

lemma mem_ofData (d : ℕ) (origin : G) (step : Fin d → G) (length : Fin d → ℕ)
    (hlength : ∀ i, 0 < length i) (k : (i : Fin d) → Fin (length i)) :
    gapMap origin step length k ∈ (ofData d origin step length hlength).carrier :=
  Finset.mem_image_of_mem _ (Finset.mem_univ k)

/-- Replace the steps and lengths of a GAP, keeping its dimension and origin. -/
def reshape (P : GAP G) (step : Fin P.dim → G) (length : Fin P.dim → ℕ)
    (hlength : ∀ i, 0 < length i) : GAP G :=
  ofData P.dim P.origin step length hlength

@[simp] lemma reshape_dim (P : GAP G) (step : Fin P.dim → G) (length : Fin P.dim → ℕ)
    (hlength : ∀ i, 0 < length i) : (P.reshape step length hlength).dim = P.dim := rfl

@[simp] lemma reshape_length (P : GAP G) (step : Fin P.dim → G) (length : Fin P.dim → ℕ)
    (hlength : ∀ i, 0 < length i) : (P.reshape step length hlength).length = length := rfl

@[simp] lemma reshape_step (P : GAP G) (step : Fin P.dim → G) (length : Fin P.dim → ℕ)
    (hlength : ∀ i, 0 < length i) : (P.reshape step length hlength).step = step := rfl

lemma origin_mem_reshape (P : GAP G) (step : Fin P.dim → G) (length : Fin P.dim → ℕ)
    (hlength : ∀ i, 0 < length i) : P.origin ∈ (P.reshape step length hlength).carrier := by
  refine Finset.mem_image.mpr ⟨fun i ↦ ⟨0, hlength i⟩, Finset.mem_univ _, ?_⟩
  simp [gapMap]

/-- Multiply every length of a progression by the same positive integer. -/
def scaleLengths (P : GAP G) (k : ℕ) (hk : 0 < k) : GAP G :=
  P.reshape P.step (fun i ↦ k * P.length i) fun i ↦
    Nat.mul_pos hk (P.length_pos i)

@[simp] lemma scaleLengths_dim (P : GAP G) (k : ℕ) (hk : 0 < k) :
    (P.scaleLengths k hk).dim = P.dim := rfl

@[simp] lemma scaleLengths_length (P : GAP G) (k : ℕ) (hk : 0 < k) :
    (P.scaleLengths k hk).length = fun i ↦ k * P.length i := rfl

@[simp] lemma scaleLengths_step (P : GAP G) (k : ℕ) (hk : 0 < k) :
    (P.scaleLengths k hk).step = P.step := rfl

/-- Scaling all coefficient intervals by `k` covers the resulting progression by `k ^ dim`
translates of the original one. -/
theorem card_scaleLengths_le (P : GAP G) (k : ℕ) (hk : 0 < k) :
    (P.scaleLengths k hk).carrier.card ≤ k ^ P.dim * P.carrier.card := by
  let Q := P.scaleLengths k hk
  let block (x : Q.carrier) (i : Fin P.dim) : Fin k :=
    ⟨(Q.coefficientsFin x i : ℕ) / P.length i, by
      have hcoeff := (Q.coefficientsFin x i).isLt
      simp only [Q, scaleLengths_length] at hcoeff
      exact (Nat.div_lt_iff_lt_mul (P.length_pos i)).mpr (by
        simpa only [mul_comm] using hcoeff)⟩
  let residue (x : Q.carrier) (i : Fin P.dim) : Fin (P.length i) :=
    ⟨(Q.coefficientsFin x i : ℕ) % P.length i, Nat.mod_lt _ (P.length_pos i)⟩
  let oldPoint (x : Q.carrier) : P.carrier :=
    ⟨gapMap P.origin P.step P.length (residue x), by
      rw [P.carrier_eq]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  let encode (x : Q.carrier) : (Fin P.dim → Fin k) × P.carrier :=
    ⟨block x, oldPoint x⟩
  have hencode : Function.Injective encode := by
    intro x y hxy
    have hblock : block x = block y := congr_arg Prod.fst hxy
    have hold : (oldPoint x : G) = oldPoint y := congr_arg (fun z ↦ (z.2 : G)) hxy
    apply Subtype.ext
    rw [← Q.coefficientsFin_spec x.2, ← Q.coefficientsFin_spec y.2]
    rw [gapMap, gapMap]
    refine congr_arg (Q.origin + ·) ?_
    change ∑ i, (Q.coefficientsFin x i : ℕ) • P.step i =
      ∑ i, (Q.coefficientsFin y i : ℕ) • P.step i
    have hdecomp : ∀ z : Q.carrier,
        ∑ i, (Q.coefficientsFin z i : ℕ) • P.step i =
          ∑ i, ((block z i : ℕ) * P.length i) • P.step i +
            ∑ i, (residue z i : ℕ) • P.step i := by
      intro z
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← add_nsmul]
      refine congr_arg (· • P.step i) ?_
      rw [mul_comm]
      exact (Nat.div_add_mod (Q.coefficientsFin z i) (P.length i)).symm
    have holdstep : ∀ z : Q.carrier,
        ∑ i, (residue z i : ℕ) • P.step i = (oldPoint z : G) - P.origin := by
      intro z
      change ∑ i, (residue z i : ℕ) • P.step i =
        (P.origin + ∑ i, (residue z i : ℕ) • P.step i) - P.origin
      abel
    rw [hdecomp x, hdecomp y, hblock]
    rw [holdstep x, holdstep y]
    rw [hold]
  have hcard := Fintype.card_le_of_injective encode hencode
  simpa only [Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, Fintype.card_coe,
    Finset.prod_const, Finset.card_univ, Q, Nat.card_eq_fintype_card] using hcard

/-- The step-homomorphism image of the box dilated by `m`. -/
def boundedStepImage (P : GAP G) (m : ℕ) : Finset G :=
  (intBox fun i ↦ m * (P.length i - 1)).image (stepHom P)

/-- A dilated symmetric coefficient box has at most `(2m+1)^dim` translates of the original
progression in its image. -/
theorem card_boundedStepImage_le (P : GAP G) (m : ℕ) :
    (P.boundedStepImage m).card ≤ (2 * m + 1) ^ P.dim * P.carrier.card := by
  set k := 2 * m + 1 with hkdef
  have hk : 0 < k := by omega
  let Q := P.scaleLengths k hk
  let shift : Fin P.dim → ℤ := fun i ↦ (m * (P.length i - 1) : ℕ)
  let f : G → G := fun z ↦ P.origin + stepHom P shift + z
  have hmaps : ∀ z ∈ P.boundedStepImage m, f z ∈ Q.carrier := by
    intro z hz
    rw [boundedStepImage, Finset.mem_image] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    rw [mem_intBox] at hv
    have hcoeff : ∀ i, 0 ≤ v i + shift i ∧
        v i + shift i < (Q.length i : ℤ) := by
      intro i
      have hi := abs_le.mp (hv i)
      have hlen := P.length_pos i
      simp only [shift]
      simp only [Q, scaleLengths_length, hkdef]
      have hcast : (((P.length i - 1 : ℕ) : ℕ) : ℤ) = (P.length i : ℤ) - 1 := by
        omega
      have hmcast : ((m * (P.length i - 1) : ℕ) : ℤ) =
          (m : ℤ) * ((P.length i : ℤ) - 1) := by
        rw [Nat.cast_mul, hcast]
      rw [hmcast] at hi ⊢
      push_cast
      constructor
      · omega
      · nlinarith
    rw [Q.carrier_eq]
    refine Finset.mem_image.mpr
      ⟨fun i ↦ ⟨(v i + shift i).toNat, by
        have := hcoeff i
        omega⟩, Finset.mem_univ _, ?_⟩
    change P.origin + ∑ i : Fin P.dim, (v i + shift i).toNat • P.step i =
      P.origin + stepHom P shift + stepHom P v
    have hcast : (fun i ↦ (((v i + shift i).toNat : ℕ) : ℤ)) = v + shift := by
      funext i
      have := hcoeff i
      simp only [Pi.add_apply]
      rw [Int.toNat_of_nonneg this.1]
    rw [← stepsHom_natCast, hcast, map_add]
    unfold stepHom
    abel
  have hinj : Function.Injective f := by
    intro x y hxy
    change P.origin + stepHom P shift + x = P.origin + stepHom P shift + y at hxy
    exact add_left_cancel hxy
  refine (Finset.card_le_card_of_injOn f hmaps hinj.injOn).trans ?_
  rw [hkdef]
  exact P.card_scaleLengths_le k hk

/-- Enlarging the lengths of a progression enlarges its carrier. -/
lemma carrier_subset_reshape (P : GAP G) (length : Fin P.dim → ℕ) (hlength : ∀ i, 0 < length i)
    (hle : ∀ i, P.length i ≤ length i) :
    P.carrier ⊆ (P.reshape P.step length hlength).carrier := by
  intro x hx
  rw [P.carrier_eq, Finset.mem_image] at hx
  obtain ⟨w, -, rfl⟩ := hx
  exact Finset.mem_image.mpr
    ⟨fun i ↦ ⟨w i, (w i).isLt.trans_le (hle i)⟩, Finset.mem_univ _, rfl⟩

/-! ## Membership through integer coefficients -/

/-- Membership in a progression, in terms of integer coefficients in the coefficient box. -/
lemma mem_carrier_iff_exists_intCoeffs (P : GAP G) {x : G} :
    x ∈ P.carrier ↔ ∃ c : Fin P.dim → ℤ, (∀ i, 0 ≤ c i ∧ c i < (P.length i : ℤ)) ∧
      x = P.origin + stepsHom P.step c := by
  rw [P.carrier_eq, Finset.mem_image]
  constructor
  · rintro ⟨w, -, rfl⟩
    refine ⟨fun i ↦ ((w i : ℕ) : ℤ), fun i ↦ ⟨Int.natCast_nonneg _, ?_⟩, gapMap_eq_stepsHom _ _ _ _⟩
    change ((w i : ℕ) : ℤ) < (P.length i : ℤ)
    exact_mod_cast (w i).isLt
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun i ↦ ⟨(c i).toNat, ?_⟩, Finset.mem_univ _, ?_⟩
    · have := hc i
      omega
    · rw [gapMap_eq_stepsHom]
      refine congr_arg (P.origin + ·) (congr_arg (stepsHom P.step) (funext fun i ↦ ?_))
      exact Int.toNat_of_nonneg (hc i).1

end GAP

/-- An elementary comparison used to state properization costs uniformly. -/
lemma two_pow_le_exp (d : ℕ) : (2 : ℝ) ^ d ≤ Real.exp (((d : ℝ) + 2) ^ 3) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  refine (pow_le_pow_left₀ (by norm_num) h2 d).trans ?_
  rw [← Real.exp_nat_mul, mul_one]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [Nat.cast_nonneg (α := ℝ) d, sq_nonneg ((d : ℝ) + 2),
    pow_nonneg (Nat.cast_nonneg (α := ℝ) d) 3]

/-- A polynomial base raised to the dimension is absorbed by a cubic exponential. -/
lemma poly_pow_le_exp_cube {d : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hbound : b ≤ 12 * ((d : ℝ) + 2) ^ 2) :
    b ^ d ≤ Real.exp (12 * ((d : ℝ) + 2) ^ 3) := by
  have hX : 0 ≤ 12 * ((d : ℝ) + 2) ^ 2 := by positivity
  have hbexp : b ≤ Real.exp (12 * ((d : ℝ) + 2) ^ 2) := by
    refine hbound.trans ?_
    linarith [Real.add_one_le_exp (12 * ((d : ℝ) + 2) ^ 2)]
  refine (pow_le_pow_left₀ hb hbexp d).trans ?_
  rw [← Real.exp_nat_mul]
  refine Real.exp_le_exp.mpr ?_
  have hd : (d : ℝ) ≤ (d : ℝ) + 2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hd hX]

/-- The explicit factor produced by the shortest-direction reboxing induction is absorbed by a
cubic exponential. -/
lemma boxReboxingFactor_le_exp_cube {k d : ℕ} (hkd : k ≤ d) :
    (boxReboxingFactor k : ℝ) ≤ Real.exp (((d : ℝ) + 2) ^ 3) := by
  have hfactor :
      (boxReboxingFactor k : ℝ) ≤
        ((4 * k + 1 : ℕ) : ℝ) ^ ((k + 2) * k) := by
    exact_mod_cast boxReboxingFactor_le_pow k
  have hexpOne : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h ⊢
    exact h
  have hexpTwo : (4 : ℝ) ≤ Real.exp 2 := by
    rw [(by norm_num : (2 : ℝ) = 1 + 1), Real.exp_add]
    nlinarith [Real.exp_pos 1]
  have hexpK : (k : ℝ) + 1 ≤ Real.exp k := by
    simpa using Real.add_one_le_exp (k : ℝ)
  have hbase : ((4 * k + 1 : ℕ) : ℝ) ≤ Real.exp ((k : ℝ) + 2) := by
    rw [Real.exp_add]
    have hmul := mul_le_mul hexpK hexpTwo (by positivity) (by positivity)
    push_cast
    nlinarith
  refine hfactor.trans ((pow_le_pow_left₀ (by positivity) hbase _).trans ?_)
  rw [← Real.exp_nat_mul]
  refine Real.exp_le_exp.mpr ?_
  have hkdR : (k : ℝ) ≤ d := by exact_mod_cast hkd
  push_cast
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k)
    (sq_nonneg ((k : ℝ) + 2)),
    pow_le_pow_left₀ (by positivity) (by linarith : (k : ℝ) + 2 ≤ d + 2) 3]

/-- The complete cost of one simultaneous quotient step is cubic-exponential in the current
dimension. -/
lemma saturated_quotient_factor_le_exp_cube {r d : ℕ} (hrd : r ≤ d) :
    (boxReboxingFactor (d - r) : ℝ) *
        ((2 * (r : ℝ) + 4) * (2 * (3 * (r : ℝ) + 1) + 1)) ^ d ≤
      Real.exp (13 * ((d : ℝ) + 2) ^ 3) := by
  have hrR : (r : ℝ) ≤ d := by exact_mod_cast hrd
  have hbase : (((2 * r + 4) * (2 * (3 * r + 1) + 1) : ℕ) : ℝ) ≤
      12 * ((d : ℝ) + 2) ^ 2 := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) r, Nat.cast_nonneg (α := ℝ) d,
      sq_nonneg ((d : ℝ) - r)]
  have hrebox := boxReboxingFactor_le_exp_cube (Nat.sub_le d r)
  have hpoly := poly_pow_le_exp_cube
    (show (0 : ℝ) ≤ (((2 * r + 4) * (2 * (3 * r + 1) + 1) : ℕ) : ℝ) by positivity)
    hbase
  push_cast at hpoly
  refine (mul_le_mul hrebox hpoly (by positivity) (by positivity)).trans_eq ?_
  rw [← Real.exp_add]
  congr 1
  ring

/-- Scaling the lengths by two and checking saturation both fit into one cubic exponential. -/
lemma saturation_room_factor_le_exp_cube (d : ℕ) :
    (2 * (3 * (d : ℝ)) + 1) ^ d * (2 : ℝ) ^ d ≤
      Real.exp (13 * ((d : ℝ) + 2) ^ 3) := by
  have hbase : (((2 * (3 * d) + 1 : ℕ) : ℝ)) ≤ 12 * ((d : ℝ) + 2) ^ 2 := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) d, sq_nonneg ((d : ℝ) + 2)]
  have hsat := poly_pow_le_exp_cube
    (show (0 : ℝ) ≤ ((2 * (3 * d) + 1 : ℕ) : ℝ) by positivity) hbase
  push_cast at hsat
  refine (mul_le_mul hsat (two_pow_le_exp d) (by positivity) (by positivity)).trans_eq ?_
  rw [← Real.exp_add]
  congr 1
  ring

/-- A cubic cost at each strict dimension drop telescopes inside a quartic budget. -/
lemma cube_step_le_fourth_difference {A : ℝ} (hA : 0 ≤ A) {e d : ℕ} (hed : e < d) :
    A * ((e : ℝ) + 2) ^ 4 + A * ((d : ℝ) + 2) ^ 3 ≤
      A * ((d : ℝ) + 2) ^ 4 := by
  have heNat : e + 2 ≤ d + 1 := by omega
  have he : (e : ℝ) + 2 ≤ (d : ℝ) + 1 := by exact_mod_cast heNat
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have he0 : (0 : ℝ) ≤ (e : ℝ) + 2 := by positivity
  have hpow : ((e : ℝ) + 2) ^ 4 ≤ ((d : ℝ) + 1) ^ 4 :=
    pow_le_pow_left₀ he0 he 4
  have hdiff : ((d : ℝ) + 1) ^ 4 + ((d : ℝ) + 2) ^ 3 ≤
      ((d : ℝ) + 2) ^ 4 := by
    nlinarith [sq_nonneg ((d : ℝ) + 1), mul_nonneg hd0 (sq_nonneg ((d : ℝ) + 1))]
  nlinarith [mul_le_mul_of_nonneg_left hpow hA, mul_le_mul_of_nonneg_left hdiff hA]

/-! ## The successive minima of the relation lattice

The coefficient box of a progression is the integer box of half-widths `length i - 1`, so the
relation lattice `GAP.relations` has successive minima with respect to it. This section reads the
geometry of numbers of `Chang.GeometryOfNumbers` and the lattice point count of
`Chang.BoxLatticePoints` through that box, which is the form in which the rank reduction of
properization consumes them.

Two facts drive the saturated quotient:

* 2-properness is implied by `3 < λ₁`, which is
  `GAP.twoProper_of_three_lt_relationMinimum`, and conversely a nonzero relation is short for `λ₁`,
  which is `GAP.exists_ne_zero_relation_short`;
* the size of a progression is controlled from below by its coefficient box and the minima,
  `∏ ℓᵢ ≤ |P| ∏ᵢ (2 ^ (dim + 1) / λᵢ + 1)`
  (`GAP.prod_length_le_card_mul_prod_relationMinimum`). -/

namespace GAP

/-- The half-widths of the coefficient box of `P`. The relations of `P` inside its coefficient box
are exactly the points of `GAP.relations P` in the integer box of these half-widths. -/
def halfWidth (P : GAP G) (i : Fin P.dim) : ℕ := P.length i - 1

lemma halfWidth_pos {P : GAP G} (hlen : ∀ i, 2 ≤ P.length i) (i : Fin P.dim) :
    0 < P.halfWidth i := by
  have := hlen i
  rw [halfWidth]
  omega

lemma cast_halfWidth (P : GAP G) (i : Fin P.dim) :
    ((P.halfWidth i : ℕ) : ℝ) = (P.length i : ℝ) - 1 := by
  rw [halfWidth, Nat.cast_sub (P.length_pos i), Nat.cast_one]

lemma abs_lt_length_iff_le_halfWidth (P : GAP G) (a : ℤ) (i : Fin P.dim) :
    a < (P.length i : ℤ) ↔ a ≤ (P.halfWidth i : ℤ) := by
  have := P.length_pos i
  rw [halfWidth]
  omega

/-- The `k`-th successive minimum of the relation lattice of `P` with respect to its coefficient
box: the least dilation factor of that box whose points contain `k` independent relations. -/
def relationMinimum (P : GAP G) (k : ℕ) : ℝ := successiveMinimum P.relations P.halfWidth k

lemma relationMinimum_nonneg (P : GAP G) (k : ℕ) : 0 ≤ P.relationMinimum k :=
  successiveMinimum_nonneg _ _ _

/-! ### The relation lattice in `ZMod q` has full rank

`q` annihilates `ZMod q`, so `q ℤ ^ d` consists of relations. The relation lattice therefore has
rank `dim`, every one of the `dim` successive minima is defined by a nonempty set of dilation
factors, and the whole successive minima API — monotonicity, positivity, attainment — applies to
all of them rather than only to `λ₁`. -/

lemma single_natCast_mem_relations {q : ℕ} (P : GAP (ZMod q)) (k : Fin P.dim) :
    Pi.single k (q : ℤ) ∈ P.relations := by
  rw [mem_relations, Finset.sum_eq_single k]
  · rw [Pi.single_eq_same, zsmul_eq_mul]
    push_cast
    rw [ZMod.natCast_self, zero_mul]
  · intro i _ hik
    rw [Pi.single_eq_of_ne hik, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- The relation lattice contains `dim` independent vectors inside the `q`-dilate of the coefficient
box, namely the vectors `q eₖ`. -/
lemma exists_hasIndependentShort_dim {q : ℕ} (hq : q ≠ 0) (P : GAP (ZMod q))
    (hlen : ∀ i, 2 ≤ P.length i) :
    ∃ t, 0 ≤ t ∧ HasIndependentShort P.relations P.halfWidth P.dim t := by
  refine ⟨(q : ℝ), Nat.cast_nonneg _, fun k ↦ Pi.single k (q : ℤ), ?_,
    fun k ↦ ⟨P.single_natCast_mem_relations k, fun i ↦ ?_⟩⟩
  · refine Fintype.linearIndependent_iff.mpr fun c hc k ↦ ?_
    have hk := congr_fun hc k
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.zero_apply] at hk
    exact (mul_eq_zero.mp hk).resolve_right (Int.natCast_ne_zero.mpr hq)
  · have hm : (1 : ℝ) ≤ (P.halfWidth i : ℝ) := by exact_mod_cast halfWidth_pos hlen i
    have hq' : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
    simp only [Pi.single_apply]
    split
    · push_cast
      rw [abs_of_nonneg hq']
      nlinarith
    · rw [Int.cast_zero, abs_zero]
      positivity

lemma exists_hasIndependentShort {q : ℕ} (hq : q ≠ 0) (P : GAP (ZMod q))
    (hlen : ∀ i, 2 ≤ P.length i) {k : ℕ} (hk : k ≤ P.dim) :
    ∃ t, 0 ≤ t ∧ HasIndependentShort P.relations P.halfWidth k t := by
  obtain ⟨t, ht, h⟩ := exists_hasIndependentShort_dim hq P hlen
  exact ⟨t, ht, h.of_le hk⟩

lemma relationMinimum_mono {q : ℕ} (hq : q ≠ 0) (P : GAP (ZMod q)) (hlen : ∀ i, 2 ≤ P.length i)
    {k k' : ℕ} (hkk' : k ≤ k') (hk' : k' ≤ P.dim) :
    P.relationMinimum k ≤ P.relationMinimum k' :=
  successiveMinimum_mono hkk' (exists_hasIndependentShort hq P hlen hk')

lemma relationMinimum_pos {q : ℕ} (hq : q ≠ 0) (P : GAP (ZMod q)) (hlen : ∀ i, 2 ≤ P.length i)
    {k : ℕ} (hk : 1 ≤ k) (hkd : k ≤ P.dim) : 0 < P.relationMinimum k :=
  BoxLattice.successiveMinimum_pos hk (exists_hasIndependentShort hq P hlen hkd)

/-- The number of successive minima, among the `dim` available ones, which do not exceed `t`. -/
def shortRelationRank (P : GAP G) (t : ℝ) : ℕ :=
  ((Finset.range P.dim).filter fun j ↦ P.relationMinimum (j + 1) ≤ t).card

lemma shortRelationRank_le_dim (P : GAP G) (t : ℝ) :
    P.shortRelationRank t ≤ P.dim := by
  unfold shortRelationRank
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

/-- By monotonicity, if the `(k+1)`-st minimum is below the cutoff, the short rank is larger
than `k`. -/
lemma lt_shortRelationRank_of_relationMinimum_le {q : ℕ} (hq : q ≠ 0)
    (P : GAP (ZMod q)) (hlen : ∀ i, 2 ≤ P.length i) {k : ℕ} (hkd : k < P.dim) {t : ℝ}
    (hk : P.relationMinimum (k + 1) ≤ t) :
    k < P.shortRelationRank t := by
  have hsubset : Finset.range (k + 1) ⊆
      (Finset.range P.dim).filter fun j ↦ P.relationMinimum (j + 1) ≤ t := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    exact (P.relationMinimum_mono hq hlen (by omega) (by omega)).trans hk
  have hcard := Finset.card_le_card hsubset
  unfold shortRelationRank
  simp only [Finset.card_range] at hcard
  omega

/-- Dually, if the `(k+1)`-st minimum is above the cutoff, at most `k` minima are short. -/
lemma shortRelationRank_le_of_lt_relationMinimum {q : ℕ} (hq : q ≠ 0)
    (P : GAP (ZMod q)) (hlen : ∀ i, 2 ≤ P.length i) {k : ℕ} {t : ℝ}
    (hk : t < P.relationMinimum (k + 1)) :
    P.shortRelationRank t ≤ k := by
  have hsubset :
      ((Finset.range P.dim).filter fun j ↦ P.relationMinimum (j + 1) ≤ t) ⊆
        Finset.range k := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    rw [Finset.mem_range]
    by_contra hcon
    have hmono : P.relationMinimum (k + 1) ≤ P.relationMinimum (j + 1) :=
      P.relationMinimum_mono hq hlen (by omega) (by omega)
    linarith
  have hcard := Finset.card_le_card hsubset
  simpa only [Finset.card_range, shortRelationRank] using hcard

/-- If the first minimum is below the cutoff, the corresponding short relation space is
nontrivial. -/
lemma shortRelationRank_pos {q : ℕ} (hq : q ≠ 0) (P : GAP (ZMod q))
    (hlen : ∀ i, 2 ≤ P.length i) (hdim : 1 ≤ P.dim) {t : ℝ}
    (hmin : P.relationMinimum 1 ≤ t) :
    0 < P.shortRelationRank t := by
  simpa only [zero_add] using
    P.lt_shortRelationRank_of_relationMinimum_le hq hlen (k := 0) (by omega) hmin

/-- The first minimum after the short block is strictly larger than the cutoff. -/
lemma lt_relationMinimum_shortRelationRank_add_one {q : ℕ} (hq : q ≠ 0)
    (P : GAP (ZMod q)) (hlen : ∀ i, 2 ≤ P.length i) {t : ℝ}
    (hr : P.shortRelationRank t < P.dim) :
    t < P.relationMinimum (P.shortRelationRank t + 1) := by
  by_contra hcon
  push Not at hcon
  have := P.lt_shortRelationRank_of_relationMinimum_le hq hlen hr hcon
  omega

/-- The short rank is attained by that many independent relations inside the cutoff dilate. -/
lemma exists_hasIndependentShort_shortRelationRank {q : ℕ} (hq : q ≠ 0)
    (P : GAP (ZMod q)) (hlen : ∀ i, 2 ≤ P.length i) {t : ℝ}
    (hr : 0 < P.shortRelationRank t) :
    HasIndependentShort P.relations P.halfWidth (P.shortRelationRank t) t := by
  set r := P.shortRelationRank t with hrdef
  have hrd : r ≤ P.dim := hrdef ▸ P.shortRelationRank_le_dim t
  have hrone : 1 ≤ r := by
    rw [hrdef]
    exact hr
  have hmin : P.relationMinimum r ≤ t := by
    by_contra hcon
    push Not at hcon
    have hrle : P.shortRelationRank t ≤ r - 1 :=
      P.shortRelationRank_le_of_lt_relationMinimum hq hlen (k := r - 1) (by
        rwa [Nat.sub_add_cancel hrone])
    rw [← hrdef] at hrle
    omega
  exact (exists_witness_successiveMinimum (P.halfWidth_pos hlen)
    (P.exists_hasIndependentShort hq hlen hrd)).mono hmin

/-- Smith normal form for the saturated span of a maximal independent family below the cutoff.
The eliminated Smith rank is exactly `shortRelationRank`. -/
theorem exists_smithNormalForm_shortRelations {q : ℕ} (hq : q ≠ 0)
    (P : GAP (ZMod q)) (hlen : ∀ i, 2 ≤ P.length i) {t : ℝ}
    (hr : 0 < P.shortRelationRank t) :
    ∃ (v : Fin (P.shortRelationRank t) → (Fin P.dim → ℤ))
      (S : Finset (Fin P.dim → ℤ))
      (_snf : Module.Basis.SmithNormalForm
        (saturatedSpan S) (Fin P.dim) (P.shortRelationRank t)),
      S = Finset.univ.image v ∧
        LinearIndependent ℤ v ∧
          (∀ j, v j ∈ P.relations) ∧ ∀ j, IsShort P.halfWidth t (v j) := by
  obtain ⟨v, hindep, hv⟩ := P.exists_hasIndependentShort_shortRelationRank hq hlen hr
  set S : Finset (Fin P.dim → ℤ) := Finset.univ.image v with hS
  obtain ⟨n, snf⟩ := (saturatedSpan S).smithNormalForm (Pi.basisFun ℤ (Fin P.dim))
  have hrank : Module.finrank ℤ (saturatedSpan S) = P.shortRelationRank t := by
    rw [finrank_saturatedSpan, hS, finrank_integerGeneratedSubspace_image v hindep]
  have hn : n = P.shortRelationRank t := by
    rw [Module.finrank_eq_card_basis snf.bN, Fintype.card_fin] at hrank
    exact hrank
  subst n
  exact ⟨v, S, snf, hS, hindep, fun j ↦ (hv j).1, fun j ↦ (hv j).2⟩

/-- Smith normal form for a maximal family below the cutoff, including the case where the family
is empty. -/
theorem exists_smithNormalForm_shortRelations_all {q : ℕ} (hq : q ≠ 0)
    (P : GAP (ZMod q)) (hlen : ∀ i, 2 ≤ P.length i) {t : ℝ} :
    ∃ (v : Fin (P.shortRelationRank t) → (Fin P.dim → ℤ))
      (S : Finset (Fin P.dim → ℤ))
      (_snf : Module.Basis.SmithNormalForm
        (saturatedSpan S) (Fin P.dim) (P.shortRelationRank t)),
      S = Finset.univ.image v ∧
        LinearIndependent ℤ v ∧
          (∀ j, v j ∈ P.relations) ∧ ∀ j, IsShort P.halfWidth t (v j) := by
  by_cases hr : 0 < P.shortRelationRank t
  · exact P.exists_smithNormalForm_shortRelations hq hlen hr
  · have hrzero : P.shortRelationRank t = 0 := Nat.eq_zero_of_not_pos hr
    let v : Fin 0 → (Fin P.dim → ℤ) := Fin.elim0
    let S : Finset (Fin P.dim → ℤ) := Finset.univ.image v
    have hSempty : S = ∅ := by
      ext x
      simp [S, v]
    obtain ⟨n, snf⟩ :=
      (saturatedSpan S).smithNormalForm (Pi.basisFun ℤ (Fin P.dim))
    have hn : n = 0 := by
      rw [← Fintype.card_fin n, ← Module.finrank_eq_card_basis snf.bN,
        finrank_saturatedSpan, hSempty]
      have hspace : integerGeneratedSubspace (∅ : Finset (Fin P.dim → ℤ)) = ⊥ := by
        ext x
        simp [integerGeneratedSubspace]
      rw [hspace]
      exact finrank_bot ℝ (Fin P.dim → ℝ)
    subst n
    rw [hrzero]
    refine ⟨v, S, snf, rfl, linearIndependent_empty_type, ?_, ?_⟩
    · intro j
      exact Fin.elim0 j
    · intro j
      exact Fin.elim0 j

/-- A maximal independent family below the cutoff spans every relation below that cutoff. -/
lemma mem_saturatedSpan_shortRelations {q : ℕ} (hq : q ≠ 0)
    (P : GAP (ZMod q)) (hlen : ∀ i, 2 ≤ P.length i)
    {r : ℕ} (hr : r = P.shortRelationRank 3)
    (v : Fin r → (Fin P.dim → ℤ))
    (hindep : LinearIndependent ℤ v)
    (hvrel : ∀ j, v j ∈ P.relations)
    (hvshort : ∀ j, IsShort P.halfWidth 3 (v j))
    {w : Fin P.dim → ℤ} (hwrel : w ∈ P.relations)
    (hwshort : IsShort P.halfWidth 3 w) :
    w ∈ saturatedSpan (Finset.univ.image v) := by
  by_contra hwspan
  have hvR : LinearIndependent ℝ (fun j ↦ intVectorToReal (v j)) := by
    change LinearIndependent ℝ (fun j i ↦ (v j i : ℝ))
    have h := (linearIndependent_algebraMap_comp_iff
      (R := ℤ) (S := ℝ) (ι' := Fin P.dim)).mpr hindep
    change LinearIndependent ℝ (fun j i ↦ algebraMap ℤ ℝ (v j i)) at h
    exact h
  have hwR : intVectorToReal w ∉
      Submodule.span ℝ (Set.range fun j ↦ intVectorToReal (v j)) := by
    intro hw
    apply hwspan
    change intVectorToReal w ∈ integerGeneratedSubspace (Finset.univ.image v)
    change intVectorToReal w ∈
      Submodule.span ℝ
        (intVectorToReal '' (↑(Finset.univ.image v) : Set (Fin P.dim → ℤ)))
    have hset :
        intVectorToReal '' (↑(Finset.univ.image v) : Set (Fin P.dim → ℤ)) =
          Set.range fun j ↦ intVectorToReal (v j) := by
      ext z
      constructor
      · rintro ⟨u, hu, rfl⟩
        rw [Finset.mem_coe, Finset.mem_image] at hu
        obtain ⟨j, -, rfl⟩ := hu
        exact ⟨j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨v j, by simp, rfl⟩
    rwa [hset]
  have hconsR : LinearIndependent ℝ
      (Fin.cons (intVectorToReal w) fun j ↦ intVectorToReal (v j)) :=
    linearIndependent_finCons.mpr ⟨hvR, hwR⟩
  have hcons : LinearIndependent ℤ (Fin.cons w v) := by
    apply (linearIndependent_algebraMap_comp_iff
      (R := ℤ) (S := ℝ) (ι' := Fin P.dim)).mp
    have heq :
        (fun i : Fin (r + 1) ↦
          algebraMap ℤ ℝ ∘
            (Fin.cons w v : Fin (r + 1) → (Fin P.dim → ℤ)) i) =
          Fin.cons (intVectorToReal w) (fun j ↦ intVectorToReal (v j)) := by
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;> funext k <;> rfl
    rw [heq]
    exact hconsR
  have hrd : r < P.dim := by
    have hcard := hcons.fintype_card_le_finrank
    rw [Module.finrank_fin_fun] at hcard
    simp only [Fintype.card_fin] at hcard
    omega
  have hfamily : HasIndependentShort P.relations P.halfWidth (r + 1) 3 := by
    refine ⟨Fin.cons w v, hcons, Fin.cases ?_ fun j ↦ ?_⟩
    · exact ⟨hwrel, hwshort⟩
    · exact ⟨hvrel j, hvshort j⟩
  have hmin : P.relationMinimum (r + 1) ≤ 3 :=
    successiveMinimum_le (by norm_num) hfamily
  have := P.lt_shortRelationRank_of_relationMinimum_le hq hlen (k := r) hrd hmin
  rw [← hr] at this
  omega

/-- Multiples of a nonzero element of a prime cyclic group are distinct below the modulus. -/
lemma nsmul_left_injective_of_ne_zero {q : ℕ} (hq : Nat.Prime q) {a : ZMod q} (ha : a ≠ 0)
    {m n : ℕ} (hm : m < q) (hn : n < q) (h : m • a = n • a) : m = n := by
  haveI : Fact q.Prime := ⟨hq⟩
  rw [nsmul_eq_mul, nsmul_eq_mul] at h
  rw [← ZMod.val_cast_of_lt hm, ← ZMod.val_cast_of_lt hn, mul_right_cancel₀ ha h]

/-- In a prime cyclic group, the real span of a short independent family is already made of
relations when the progression has enough room. Otherwise the `q` multiples of a nonrelation,
reduced into a fundamental parallelepiped, would give `q` distinct elements in a bounded dilate
of the coefficient box. -/
theorem saturatedSpan_shortRelations_le_relations {q r : ℕ} (hq : Nat.Prime q)
    (P : GAP (ZMod q)) (v : Fin r → (Fin P.dim → ℤ))
    (hrel : ∀ j, v j ∈ P.relations)
    (hshort : ∀ j, IsShort P.halfWidth 3 (v j)) (hrd : r ≤ P.dim)
    (hroom : (2 * (3 * P.dim) + 1) ^ P.dim * P.carrier.card < q) :
    (saturatedSpan (Finset.univ.image v)).toAddSubgroup ≤ P.relations := by
  haveI : Fact q.Prime := ⟨hq⟩
  intro x hx
  change stepHom P x = 0
  by_contra hxne
  have hspanrel :
      Submodule.span ℤ (Set.range v) ≤
        AddSubgroup.toIntSubmodule P.relations := by
    refine Submodule.span_le.mpr ?_
    rintro w ⟨j, rfl⟩
    exact hrel j
  have hreduce : ∀ a : Fin q, ∃ y : Fin P.dim → ℤ,
      stepHom P y = (a : ℕ) • stepHom P x ∧
        y ∈ intBox (fun i ↦ 3 * P.dim * P.halfWidth i) := by
    intro a
    obtain ⟨y, hcongr, hy⟩ := exists_congr_span_isShort v hshort
      (x := (a : ℤ) • x) (Submodule.smul_mem _ _ hx)
    refine ⟨y, ?_, mem_intBox.mpr fun i ↦ ?_⟩
    · have hzero : stepHom P ((a : ℤ) • x - y) = 0 := hspanrel hcongr
      rw [map_sub, sub_eq_zero, map_zsmul] at hzero
      rw [← hzero]
      exact natCast_zsmul (stepHom P x) a
    · have hyi := hy i
      have hL : (0 : ℝ) ≤ (P.halfWidth i : ℝ) := Nat.cast_nonneg _
      have hrdR : (r : ℝ) ≤ P.dim := by exact_mod_cast hrd
      have hmul := mul_le_mul_of_nonneg_right hrdR
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hL)
      have hyr : |(y i : ℝ)| ≤
          (3 * P.dim * P.halfWidth i : ℕ) := by
        push_cast
        nlinarith
      rw [← Int.cast_abs] at hyr
      exact_mod_cast hyr
  choose y hy using hreduce
  let f : Fin q → P.boundedStepImage (3 * P.dim) :=
    fun a ↦ ⟨stepHom P (y a), by
      rw [boundedStepImage, Finset.mem_image]
      exact ⟨y a, hy a |>.2, rfl⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hmap : (a : ℕ) • stepHom P x = (b : ℕ) • stepHom P x := by
      rw [← (hy a).1, ← (hy b).1]
      exact congr_arg Subtype.val hab
    exact Fin.ext (nsmul_left_injective_of_ne_zero hq hxne a.isLt b.isLt hmap)
  have hcard : q ≤ (P.boundedStepImage (3 * P.dim)).card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_le_of_injective f hf
  exact (not_lt_of_ge (hcard.trans (P.card_boundedStepImage_le (3 * P.dim)))) hroom

/-! ### Properness through the first minimum -/

/-- A single nonzero relation is an independent short family for a large enough dilation factor,
so the first minimum of a progression with a nonzero relation is defined by a nonempty set. -/
lemma exists_hasIndependentShort_one {P : GAP G} (hlen : ∀ i, 2 ≤ P.length i)
    {v : Fin P.dim → ℤ} (hv : v ∈ P.relations) (hne : v ≠ 0) :
    ∃ t, 0 ≤ t ∧ HasIndependentShort P.relations P.halfWidth 1 t := by
  classical
  set B : ℕ := Finset.univ.sup fun i ↦ (v i).natAbs with hB
  refine ⟨(B : ℝ), Nat.cast_nonneg _, fun _ ↦ v, linearIndependent_unique_iff.mpr hne,
    fun _ ↦ ⟨hv, fun i ↦ ?_⟩⟩
  have h1 : |(v i : ℝ)| ≤ (B : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    exact_mod_cast Finset.le_sup (f := fun i ↦ (v i).natAbs) (Finset.mem_univ i)
  have h2 : (1 : ℝ) ≤ (P.halfWidth i : ℝ) := by
    exact_mod_cast halfWidth_pos hlen i
  nlinarith [Nat.cast_nonneg (α := ℝ) B, abs_nonneg (v i : ℝ)]

/-- A nonzero relation that is short for the dilation factor `t` bounds the first minimum. -/
lemma relationMinimum_one_le {P : GAP G} {v : Fin P.dim → ℤ} (hv : v ∈ P.relations) (hne : v ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) (hshort : ∀ i, |(v i : ℝ)| ≤ t * (P.halfWidth i : ℝ)) :
    P.relationMinimum 1 ≤ t :=
  successiveMinimum_le ht ⟨fun _ ↦ v, linearIndependent_unique_iff.mpr hne,
    fun _ ↦ ⟨hv, hshort⟩⟩

/-- **Minkowski's first theorem in terms of the first minimum**: a progression with fewer elements
than a sub-box of its coefficient box has a small first minimum. It is
`exists_ne_zero_mem_relations` read through `relationMinimum_one_le`. -/
theorem relationMinimum_one_le_of_card_lt (P : GAP G) {m : Fin P.dim → ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hm : ∀ i, m i < P.length i) (hmt : ∀ i, (m i : ℝ) ≤ t * (P.halfWidth i : ℝ))
    (hcard : P.carrier.card < ∏ i, (m i + 1)) : P.relationMinimum 1 ≤ t := by
  obtain ⟨v, hv, hne, hbox⟩ := P.exists_ne_zero_mem_relations hm hcard
  refine relationMinimum_one_le hv hne ht fun i ↦ ?_
  calc |(v i : ℝ)| = ((|v i| : ℤ) : ℝ) := by rw [Int.cast_abs]
    _ ≤ ((m i : ℕ) : ℝ) := by exact_mod_cast hbox i
    _ ≤ t * (P.halfWidth i : ℝ) := hmt i

/-- A progression smaller than its own coefficient box — that is, one that is not proper — has
first minimum at most `1`. -/
theorem relationMinimum_one_le_one_of_card_lt (P : GAP G)
    (hcard : P.carrier.card < ∏ i, P.length i) : P.relationMinimum 1 ≤ 1 := by
  refine P.relationMinimum_one_le_of_card_lt zero_le_one (fun i ↦ ?_) (fun i ↦ (one_mul _).ge) ?_
  · have := P.length_pos i
    rw [halfWidth]
    omega
  · refine hcard.trans_le (le_of_eq (Finset.prod_congr rfl fun i _ ↦ ?_))
    have := P.length_pos i
    rw [halfWidth]
    omega

/-- A progression whose first minimum exceeds `3` is 2-proper: a relation inside the doubled box
has `|vᵢ| ≤ 2 ℓᵢ - 1 ≤ 3 (ℓᵢ - 1)` once every length is at least two, so it is short for the
dilation factor `3`. -/
theorem twoProper_of_three_lt_relationMinimum (P : GAP G) (hlen : ∀ i, 2 ≤ P.length i)
    (hmin : 3 < P.relationMinimum 1) : P.TwoProper := by
  refine P.twoProper_iff.mpr fun v hv hlt ↦ ?_
  by_contra hne
  refine absurd (relationMinimum_one_le hv hne (by norm_num) fun i ↦ ?_) (not_le.mpr hmin)
  have hlen' : (2 : ℤ) ≤ (P.length i : ℤ) := by exact_mod_cast hlen i
  have hint : |v i| ≤ 3 * ((P.length i : ℤ) - 1) := by
    have := Int.lt_iff_add_one_le.mp (hlt i)
    linarith
  have hcast : ((3 * ((P.length i : ℤ) - 1) : ℤ) : ℝ) = 3 * (P.halfWidth i : ℝ) := by
    rw [P.cast_halfWidth]
    push_cast
    ring
  calc |(v i : ℝ)| = ((|v i| : ℤ) : ℝ) := by rw [Int.cast_abs]
    _ ≤ ((3 * ((P.length i : ℤ) - 1) : ℤ) : ℝ) := by exact_mod_cast hint
    _ = 3 * (P.halfWidth i : ℝ) := hcast

/-- The first minimum is attained: a progression with a nonzero relation has one that is short for
the dilation factor `λ₁`. This is the relation the rank reduction is driven by. -/
theorem exists_ne_zero_relation_short (P : GAP G) (hlen : ∀ i, 2 ≤ P.length i)
    {v₀ : Fin P.dim → ℤ} (hv₀ : v₀ ∈ P.relations) (hne₀ : v₀ ≠ 0) :
    ∃ v ∈ P.relations, v ≠ 0 ∧ ∀ i, |(v i : ℝ)| ≤ P.relationMinimum 1 * (P.halfWidth i : ℝ) := by
  obtain ⟨w, hindep, hw⟩ := exists_witness_successiveMinimum (halfWidth_pos hlen)
    (exists_hasIndependentShort_one hlen hv₀ hne₀)
  exact ⟨w 0, (hw 0).1, hindep.ne_zero 0, (hw 0).2⟩

/-- A progression of positive dimension in `ZMod q` has a nonzero relation, namely `q e₀`. -/
lemma exists_ne_zero_mem_relations_of_one_le_dim {q : ℕ} (hq : q ≠ 0) (P : GAP (ZMod q))
    (hdim : 1 ≤ P.dim) : ∃ v ∈ P.relations, v ≠ 0 := by
  refine ⟨Pi.single ⟨0, hdim⟩ (q : ℤ), P.single_natCast_mem_relations _, fun hzero ↦ ?_⟩
  have hval := congr_fun hzero ⟨0, hdim⟩
  rw [Pi.single_eq_same, Pi.zero_apply] at hval
  exact hq (Int.natCast_eq_zero.mp hval)

/-- **A shortest relation is primitive**: with enough room, no integer `k` of absolute value at
least two divides all the coordinates of a relation attaining the first minimum.

This is what makes the subgroup generated by such a relation *saturated* in `ℤ ^ dim`, so that the
quotient is free and `stepHom` factors through it. Without the room hypothesis it is false — in
`ZMod q` of dimension one the shortest relation is `q`, divisible by everything — and the reason it
becomes true is that a divisor `k` of a short relation is smaller than `q`, hence invertible, so
dividing by it produces a *shorter* relation rather than leaving the lattice. -/
theorem exists_primitive_relation_short_of_le {q : ℕ} (hq : Nat.Prime q) (P : GAP (ZMod q))
    (hlen : ∀ i, 2 ≤ P.length i) {t : ℝ}
    (hroom : ∀ i, t * (P.halfWidth i : ℝ) < q) (hdim : 1 ≤ P.dim)
    (hmin : P.relationMinimum 1 ≤ t) :
    ∃ v ∈ P.relations, v ≠ 0 ∧
      (∀ i, |(v i : ℝ)| ≤ P.relationMinimum 1 * (P.halfWidth i : ℝ)) ∧
      ∀ k : ℤ, (∀ i, k ∣ v i) → IsUnit k := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hq0 : q ≠ 0 := hq.pos.ne'
  obtain ⟨v₀, hv₀, hne₀⟩ := exists_ne_zero_mem_relations_of_one_le_dim hq0 P hdim
  obtain ⟨v, hv, hne, hshort⟩ := P.exists_ne_zero_relation_short hlen hv₀ hne₀
  have hminpos : 0 < P.relationMinimum 1 := P.relationMinimum_pos hq0 hlen le_rfl hdim
  -- every coordinate of `v` is smaller than `q`
  have hsmall : ∀ i, |v i| < (q : ℤ) := by
    intro i
    have hnn : (0 : ℝ) ≤ (P.halfWidth i : ℝ) := Nat.cast_nonneg _
    have hqi : t * (P.halfWidth i : ℝ) < (q : ℝ) := by simpa using hroom i
    have : |(v i : ℝ)| < (q : ℝ) := by
      nlinarith [hshort i, mul_le_mul_of_nonneg_right hmin hnn]
    rw [← Int.cast_abs] at this
    exact_mod_cast this
  refine ⟨v, hv, hne, hshort, fun k hk ↦ ?_⟩
  by_contra hcon
  rw [Int.isUnit_iff] at hcon
  push Not at hcon
  have hk0 : k ≠ 0 := fun hzero ↦ hne (funext fun i ↦ zero_dvd_iff.mp (hzero ▸ hk i))
  have hk2 : 2 ≤ |k| := by
    rcases abs_cases k with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  -- `k` is invertible modulo `q`, because it divides a coordinate of `v`
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hne
  rw [Pi.zero_apply] at hi₀
  have hkle : |k| ≤ |v i₀| :=
    Int.le_of_dvd (abs_pos.mpr hi₀) ((abs_dvd _ _).mpr ((dvd_abs _ _).mpr (hk i₀)))
  have hkq : ((k : ℤ) : ZMod q) ≠ 0 := by
    intro hzero
    have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd k q).mp hzero
    have := Int.le_of_dvd (abs_pos.mpr hk0) ((dvd_abs _ _).mpr hdvd)
    have := hsmall i₀
    omega
  -- dividing by `k` produces a shorter relation
  set w : Fin P.dim → ℤ := fun i ↦ v i / k with hw
  have hkw : ∀ i, k * w i = v i := fun i ↦ Int.mul_ediv_cancel' (hk i)
  have hwne : w ≠ 0 := fun hzero ↦ hne (funext fun i ↦ by
    rw [← hkw i, congr_fun hzero i, Pi.zero_apply, mul_zero])
  have hveq : v = k • w := funext fun i ↦ by
    rw [Pi.smul_apply, smul_eq_mul, hkw i]
  have hwrel : w ∈ P.relations := by
    have hzero : (k : ZMod q) * stepHom P w = 0 := by
      have hkv : stepHom P v = k • stepHom P w := by rw [hveq, map_zsmul]
      rw [← zsmul_eq_mul, ← hkv]
      exact hv
    exact (mul_eq_zero.mp hzero).resolve_left hkq
  have hwshort : ∀ i, |(w i : ℝ)| ≤ P.relationMinimum 1 / 2 * (P.halfWidth i : ℝ) := by
    intro i
    have hint : 2 * |w i| ≤ |v i| := by
      rw [← hkw i, abs_mul]
      nlinarith [abs_nonneg (w i), abs_nonneg k]
    have hreal : 2 * |(w i : ℝ)| ≤ |(v i : ℝ)| := by
      rw [← Int.cast_abs, ← Int.cast_abs]
      exact_mod_cast hint
    have := hshort i
    linarith
  have := relationMinimum_one_le hwrel hwne (by positivity) hwshort
  linarith

/-- The unit-threshold specialization of `exists_primitive_relation_short_of_le`. -/
theorem exists_primitive_relation_short {q : ℕ} (hq : Nat.Prime q) (P : GAP (ZMod q))
    (hlen : ∀ i, 2 ≤ P.length i) (hroom : ∀ i, P.halfWidth i < q) (hdim : 1 ≤ P.dim)
    (hmin : P.relationMinimum 1 ≤ 1) :
    ∃ v ∈ P.relations, v ≠ 0 ∧
      (∀ i, |(v i : ℝ)| ≤ P.relationMinimum 1 * (P.halfWidth i : ℝ)) ∧
      ∀ k : ℤ, (∀ i, k ∣ v i) → IsUnit k := by
  refine P.exists_primitive_relation_short_of_le hq hlen (fun i ↦ ?_) hdim hmin
  have hi : ((P.halfWidth i : ℕ) : ℝ) < (q : ℝ) := by exact_mod_cast hroom i
  simpa only [one_mul] using hi

/-! ### The projected coefficient body

Once a primitive relation has been made a basis vector, quotienting the real coefficient box along
that vector produces a symmetric convex body in one lower dimension. Its integer points, rather
than merely the images of the old integer points, are the input to reboxing. -/

/-- The image of the real coefficient box in quotient coordinates. -/
def quotientBody (P : GAP G)
    (b : Module.Basis (Fin P.dim) ℤ (Fin P.dim → ℤ)) (j : Fin P.dim) :
    Set (Fin (P.dim - 1) → ℝ) :=
  basisRealQuotientMap b j '' BoxLattice.realBox P.halfWidth

lemma convex_quotientBody (P : GAP G)
    (b : Module.Basis (Fin P.dim) ℤ (Fin P.dim → ℤ)) (j : Fin P.dim) :
    Convex ℝ (P.quotientBody b j) :=
  (BoxLattice.convex_realBox P.halfWidth).linear_image (basisRealQuotientMap b j)

lemma isCompact_quotientBody (P : GAP G)
    (b : Module.Basis (Fin P.dim) ℤ (Fin P.dim → ℤ)) (j : Fin P.dim) :
    IsCompact (P.quotientBody b j) := by
  refine (Metric.isCompact_of_isClosed_isBounded (BoxLattice.isClosed_realBox P.halfWidth)
    (BoxLattice.isBounded_realBox P.halfWidth)).image ?_
  exact LinearMap.continuous_of_finiteDimensional (basisRealQuotientMap b j)

lemma isClosed_quotientBody (P : GAP G)
    (b : Module.Basis (Fin P.dim) ℤ (Fin P.dim → ℤ)) (j : Fin P.dim) :
    IsClosed (P.quotientBody b j) :=
  (P.isCompact_quotientBody b j).isClosed

lemma isBounded_quotientBody (P : GAP G)
    (b : Module.Basis (Fin P.dim) ℤ (Fin P.dim → ℤ)) (j : Fin P.dim) :
    Bornology.IsBounded (P.quotientBody b j) :=
  (P.isCompact_quotientBody b j).isBounded

lemma quotientBody_mem_nhds (P : GAP G) (hlen : ∀ i, 2 ≤ P.length i)
    (b : Module.Basis (Fin P.dim) ℤ (Fin P.dim → ℤ)) (j : Fin P.dim) :
    P.quotientBody b j ∈ 𝓝 (0 : Fin (P.dim - 1) → ℝ) := by
  exact image_realBox_mem_nhds_of_surjective P.halfWidth
    (fun i ↦ by have hi := hlen i; rw [halfWidth]; omega)
    (basisRealQuotientMap b j) (basisRealQuotientMap_surjective b j)

lemma span_quotientBody_inter_standardLattice_eq_top
    (P : GAP G) (hlen : ∀ i, 2 ≤ P.length i)
    (b : Module.Basis (Fin P.dim) ℤ (Fin P.dim → ℤ)) (j : Fin P.dim) :
    Submodule.span ℝ
      (P.quotientBody b j ∩
        ((((⊤ : AddSubgroup (Fin (P.dim - 1) → ℤ)).map
          (BoxLattice.intCastHom :
            (Fin (P.dim - 1) → ℤ) →+ (Fin (P.dim - 1) → ℝ)))) :
              Set (Fin (P.dim - 1) → ℝ))) = ⊤ := by
  exact span_image_realBox_inter_standardLattice_eq_top P.halfWidth
    (fun i ↦ by have hi := hlen i; rw [halfWidth]; omega)
    (basisRealQuotientMap b j) (basisQuotientMap b j)
    (basisRealQuotientMap_intCast b j) (basisRealQuotientMap_surjective b j)

lemma neg_mem_quotientBody {P : GAP G}
    {b : Module.Basis (Fin P.dim) ℤ (Fin P.dim → ℤ)} {j : Fin P.dim}
    {x : Fin (P.dim - 1) → ℝ} (hx : x ∈ P.quotientBody b j) :
    -x ∈ P.quotientBody b j := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨-y, BoxLattice.neg_mem_realBox P.halfWidth y hy, ?_⟩
  exact map_neg (basisRealQuotientMap b j) y

lemma zero_mem_quotientBody (P : GAP G)
    (b : Module.Basis (Fin P.dim) ℤ (Fin P.dim → ℤ)) (j : Fin P.dim) :
    (0 : Fin (P.dim - 1) → ℝ) ∈ P.quotientBody b j := by
  refine ⟨0, fun i ↦ ?_, map_zero (basisRealQuotientMap b j)⟩
  simp only [Pi.zero_apply, abs_zero]
  positivity

/-- The integer lattice points of the projected coefficient body. -/
def quotientIntegerPoints (P : GAP G)
    (b : Module.Basis (Fin P.dim) ℤ (Fin P.dim → ℤ)) (j : Fin P.dim) :
    Set (Fin (P.dim - 1) → ℤ) :=
  {v | BoxLattice.intCastHom v ∈ P.quotientBody b j}

lemma quotientIntegerPoints_finite (P : GAP G)
    (b : Module.Basis (Fin P.dim) ℤ (Fin P.dim → ℤ)) (j : Fin P.dim) :
    (P.quotientIntegerPoints b j).Finite := by
  let L : AddSubgroup (Fin (P.dim - 1) → ℝ) :=
    (⊤ : AddSubgroup (Fin (P.dim - 1) → ℤ)).map BoxLattice.intCastHom
  letI : DiscreteTopology L := BoxLattice.discreteTopology_map ⊤
  have hinter : (P.quotientBody b j ∩ (L : Set (Fin (P.dim - 1) → ℝ))).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      (P.isBounded_quotientBody b j) AddSubgroup.isClosed_of_discrete
  refine Set.Finite.of_finite_image (f := BoxLattice.intCastHom) ?_
    BoxLattice.intCastHom_injective.injOn
  refine hinter.subset ?_
  rintro x ⟨v, hv, rfl⟩
  refine ⟨hv, AddSubgroup.mem_map.mpr ⟨v, Set.mem_univ v, rfl⟩⟩

/-- The finite set of integer points of the projected coefficient body. -/
noncomputable def quotientCoords (P : GAP G)
    (b : Module.Basis (Fin P.dim) ℤ (Fin P.dim → ℤ)) (j : Fin P.dim) :
    Finset (Fin (P.dim - 1) → ℤ) :=
  (P.quotientIntegerPoints_finite b j).toFinset

lemma mem_quotientCoords {P : GAP G}
    {b : Module.Basis (Fin P.dim) ℤ (Fin P.dim → ℤ)} {j : Fin P.dim}
    {v : Fin (P.dim - 1) → ℤ} :
    v ∈ P.quotientCoords b j ↔ BoxLattice.intCastHom v ∈ P.quotientBody b j := by
  rw [quotientCoords, Set.Finite.mem_toFinset]
  rfl

lemma zero_mem_quotientCoords (P : GAP G)
    (b : Module.Basis (Fin P.dim) ℤ (Fin P.dim → ℤ)) (j : Fin P.dim) :
    (0 : Fin (P.dim - 1) → ℤ) ∈ P.quotientCoords b j := by
  rw [mem_quotientCoords, map_zero]
  exact P.zero_mem_quotientBody b j

lemma finsetAffineDim_le_ambient' {r : ℕ} (D : Finset (Fin r → ℝ)) :
    finsetAffineDim D ≤ r := by
  unfold finsetAffineDim
  simpa using Submodule.finrank_le (affineSpan ℝ (D : Set (Fin r → ℝ))).direction

/-- The projected body's integer points form a symmetric convex progression of dimension at most
`dim - 1`. -/
lemma isSymmetricConvexProgression_quotientCoords (P : GAP G)
    (b : Module.Basis (Fin P.dim) ℤ (Fin P.dim → ℤ)) (j : Fin P.dim) :
    IsSymmetricConvexProgression (r := P.dim - 1) (P.quotientCoords b j) := by
  refine ⟨P.quotientBody b j, P.convex_quotientBody b j, fun x ↦ ⟨?_, ?_⟩,
    fun v ↦ mem_quotientCoords, finsetAffineDim_le_ambient' _⟩
  · exact neg_mem_quotientBody
  · intro hx
    simpa using neg_mem_quotientBody hx

/-- The integer points of a one-relation projected coefficient box admit the same proper
centered reboxing as the simultaneous Smith quotient. -/
theorem exists_proper_GAP_reboxing_quotientCoords (P : GAP G)
    (hlen : ∀ i, 2 ≤ P.length i)
    (b : Module.Basis (Fin P.dim) ℤ (Fin P.dim → ℤ)) (j : Fin P.dim) :
    ∃ Q : GAP (Fin (P.dim - 1) → ℤ), Q.Proper ∧
      P.quotientCoords b j ⊆ Q.carrier ∧ Q.dim = P.dim - 1 ∧
      Q.carrier.card ≤ boxReboxingFactor (P.dim - 1) *
        (P.quotientCoords b j).card := by
  refine exists_proper_GAP_reboxing_image_realBox P.halfWidth
    (fun i ↦ P.halfWidth_pos hlen i) (basisRealQuotientMap b j)
    (basisQuotientMap b j) (basisRealQuotientMap_intCast b j)
    (basisRealQuotientMap_surjective b j) (P.quotientCoords b j) ?_
  intro v
  rw [mem_quotientCoords]
  rfl

/-- Every integer point of the original symmetric coefficient box maps into the projected convex
progression. -/
lemma basisQuotientMap_mem_quotientCoords {P : GAP G}
    {b : Module.Basis (Fin P.dim) ℤ (Fin P.dim → ℤ)} {j : Fin P.dim}
    {v : Fin P.dim → ℤ} (hv : v ∈ symBox P) :
    basisQuotientMap b j v ∈ P.quotientCoords b j := by
  rw [mem_quotientCoords, ← basisRealQuotientMap_intCast]
  refine ⟨BoxLattice.intCastHom v, fun i ↦ ?_, rfl⟩
  have hi := mem_symBox.mp hv i
  have hlen := P.length_pos i
  rw [BoxLattice.intCastHom_apply, ← Int.cast_abs]
  exact_mod_cast (show |v i| ≤ (P.halfWidth i : ℤ) by
    rw [halfWidth]
    omega)

/-! ### Projecting by a saturated family -/

/-- The image of the coefficient box after quotienting by a saturated span in Smith
coordinates. -/
def smithQuotientBody (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    Set (Fin (P.dim - n) → ℝ) :=
  smithRealQuotientMap snf '' BoxLattice.realBox P.halfWidth

lemma convex_smithQuotientBody (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    Convex ℝ (P.smithQuotientBody snf) :=
  (BoxLattice.convex_realBox P.halfWidth).linear_image (smithRealQuotientMap snf)

lemma isCompact_smithQuotientBody (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    IsCompact (P.smithQuotientBody snf) := by
  refine (Metric.isCompact_of_isClosed_isBounded (BoxLattice.isClosed_realBox P.halfWidth)
    (BoxLattice.isBounded_realBox P.halfWidth)).image ?_
  exact LinearMap.continuous_of_finiteDimensional (smithRealQuotientMap snf)

lemma isBounded_smithQuotientBody (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    Bornology.IsBounded (P.smithQuotientBody snf) :=
  (P.isCompact_smithQuotientBody snf).isBounded

lemma isClosed_smithQuotientBody (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    IsClosed (P.smithQuotientBody snf) :=
  (P.isCompact_smithQuotientBody snf).isClosed

lemma smithQuotientBody_mem_nhds (P : GAP G) (hlen : ∀ i, 2 ≤ P.length i)
    {n : ℕ} {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    P.smithQuotientBody snf ∈ 𝓝 (0 : Fin (P.dim - n) → ℝ) := by
  exact image_realBox_mem_nhds_of_surjective P.halfWidth
    (fun i ↦ by have hi := hlen i; rw [halfWidth]; omega) (smithRealQuotientMap snf)
    (smithRealQuotientMap_surjective snf)

lemma span_smithQuotientBody_inter_standardLattice_eq_top
    (P : GAP G) (hlen : ∀ i, 2 ≤ P.length i)
    {n : ℕ} {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    Submodule.span ℝ
      (P.smithQuotientBody snf ∩
        ((((⊤ : AddSubgroup (Fin (P.dim - n) → ℤ)).map
          (BoxLattice.intCastHom :
            (Fin (P.dim - n) → ℤ) →+ (Fin (P.dim - n) → ℝ)))) :
              Set (Fin (P.dim - n) → ℝ))) = ⊤ := by
  exact span_image_realBox_inter_standardLattice_eq_top P.halfWidth
    (fun i ↦ by have hi := hlen i; rw [halfWidth]; omega) (smithRealQuotientMap snf)
    (smithQuotientMap snf) (smithRealQuotientMap_intCast snf)
    (smithRealQuotientMap_surjective snf)

lemma neg_mem_smithQuotientBody {P : GAP G} {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    {snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n}
    {x : Fin (P.dim - n) → ℝ} (hx : x ∈ P.smithQuotientBody snf) :
    -x ∈ P.smithQuotientBody snf := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨-y, BoxLattice.neg_mem_realBox P.halfWidth y hy, ?_⟩
  exact map_neg (smithRealQuotientMap snf) y

lemma zero_mem_smithQuotientBody (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    (0 : Fin (P.dim - n) → ℝ) ∈ P.smithQuotientBody snf := by
  refine ⟨0, fun i ↦ ?_, map_zero (smithRealQuotientMap snf)⟩
  simp only [Pi.zero_apply, abs_zero]
  positivity

/-- The integer lattice points of a saturated projected coefficient body. -/
def smithQuotientIntegerPoints (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    Set (Fin (P.dim - n) → ℤ) :=
  {v | BoxLattice.intCastHom v ∈ P.smithQuotientBody snf}

lemma smithQuotientIntegerPoints_finite (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    (P.smithQuotientIntegerPoints snf).Finite := by
  let L : AddSubgroup (Fin (P.dim - n) → ℝ) :=
    (⊤ : AddSubgroup (Fin (P.dim - n) → ℤ)).map BoxLattice.intCastHom
  letI : DiscreteTopology L := BoxLattice.discreteTopology_map ⊤
  have hinter : (P.smithQuotientBody snf ∩
      (L : Set (Fin (P.dim - n) → ℝ))).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      (P.isBounded_smithQuotientBody snf) AddSubgroup.isClosed_of_discrete
  refine Set.Finite.of_finite_image (f := BoxLattice.intCastHom) ?_
    BoxLattice.intCastHom_injective.injOn
  refine hinter.subset ?_
  rintro x ⟨v, hv, rfl⟩
  refine ⟨hv, AddSubgroup.mem_map.mpr ⟨v, Set.mem_univ v, rfl⟩⟩

/-- The finite set of integer points of a saturated projected coefficient body. -/
noncomputable def smithQuotientCoords (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    Finset (Fin (P.dim - n) → ℤ) :=
  (P.smithQuotientIntegerPoints_finite snf).toFinset

lemma mem_smithQuotientCoords {P : GAP G} {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    {snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n}
    {v : Fin (P.dim - n) → ℤ} :
    v ∈ P.smithQuotientCoords snf ↔
      BoxLattice.intCastHom v ∈ P.smithQuotientBody snf := by
  rw [smithQuotientCoords, Set.Finite.mem_toFinset]
  rfl

lemma zero_mem_smithQuotientCoords (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    (0 : Fin (P.dim - n) → ℤ) ∈ P.smithQuotientCoords snf := by
  rw [mem_smithQuotientCoords, map_zero]
  exact P.zero_mem_smithQuotientBody snf

lemma isSymmetricConvexProgression_smithQuotientCoords (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    IsSymmetricConvexProgression (r := P.dim - n) (P.smithQuotientCoords snf) := by
  refine ⟨P.smithQuotientBody snf, P.convex_smithQuotientBody snf,
    fun x ↦ ⟨?_, ?_⟩, fun v ↦ mem_smithQuotientCoords,
    finsetAffineDim_le_ambient' _⟩
  · exact neg_mem_smithQuotientBody
  · intro hx
    simpa using neg_mem_smithQuotientBody hx

/-- The integer points of a saturated projected coefficient box admit a proper centered
reboxing, with the explicit loss produced by the shortest-direction induction. -/
theorem exists_proper_GAP_reboxing_smithQuotientCoords
    (P : GAP G) (hlen : ∀ i, 2 ≤ P.length i) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    ∃ Q : GAP (Fin (P.dim - n) → ℤ), Q.Proper ∧
      P.smithQuotientCoords snf ⊆ Q.carrier ∧ Q.dim = P.dim - n ∧
      Q.carrier.card ≤ boxReboxingFactor (P.dim - n) *
        (P.smithQuotientCoords snf).card := by
  refine exists_proper_GAP_reboxing_image_realBox P.halfWidth
    (fun i ↦ P.halfWidth_pos hlen i) (smithRealQuotientMap snf)
    (smithQuotientMap snf) (smithRealQuotientMap_intCast snf)
    (smithRealQuotientMap_surjective snf) (P.smithQuotientCoords snf) ?_
  intro v
  rw [mem_smithQuotientCoords]
  rfl

/-- Original coefficient vectors map to integer points of the saturated projected body. -/
lemma smithQuotientMap_mem_smithQuotientCoords {P : GAP G} {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    {snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n}
    {v : Fin P.dim → ℤ} (hv : v ∈ symBox P) :
    smithQuotientMap snf v ∈ P.smithQuotientCoords snf := by
  rw [mem_smithQuotientCoords, ← smithRealQuotientMap_intCast]
  refine ⟨BoxLattice.intCastHom v, fun i ↦ ?_, rfl⟩
  have hi := mem_symBox.mp hv i
  have hlen := P.length_pos i
  rw [BoxLattice.intCastHom_apply, ← Int.cast_abs]
  exact_mod_cast (show |v i| ≤ (P.halfWidth i : ℤ) by
    rw [halfWidth]
    omega)

/-- Every lattice point of the projected body has an integral lift in a controlled dilate of the
original coefficient box when the quotient directions are `3`-short. -/
lemma exists_bounded_lift_smithQuotientCoords {P : GAP G} {r : ℕ}
    (v : Fin r → (Fin P.dim → ℤ)) {S : Finset (Fin P.dim → ℤ)}
    (hS : S = Finset.univ.image v)
    (hshort : ∀ j, IsShort P.halfWidth 3 (v j))
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) r)
    {y : Fin (P.dim - r) → ℤ} (hy : y ∈ P.smithQuotientCoords snf) :
    ∃ z : Fin P.dim → ℤ, smithQuotientMap snf z = y ∧
      z ∈ intBox (fun i ↦ (3 * r + 1) * P.halfWidth i) := by
  rw [mem_smithQuotientCoords] at hy
  obtain ⟨b, hb, hby⟩ := hy
  set z₀ := smithQuotientLift snf y with hz₀
  have hker : BoxLattice.intCastHom z₀ - b ∈ integerGeneratedSubspace S := by
    rw [← smithRealQuotientMap_eq_zero_iff snf, map_sub,
      smithRealQuotientMap_intCast, smithQuotientMap_lift]
    exact sub_eq_zero.mpr hby.symm
  have hspan : intVectorToReal z₀ - b ∈
      Submodule.span ℝ (Set.range fun j ↦ intVectorToReal (v j)) := by
    rw [hS, integerGeneratedSubspace] at hker
    have hset :
        intVectorToReal '' (↑(Finset.univ.image v) : Set (Fin P.dim → ℤ)) =
          Set.range fun j ↦ intVectorToReal (v j) := by
      ext x
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [Finset.mem_coe, Finset.mem_image] at hw
        obtain ⟨j, -, rfl⟩ := hw
        exact ⟨j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨v j, by simp, rfl⟩
    rwa [hset] at hker
  obtain ⟨z, hcongr, hz⟩ := exists_congr_close_isShort v hshort z₀ b hspan
  refine ⟨z, ?_, mem_intBox.mpr fun i ↦ ?_⟩
  · have hspanSat : Submodule.span ℤ (Set.range v) ≤ saturatedSpan S := by
      refine Submodule.span_le.mpr ?_
      rintro w ⟨j, rfl⟩
      apply subset_saturatedSpan S
      rw [hS, Finset.mem_coe, Finset.mem_image]
      exact ⟨j, Finset.mem_univ _, rfl⟩
    have hmaps := (smithQuotientMap_eq_iff snf z₀ z).mpr (hspanSat hcongr)
    rw [smithQuotientMap_lift] at hmaps
    exact hmaps.symm
  · have hb' : |b i| ≤ (P.halfWidth i : ℝ) := hb i
    have hz' := hz i
    have hL : (0 : ℝ) ≤ (P.halfWidth i : ℝ) := Nat.cast_nonneg _
    have hreal : |(z i : ℝ)| ≤ ((3 * r + 1) * P.halfWidth i : ℕ) := by
      push_cast
      nlinarith
    rw [← Int.cast_abs] at hreal
    exact_mod_cast hreal

/-- The image in the ambient group of the projected body's lattice points is controlled by a
bounded dilate of the original progression. -/
lemma card_image_smithQuotientCoords_le {P : GAP G} {r : ℕ}
    (v : Fin r → (Fin P.dim → ℤ)) {S : Finset (Fin P.dim → ℤ)}
    (hS : S = Finset.univ.image v)
    (hshort : ∀ j, IsShort P.halfWidth 3 (v j))
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) r)
    (hrel : (saturatedSpan S).toAddSubgroup ≤ P.relations) :
    ((P.smithQuotientCoords snf).image
      (stepsHom (P.smithQuotientStep snf))).card ≤
        (2 * (3 * r + 1) + 1) ^ P.dim * P.carrier.card := by
  refine (Finset.card_le_card ?_).trans (P.card_boundedStepImage_le (3 * r + 1))
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨z, hzmap, hz⟩ :=
    P.exists_bounded_lift_smithQuotientCoords v hS hshort snf hy
  rw [boundedStepImage, Finset.mem_image]
  refine ⟨z, hz, ?_⟩
  rw [← P.stepHom_smithQuotientMap snf hrel z, hzmap]

/-- Two projected lattice points with the same group image differ by a relation that admits a
controlled representative modulo the saturated quotient directions. -/
lemma exists_bounded_relation_of_same_smithImage {P : GAP G} {r : ℕ}
    (v : Fin r → (Fin P.dim → ℤ)) {S : Finset (Fin P.dim → ℤ)}
    (hS : S = Finset.univ.image v)
    (hshort : ∀ j, IsShort P.halfWidth 3 (v j))
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) r)
    (hrel : (saturatedSpan S).toAddSubgroup ≤ P.relations)
    {y y₀ : Fin (P.dim - r) → ℤ}
    (hy : y ∈ P.smithQuotientCoords snf) (hy₀ : y₀ ∈ P.smithQuotientCoords snf)
    (himage : stepsHom (P.smithQuotientStep snf) y =
      stepsHom (P.smithQuotientStep snf) y₀) :
    ∃ z ∈ P.relations, smithQuotientMap snf z = y - y₀ ∧
      z ∈ intBox (fun i ↦ (3 * r + 2) * P.halfWidth i) := by
  rw [mem_smithQuotientCoords] at hy hy₀
  obtain ⟨b, hb, hby⟩ := hy
  obtain ⟨b₀, hb₀, hb₀y⟩ := hy₀
  set z₀ := smithQuotientLift snf (y - y₀) with hz₀
  have hker : BoxLattice.intCastHom z₀ - (b - b₀) ∈ integerGeneratedSubspace S := by
    rw [← smithRealQuotientMap_eq_zero_iff snf, map_sub,
      smithRealQuotientMap_intCast, smithQuotientMap_lift, map_sub, map_sub]
    rw [hby, hb₀y]
    exact sub_self _
  have hspan : intVectorToReal z₀ - (b - b₀) ∈
      Submodule.span ℝ (Set.range fun j ↦ intVectorToReal (v j)) := by
    rw [hS, integerGeneratedSubspace] at hker
    have hset :
        intVectorToReal '' (↑(Finset.univ.image v) : Set (Fin P.dim → ℤ)) =
          Set.range fun j ↦ intVectorToReal (v j) := by
      ext x
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [Finset.mem_coe, Finset.mem_image] at hw
        obtain ⟨j, -, rfl⟩ := hw
        exact ⟨j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨v j, by simp, rfl⟩
    rwa [hset] at hker
  obtain ⟨z, hcongr, hz⟩ :=
    exists_congr_close_isShort v hshort z₀ (b - b₀) hspan
  have hspanSat : Submodule.span ℤ (Set.range v) ≤ saturatedSpan S := by
    refine Submodule.span_le.mpr ?_
    rintro w ⟨j, rfl⟩
    apply subset_saturatedSpan S
    rw [hS, Finset.mem_coe, Finset.mem_image]
    exact ⟨j, Finset.mem_univ _, rfl⟩
  have hzmap : smithQuotientMap snf z = y - y₀ := by
    have hmaps := (smithQuotientMap_eq_iff snf z₀ z).mpr (hspanSat hcongr)
    rw [smithQuotientMap_lift] at hmaps
    exact hmaps.symm
  refine ⟨z, ?_, hzmap, mem_intBox.mpr fun i ↦ ?_⟩
  · change stepHom P z = 0
    rw [← P.stepHom_smithQuotientMap snf hrel z, hzmap, map_sub, himage, sub_self]
  · have hb' : |b i| ≤ (P.halfWidth i : ℝ) := hb i
    have hb₀' : |b₀ i| ≤ (P.halfWidth i : ℝ) := hb₀ i
    have hz' := hz i
    have hbb₀ : |b i - b₀ i| ≤ 2 * (P.halfWidth i : ℝ) :=
      (abs_sub _ _).trans (by linarith)
    have hbb₀' : |(b - b₀) i| ≤ 2 * (P.halfWidth i : ℝ) := by
      simpa only [Pi.sub_apply] using hbb₀
    have hreal : |(z i : ℝ)| ≤ ((3 * r + 2) * P.halfWidth i : ℕ) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) (P.halfWidth i)]
    rw [← Int.cast_abs] at hreal
    exact_mod_cast hreal

/-- Fibres of the quotient step map on the projected body have dimension-only size. Distinct
representatives are separated by the `3`-box, since every `3`-short relation belongs to the
maximal saturated short span. -/
lemma card_smithQuotientCoords_fiber_le {q : ℕ} (hq : q ≠ 0)
    (P : GAP (ZMod q)) (hlen : ∀ i, 2 ≤ P.length i)
    {r : ℕ} (hr : r = P.shortRelationRank 3)
    (v : Fin r → (Fin P.dim → ℤ)) (hindep : LinearIndependent ℤ v)
    (hvrel : ∀ j, v j ∈ P.relations)
    (hvshort : ∀ j, IsShort P.halfWidth 3 (v j))
    {S : Finset (Fin P.dim → ℤ)} (hS : S = Finset.univ.image v)
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) r)
    (hrel : (saturatedSpan S).toAddSubgroup ≤ P.relations)
    (g : ZMod q) :
    ((P.smithQuotientCoords snf).filter fun y ↦
      stepsHom (P.smithQuotientStep snf) y = g).card ≤
        (2 * r + 4) ^ P.dim := by
  classical
  set F := (P.smithQuotientCoords snf).filter fun y ↦
    stepsHom (P.smithQuotientStep snf) y = g with hF
  rcases Finset.eq_empty_or_nonempty F with hFempty | ⟨y₀, hy₀F⟩
  · rw [hFempty, Finset.card_empty]
    positivity
  have hy₀ := (Finset.mem_filter.mp (hF ▸ hy₀F)).1
  have hlift : ∀ y, ∃ z : Fin P.dim → ℤ, y ∈ F →
      z ∈ P.relations ∧ smithQuotientMap snf z = y - y₀ ∧
        z ∈ intBox (fun i ↦ (3 * r + 2) * P.halfWidth i) := by
    intro y
    by_cases hyF : y ∈ F
    swap
    · exact ⟨0, fun h ↦ absurd h hyF⟩
    have hyfilter := Finset.mem_filter.mp (hF ▸ hyF)
    have hy₀filter := Finset.mem_filter.mp (hF ▸ hy₀F)
    obtain ⟨z, hzrel, hzmap, hzbox⟩ :=
      P.exists_bounded_relation_of_same_smithImage v hS hvshort snf hrel
        hyfilter.1 hy₀filter.1 (hyfilter.2.trans hy₀filter.2.symm)
    exact ⟨z, fun _ ↦ ⟨hzrel, hzmap, hzbox⟩⟩
  choose z hz using hlift
  have hzinj : Set.InjOn z F := by
    intro a ha b hb hab
    have hmaps := congr_arg (smithQuotientMap snf) hab
    rw [(hz a ha).2.1, (hz b hb).2.1, sub_left_inj] at hmaps
    exact hmaps
  set Z := F.image z with hZ
  have hZcard : Z.card = F.card := by
    rw [hZ, Finset.card_image_of_injOn hzinj]
  have hbox : ∀ u ∈ Z, ∀ i,
      |u i| ≤ (((3 * r + 2) * P.halfWidth i : ℕ) : ℤ) := by
    intro u hu i
    rw [hZ, Finset.mem_image] at hu
    obtain ⟨y, hyF, rfl⟩ := hu
    exact mem_intBox.mp (hz y hyF).2.2 i
  have hsep : ∀ u ∈ Z, ∀ w ∈ Z, u ≠ w →
      ∃ i, ((3 * P.halfWidth i : ℕ) : ℤ) < |u i - w i| := by
    intro u hu w hw huw
    rw [hZ, Finset.mem_image] at hu hw
    obtain ⟨a, haF, rfl⟩ := hu
    obtain ⟨b, hbF, rfl⟩ := hw
    by_contra hcon
    push Not at hcon
    have hdiffrel : z a - z b ∈ P.relations :=
      P.relations.sub_mem (hz a haF).1 (hz b hbF).1
    have hdiffshort : IsShort P.halfWidth 3 (z a - z b) := by
      intro i
      have hi := hcon i
      push_cast at hi
      rw [Pi.sub_apply, ← Int.cast_abs]
      exact_mod_cast hi
    have hdiffSat : z a - z b ∈ saturatedSpan S := by
      rw [hS]
      exact P.mem_saturatedSpan_shortRelations hq hlen hr v hindep hvrel hvshort
        hdiffrel hdiffshort
    have hmaps := (smithQuotientMap_eq_iff snf (z a) (z b)).mpr hdiffSat
    rw [(hz a haF).2.1, (hz b hbF).2.1, sub_left_inj] at hmaps
    exact huw (congr_arg z hmaps)
  have hpack := card_mul_prod_le_of_separated hbox hsep
  have hfactor : ∏ i : Fin P.dim,
      (2 * (((3 * r + 2) * P.halfWidth i) + 3 * P.halfWidth i) + 1) ≤
        (2 * r + 4) ^ P.dim * ∏ i : Fin P.dim, (3 * P.halfWidth i + 1) := by
    refine (Finset.prod_le_prod' (g := fun i ↦
      (2 * r + 4) * (3 * P.halfWidth i + 1)) fun i _ ↦ ?_).trans ?_
    · nlinarith [Nat.zero_le (P.halfWidth i)]
    · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
  have hmul : F.card * ∏ i : Fin P.dim, (3 * P.halfWidth i + 1) ≤
      (2 * r + 4) ^ P.dim * ∏ i : Fin P.dim, (3 * P.halfWidth i + 1) := by
    rw [← hZcard]
    exact hpack.trans hfactor
  have hden : 0 < ∏ i : Fin P.dim, (3 * P.halfWidth i + 1) := by positivity
  exact (Nat.mul_le_mul_right_iff hden).mp hmul

/-- The full projected lattice-point set is bounded by a dimension-only factor times the original
progression. This combines the bounded image estimate with the separated-fibre estimate. -/
lemma card_smithQuotientCoords_le {q : ℕ} (hq : q ≠ 0)
    (P : GAP (ZMod q)) (hlen : ∀ i, 2 ≤ P.length i)
    {r : ℕ} (hr : r = P.shortRelationRank 3)
    (v : Fin r → (Fin P.dim → ℤ)) (hindep : LinearIndependent ℤ v)
    (hvrel : ∀ j, v j ∈ P.relations)
    (hvshort : ∀ j, IsShort P.halfWidth 3 (v j))
    {S : Finset (Fin P.dim → ℤ)} (hS : S = Finset.univ.image v)
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) r)
    (hrel : (saturatedSpan S).toAddSubgroup ≤ P.relations) :
    (P.smithQuotientCoords snf).card ≤
      ((2 * r + 4) * (2 * (3 * r + 1) + 1)) ^ P.dim * P.carrier.card := by
  let φ := stepsHom (P.smithQuotientStep snf)
  have hcard : (P.smithQuotientCoords snf).card ≤
      (2 * r + 4) ^ P.dim *
        ((P.smithQuotientCoords snf).image φ).card := by
    refine Finset.card_le_mul_card_image_of_maps_to
      (f := φ) (fun y hy ↦ Finset.mem_image_of_mem _ hy) _
      fun g _ ↦ ?_
    exact P.card_smithQuotientCoords_fiber_le hq hlen hr v hindep hvrel hvshort
      hS snf hrel g
  refine hcard.trans ?_
  have himage := P.card_image_smithQuotientCoords_le v hS hvshort snf hrel
  refine (Nat.mul_le_mul_left ((2 * r + 4) ^ P.dim) himage).trans ?_
  rw [← mul_assoc, ← mul_pow]

/-- Reboxing after quotienting by a saturated family of relations gives a
progression whose dimension is the complementary Smith rank. -/
theorem exists_container_of_saturated_relations {q : ℕ} (P : GAP (ZMod q)) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n)
    (hlen : ∀ i, 2 ≤ P.length i)
    (hrel : (saturatedSpan S).toAddSubgroup ≤ P.relations) :
    ∃ Q : GAP (ZMod q), P.carrier ⊆ Q.carrier ∧ Q.dim ≤ P.dim - n ∧
      (Q.carrier.card : ℝ) ≤
        boxReboxingFactor (P.dim - n) *
          (P.smithQuotientCoords snf).card := by
  obtain ⟨P', -, hDP', hP'dim, hP'card⟩ :=
    P.exists_proper_GAP_reboxing_smithQuotientCoords hlen snf
  set Q : GAP (ZMod q) :=
    (P'.map (stepsHom (P.smithQuotientStep snf))).shift P.origin with hQ
  have hsub : P.carrier ⊆ Q.carrier := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := P.mem_carrier_iff_exists_intCoeffs.mp hx
    have hcsym : c ∈ symBox P := by
      rw [mem_symBox]
      intro i
      have := hc i
      rw [abs_of_nonneg this.1]
      omega
    have hcP' : smithQuotientMap snf c ∈ P'.carrier :=
      hDP' (smithQuotientMap_mem_smithQuotientCoords hcsym)
    have hcmap : stepsHom (P.smithQuotientStep snf) (smithQuotientMap snf c) ∈
        (P'.map (stepsHom (P.smithQuotientStep snf))).carrier :=
      Finset.mem_image_of_mem _ hcP'
    refine Finset.mem_image.mpr
      ⟨stepsHom (P.smithQuotientStep snf) (smithQuotientMap snf c), hcmap, ?_⟩
    rw [P.stepHom_smithQuotientMap snf hrel]
    change stepHom P c + P.origin = P.origin + stepHom P c
    abel
  refine ⟨Q, hsub, hP'dim.le, ?_⟩
  have hQcard : Q.carrier.card ≤ P'.carrier.card :=
    Finset.card_image_le.trans (P'.card_map_le (stepsHom (P.smithQuotientStep snf)))
  exact ((Nat.cast_le (α := ℝ)).mpr hQcard).trans (by exact_mod_cast hP'card)

/-- The simultaneous quotient rank-reduction step. All relations below the cutoff are removed at
once, their saturation consists of genuine relations by the room hypothesis, and the projected
body has dimension-only size by `card_smithQuotientCoords_le`. -/
theorem twoProper_or_exists_GAP_dim_lt {q : ℕ} (hq : Nat.Prime q)
    (P : GAP (ZMod q)) (hlen : ∀ i, 2 ≤ P.length i)
    (hroom : (2 * (3 * P.dim) + 1) ^ P.dim * P.carrier.card < q) :
    P.TwoProper ∨
      ∃ Q : GAP (ZMod q), P.carrier ⊆ Q.carrier ∧ Q.dim < P.dim ∧
        (Q.carrier.card : ℝ) ≤
          boxReboxingFactor (P.dim - P.shortRelationRank 3) *
            (((2 * P.shortRelationRank 3 + 4) *
                (2 * (3 * P.shortRelationRank 3 + 1) + 1)) ^ P.dim) *
              P.carrier.card := by
  by_cases hdim : 1 ≤ P.dim
  swap
  · refine Or.inl (P.twoProper_iff.mpr fun w _ _ ↦ funext fun i ↦ ?_)
    exact absurd i.isLt (by omega)
  by_cases hmin : 3 < P.relationMinimum 1
  · exact Or.inl (P.twoProper_of_three_lt_relationMinimum hlen hmin)
  push Not at hmin
  have hrpos : 0 < P.shortRelationRank 3 :=
    P.shortRelationRank_pos hq.ne_zero hlen hdim hmin
  obtain ⟨v, S, snf, hS, hindep, hvrel, hvshort⟩ :=
    P.exists_smithNormalForm_shortRelations hq.ne_zero hlen hrpos
  have hrd := P.shortRelationRank_le_dim 3
  have hsat : (saturatedSpan S).toAddSubgroup ≤ P.relations := by
    rw [hS]
    exact P.saturatedSpan_shortRelations_le_relations hq v hvrel hvshort hrd hroom
  obtain ⟨Q, hsub, hQdim, hQcard⟩ :=
    P.exists_container_of_saturated_relations snf hlen hsat
  refine Or.inr ⟨Q, hsub, hQdim.trans_lt (by omega), ?_⟩
  have hcoords := P.card_smithQuotientCoords_le hq.ne_zero hlen rfl
    v hindep hvrel hvshort hS snf hsat
  have hcoordsR : ((P.smithQuotientCoords snf).card : ℝ) ≤
      (((2 * P.shortRelationRank 3 + 4) *
          (2 * (3 * P.shortRelationRank 3 + 1) + 1)) ^ P.dim : ℕ) *
        P.carrier.card := by
    exact_mod_cast hcoords
  push_cast at hcoordsR
  refine hQcard.trans ?_
  refine (mul_le_mul_of_nonneg_left hcoordsR (by positivity)).trans_eq ?_
  exact (mul_assoc _ _ _).symm

/-- **The quotient construction.** Quotienting by a primitive relation and reboxing
produces a GAP of strictly smaller dimension containing the original progression. The size is
measured here against the integer points of the projected coefficient body; the remaining global
accounting is precisely a bound for this finite set in terms of `P.carrier.card`. -/
theorem exists_dim_lt_container_of_primitive_relation {q : ℕ} (P : GAP (ZMod q))
    (hlen : ∀ i, 2 ≤ P.length i)
    {v : Fin P.dim → ℤ} (hv : v ∈ P.relations) (hvne : v ≠ 0)
    (hprimitive : ∀ k : ℤ, (∀ i, k ∣ v i) → IsUnit k) (hdim : 1 ≤ P.dim) :
    ∃ (b : Module.Basis (Fin P.dim) ℤ (Fin P.dim → ℤ)) (j : Fin P.dim)
      (Q : GAP (ZMod q)), P.carrier ⊆ Q.carrier ∧ Q.dim < P.dim ∧
      (Q.carrier.card : ℝ) ≤
        boxReboxingFactor (P.dim - 1) *
          (P.quotientCoords b j).card := by
  obtain ⟨b, j, u, hu, hvbasis⟩ := exists_basis_eq_unit_smul hvne hprimitive
  have hzero : stepHom P (b j) = 0 :=
    P.stepHom_basis_eq_zero_of_unit_smul_mem_relations hv b j u hu hvbasis
  obtain ⟨P', -, hDP', hP'dim, hP'card⟩ :=
    P.exists_proper_GAP_reboxing_quotientCoords hlen b j
  set Q : GAP (ZMod q) :=
    (P'.map (stepsHom (basisQuotientStep P b j))).shift P.origin with hQ
  have hsub : P.carrier ⊆ Q.carrier := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := P.mem_carrier_iff_exists_intCoeffs.mp hx
    have hcsym : c ∈ symBox P := by
      rw [mem_symBox]
      intro i
      have := hc i
      rw [abs_of_nonneg this.1]
      omega
    have hcP' : basisQuotientMap b j c ∈ P'.carrier :=
      hDP' (basisQuotientMap_mem_quotientCoords hcsym)
    have hcmap : stepsHom (basisQuotientStep P b j) (basisQuotientMap b j c) ∈
        (P'.map (stepsHom (basisQuotientStep P b j))).carrier :=
      Finset.mem_image_of_mem _ hcP'
    refine Finset.mem_image.mpr
      ⟨stepsHom (basisQuotientStep P b j) (basisQuotientMap b j c), hcmap, ?_⟩
    rw [stepHom_basisQuotientMap P b j hzero]
    change stepHom P c + P.origin = P.origin + stepHom P c
    abel
  refine ⟨b, j, Q, hsub, hP'dim.le.trans_lt (by omega), ?_⟩
  have hQcard : Q.carrier.card ≤ P'.carrier.card :=
    Finset.card_image_le.trans (P'.card_map_le (stepsHom (basisQuotientStep P b j)))
  exact ((Nat.cast_le (α := ℝ)).mpr hQcard).trans (by exact_mod_cast hP'card)

/-- A one-relation quotient rank-reduction step: a progression with room is either already
2-proper or is contained in a reboxed progression of strictly smaller dimension. -/
theorem twoProper_or_exists_oneRelation_dim_lt {q : ℕ} (hq : Nat.Prime q)
    (P : GAP (ZMod q)) (hlen : ∀ i, 2 ≤ P.length i)
    (hroom : ∀ i, 3 * P.halfWidth i < q) :
    P.TwoProper ∨
      ∃ (b : Module.Basis (Fin P.dim) ℤ (Fin P.dim → ℤ)) (j : Fin P.dim)
        (Q : GAP (ZMod q)), P.carrier ⊆ Q.carrier ∧ Q.dim < P.dim ∧
          (Q.carrier.card : ℝ) ≤
            boxReboxingFactor (P.dim - 1) *
              (P.quotientCoords b j).card := by
  by_cases hdim : 1 ≤ P.dim
  swap
  · refine Or.inl (P.twoProper_iff.mpr fun v _ _ ↦ funext fun i ↦ ?_)
    exact absurd i.isLt (by omega)
  by_cases hmin : 3 < P.relationMinimum 1
  · exact Or.inl (P.twoProper_of_three_lt_relationMinimum hlen hmin)
  push Not at hmin
  have hroomReal : ∀ i, (3 : ℝ) * (P.halfWidth i : ℝ) < (q : ℝ) := by
    intro i
    exact_mod_cast hroom i
  obtain ⟨v, hv, hvne, -, hprimitive⟩ :=
    P.exists_primitive_relation_short_of_le hq hlen hroomReal hdim hmin
  exact Or.inr
    (P.exists_dim_lt_container_of_primitive_relation hlen hv hvne hprimitive hdim)

/-! ### The size accounting -/

lemma coe_boxRelations (P : GAP G) :
    (P.boxRelations : Set (Fin P.dim → ℤ)) =
      BoxLattice.latticeBoxPoints P.relations P.halfWidth := by
  ext v
  simp only [Finset.mem_coe, mem_boxRelations, BoxLattice.latticeBoxPoints, Set.mem_setOf_eq,
    ← mem_relations, P.abs_lt_length_iff_le_halfWidth]
  exact and_comm

/-- The number of relations inside the coefficient box, bounded by the successive minima. This is
the lattice point count `(†)` of `Chang.BoxLatticePoints`, read through a progression. -/
theorem card_boxRelations_le (P : GAP G) (hlen : ∀ i, 2 ≤ P.length i) :
    (P.boxRelations.card : ℝ) ≤
      ∏ i : Fin P.dim, ((2 : ℝ) ^ (P.dim + 1) / P.relationMinimum ((i : ℕ) + 1) + 1) := by
  have h := BoxLattice.ncard_latticeBoxPoints_le P.relations (halfWidth_pos hlen)
  rwa [← P.coe_boxRelations, Set.ncard_coe_finset] at h

/-- **The size accounting for properization**: the coefficient box of a progression is no larger
than the progression times `∏ᵢ (2 ^ (dim + 1) / λᵢ + 1)`.

Combined with `GAP.card_le_prod_length` this pins `|P|` between `∏ ℓᵢ` and
`∏ ℓᵢ / ∏ᵢ (2 ^ (dim + 1) / λᵢ + 1)`, so a progression all of whose minima are bounded below is
almost as large as its coefficient box. It is the inequality that a rank reduction has to pay
for. -/
theorem prod_length_le_card_mul_prod_relationMinimum (P : GAP G) (hlen : ∀ i, 2 ≤ P.length i) :
    ((∏ i, P.length i : ℕ) : ℝ) ≤ P.carrier.card *
      ∏ i : Fin P.dim, ((2 : ℝ) ^ (P.dim + 1) / P.relationMinimum ((i : ℕ) + 1) + 1) := by
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (P.card_boxRelations_le hlen)
    (Nat.cast_nonneg (P.carrier.card)))
  exact_mod_cast P.prod_length_le_card_mul_card_boxRelations

/-- The size accounting in terms of the first minimum alone: in `ZMod q` all the minima are at
least `λ₁`, so

`∏ ℓᵢ ≤ |P| (2 ^ (dim + 1) / λ₁ + 1) ^ dim`.

Read the other way round, a progression much smaller than its coefficient box has a small first
minimum, which identifies when the simultaneous saturated quotient must remove a nonzero
relation space. -/
theorem prod_length_le_card_mul_pow {q : ℕ} (hq : q ≠ 0) (P : GAP (ZMod q))
    (hlen : ∀ i, 2 ≤ P.length i) :
    ((∏ i, P.length i : ℕ) : ℝ) ≤ P.carrier.card *
      ((2 : ℝ) ^ (P.dim + 1) / P.relationMinimum 1 + 1) ^ P.dim := by
  refine (P.prod_length_le_card_mul_prod_relationMinimum hlen).trans ?_
  have hpow : ((2 : ℝ) ^ (P.dim + 1) / P.relationMinimum 1 + 1) ^ P.dim
      = ∏ _i : Fin P.dim, ((2 : ℝ) ^ (P.dim + 1) / P.relationMinimum 1 + 1) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hpow]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _ ↦ ?_) fun i _ ↦ ?_)
    (Nat.cast_nonneg _)
  · have := div_nonneg (le_of_lt (by positivity : (0 : ℝ) < (2 : ℝ) ^ (P.dim + 1)))
      (P.relationMinimum_nonneg ((i : ℕ) + 1))
    linarith
  · have hdim : 1 ≤ P.dim := by
      have := i.isLt
      omega
    have hpos : 0 < P.relationMinimum 1 := P.relationMinimum_pos hq hlen le_rfl hdim
    have hle : P.relationMinimum 1 ≤ P.relationMinimum ((i : ℕ) + 1) :=
      P.relationMinimum_mono hq hlen (by omega) (by have := i.isLt; omega)
    have := div_le_div_of_nonneg_left (le_of_lt (by positivity : (0 : ℝ) < (2 : ℝ) ^ (P.dim + 1)))
      hpos hle
    linarith

end GAP

/-! ## Iterated simultaneous properization -/

/-- The universal cost constant for iterated properization. -/
def properizationConstant : ℝ := 14

lemma properizationConstant_pos : 0 < properizationConstant := by
  norm_num [properizationConstant]

/-- Iterating the saturated quotient step properizes a progression. The cubic cost of each step
telescopes into a quartic exponent because the dimension decreases strictly. -/
theorem exists_twoProperGAP_container {q : ℕ} (P : GAP (ZMod q))
    (hq : Nat.Prime q)
    (hroom :
      Real.exp (properizationConstant * ((P.dim : ℝ) + 2) ^ 4) *
        P.carrier.card ≤ q) :
    ∃ Q : GAP (ZMod q), Q.TwoProper ∧ P.carrier ⊆ Q.carrier ∧
      (∀ i, 1 < Q.length i) ∧ Q.dim ≤ P.dim ∧
      (Q.carrier.card : ℝ) ≤
        Real.exp (properizationConstant * ((P.dim : ℝ) + 2) ^ 4) *
          P.carrier.card := by
  induction hdimP : P.dim using Nat.strong_induction_on generalizing P with
  | h d ih =>
      let P₂ := P.scaleLengths 2 (by omega)
      have hdim : P₂.dim = d := hdimP
      have hPsub : P.carrier ⊆ P₂.carrier := by
        exact P.carrier_subset_reshape _ (fun i ↦ Nat.mul_pos (by omega) (P.length_pos i))
          fun i ↦ by omega
      have hP₂len : ∀ i, 2 ≤ P₂.length i := by
        intro i
        have hi := P₂.length_pos i
        simp only [P₂, GAP.scaleLengths_length]
        simp only [P₂, GAP.scaleLengths_length] at hi
        omega
      have hP₂cardNat : P₂.carrier.card ≤ 2 ^ d * P.carrier.card := by
        simpa only [P₂, hdimP] using P.card_scaleLengths_le 2 (by omega)
      have hP₂card :
          (P₂.carrier.card : ℝ) ≤ Real.exp (((d : ℝ) + 2) ^ 3) * P.carrier.card := by
        refine (Nat.cast_le.mpr hP₂cardNat).trans ?_
        push_cast
        exact mul_le_mul_of_nonneg_right (two_pow_le_exp d) (Nat.cast_nonneg _)
      have hstepRoom : (2 * (3 * P₂.dim) + 1) ^ P₂.dim * P₂.carrier.card < q := by
        have hfactor := saturation_room_factor_le_exp_cube d
        have hfactorCard :
            ((((2 * (3 * d) + 1) ^ d * P₂.carrier.card : ℕ) : ℝ)) ≤
              Real.exp (13 * ((d : ℝ) + 2) ^ 3) * P.carrier.card := by
          rw [Nat.cast_mul]
          refine (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hP₂cardNat)
            (Nat.cast_nonneg _)).trans ?_
          rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, ← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
          simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hfactor
        have hexp :
            Real.exp (13 * ((d : ℝ) + 2) ^ 3) <
              Real.exp (properizationConstant * ((d : ℝ) + 2) ^ 4) := by
          refine Real.exp_lt_exp.mpr ?_
          have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          have hx : (1 : ℝ) < (d : ℝ) + 2 := by linarith
          have hpow : ((d : ℝ) + 2) ^ 3 < ((d : ℝ) + 2) ^ 4 := by
            rw [pow_succ]
            nlinarith [pow_pos (show (0 : ℝ) < (d : ℝ) + 2 by positivity) 3]
          rw [properizationConstant]
          nlinarith [pow_pos (show (0 : ℝ) < (d : ℝ) + 2 by positivity) 4]
        have hstrict :
            Real.exp (13 * ((d : ℝ) + 2) ^ 3) * P.carrier.card <
              Real.exp (properizationConstant * ((d : ℝ) + 2) ^ 4) *
                P.carrier.card := by
          exact mul_lt_mul_of_pos_right hexp (by exact_mod_cast P.nonempty.card_pos)
        have hreal :
            ((((2 * (3 * d) + 1) ^ d * P₂.carrier.card : ℕ) : ℝ)) < (q : ℝ) :=
          hfactorCard.trans_lt (hstrict.trans_le (by simpa only [hdimP] using hroom))
        simpa only [hdim] using (show
          (2 * (3 * d) + 1) ^ d * P₂.carrier.card < q by exact_mod_cast hreal)
      rcases P₂.twoProper_or_exists_GAP_dim_lt hq hP₂len hstepRoom with
        hproper | ⟨Q, hP₂sub, hQdim, hQcard⟩
      · refine ⟨P₂, hproper, hPsub, ?_, hdim.le, ?_⟩
        · intro i
          exact lt_of_lt_of_le (by omega) (hP₂len i)
        · refine hP₂card.trans ?_
          refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (Nat.cast_nonneg _)
          have hA1 : 1 ≤ properizationConstant := by
            norm_num [properizationConstant]
          have hpow : ((d : ℝ) + 2) ^ 3 ≤ ((d : ℝ) + 2) ^ 4 := by
            rw [pow_succ]
            nlinarith [pow_nonneg (show (0 : ℝ) ≤ (d : ℝ) + 2 by positivity) 3]
          exact (le_mul_of_one_le_left (by positivity) hA1).trans
            (mul_le_mul_of_nonneg_left hpow properizationConstant_pos.le)
      · have hrank := P₂.shortRelationRank_le_dim 3
        have hfactor :=
          saturated_quotient_factor_le_exp_cube hrank
        have hQcard' :
            (Q.carrier.card : ℝ) ≤
              Real.exp (properizationConstant * ((d : ℝ) + 2) ^ 3) *
                P.carrier.card := by
          refine hQcard.trans ?_
          have hmul := mul_le_mul hfactor hP₂card (by positivity) (by positivity)
          refine hmul.trans_eq ?_
          rw [hdim, ← mul_assoc, ← Real.exp_add]
          rw [properizationConstant]
          congr 1
          ring_nf
        have hQroom :
            Real.exp (properizationConstant * ((Q.dim : ℝ) + 2) ^ 4) *
                Q.carrier.card ≤ q := by
          refine (mul_le_mul_of_nonneg_left hQcard' (by positivity)).trans ?_
          rw [← mul_assoc, ← Real.exp_add]
          refine (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_)
            (Nat.cast_nonneg _)).trans hroom
          simpa only [hdim, hdimP] using
            cube_step_le_fourth_difference properizationConstant_pos.le hQdim
        obtain ⟨R, hRproper, hQRsub, hRlen, hRdim, hRcard⟩ :=
          ih Q.dim (by simpa only [hdim] using hQdim) Q hQroom rfl
        refine ⟨R, hRproper, hPsub.trans (hP₂sub.trans hQRsub), hRlen,
          hRdim.trans (Nat.le_of_lt (by simpa only [hdim] using hQdim)), ?_⟩
        refine hRcard.trans ?_
        refine (mul_le_mul_of_nonneg_left hQcard' (by positivity)).trans ?_
        rw [← mul_assoc, ← Real.exp_add]
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (Nat.cast_nonneg _)
        simpa only [hdim, hdimP] using
          cube_step_le_fourth_difference properizationConstant_pos.le hQdim

end

end DenseSetsWithoutLargeSumsets
