/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.Chang.ConvexGeometry
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.Chang.GeometryOfNumbers

/-! # The lattice point count for a box of integer points

`Chang.ConvexGeometry` bounds the number of points of a discrete subgroup of a real normed space
inside a symmetric convex body by `∏ᵢ (2 ^ (d + 1) / λᵢ + 1)`, where the `λᵢ` are the successive
minima of the subgroup with respect to the body. This file transports that bound to the setting in
which properization consumes it: a subgroup `Λ` of `ℤ ^ d` and the box of half-widths `L`, with the
successive minima of `Chang.GeometryOfNumbers`. It is the statement `(†)` that the rank reduction
of properization consumes.

The transport is along the coordinatewise inclusion `intCastHom : ℤ ^ d → ℝ ^ d`:

- `realBox` is the real box of half-widths `L`, and `convex_realBox`, `isClosed_realBox`,
  `isBounded_realBox`, `neg_mem_realBox` and `realBox_mem_nhds` say that it is a symmetric convex
  body;
- `discreteTopology_map` says that the image of a subgroup of `ℤ ^ d` is a discrete subgroup of
  `ℝ ^ d`, because a nonzero integer vector has sup norm at least one;
- `ncard_inter_eq` identifies the two counts;
- `hasIndependentShort_of_map` turns an `ℝ`-independent short family of the image into a
  `ℤ`-independent short family of `Λ`. Only this direction is needed: it makes the discrete minima
  no larger than the real ones, which is what the bound requires. The converse direction — that
  `ℤ`-independent integer vectors are `ℝ`-independent — is never used, so no transfer of linear
  independence along `ℤ → ℚ → ℝ` is needed here.

The result is `ncard_latticeBoxPoints_le`.
-/

namespace DenseSetsWithoutLargeSumsets

namespace BoxLattice

open scoped Pointwise Topology

open Metric Module

noncomputable section

variable {d : ℕ}

/-! ## The inclusion of integer vectors -/

/-- The coordinatewise inclusion of integer vectors into real vectors. -/
def intCastHom : (Fin d → ℤ) →+ (Fin d → ℝ) where
  toFun v i := (v i : ℝ)
  map_zero' := by
    funext i
    simp
  map_add' u v := by
    funext i
    simp only [Pi.add_apply]
    push_cast
    ring

@[simp] lemma intCastHom_apply (v : Fin d → ℤ) (i : Fin d) : intCastHom v i = (v i : ℝ) := rfl

lemma intCastHom_injective : Function.Injective (intCastHom : (Fin d → ℤ) → (Fin d → ℝ)) := by
  intro u v huv
  funext i
  have := congr_fun huv i
  rw [intCastHom_apply, intCastHom_apply] at this
  exact_mod_cast this

lemma intCastHom_zsmul (c : ℤ) (v : Fin d → ℤ) :
    intCastHom (c • v) = (c : ℝ) • intCastHom v := by
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

/-! ## The real box is a symmetric convex body -/

/-- The real box of half-widths `L`. -/
def realBox (L : Fin d → ℕ) : Set (Fin d → ℝ) := {x | ∀ i, |x i| ≤ (L i : ℝ)}

lemma mem_realBox {L : Fin d → ℕ} {x : Fin d → ℝ} :
    x ∈ realBox L ↔ ∀ i, |x i| ≤ (L i : ℝ) := Iff.rfl

lemma convex_realBox (L : Fin d → ℕ) : Convex ℝ (realBox L) := by
  intro x hx y hy a b ha hb hab i
  rw [mem_realBox] at hx hy
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  apply le_trans (abs_add_le _ _)
  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  nlinarith [hx i, hy i, abs_nonneg (x i), abs_nonneg (y i)]

lemma neg_mem_realBox (L : Fin d → ℕ) : ∀ x ∈ realBox L, -x ∈ realBox L := by
  intro x hx i
  simpa using hx i

lemma isClosed_realBox (L : Fin d → ℕ) : IsClosed (realBox L) := by
  have hinter : realBox L = ⋂ i, {x : Fin d → ℝ | |x i| ≤ (L i : ℝ)} := by
    ext x
    simp only [mem_realBox, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hinter]
  exact isClosed_iInter fun i ↦ isClosed_le ((continuous_apply i).abs) continuous_const

lemma isBounded_realBox (L : Fin d → ℕ) : Bornology.IsBounded (realBox L) := by
  apply Bornology.IsBounded.subset (Metric.isBounded_closedBall
    (x := (0 : Fin d → ℝ)) (r := ((Finset.univ.sup L : ℕ) : ℝ)))
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).mpr
  intro i
  refine le_trans (le_of_eq (Real.norm_eq_abs _)) (le_trans (hx i) (Nat.cast_le.mpr ?_))
  exact Finset.le_sup (Finset.mem_univ i)

lemma realBox_mem_nhds {L : Fin d → ℕ} (hL : ∀ i, 0 < L i) :
    realBox L ∈ 𝓝 (0 : Fin d → ℝ) := by
  apply Filter.mem_of_superset (Metric.ball_mem_nhds 0 zero_lt_one)
  intro x hx i
  rw [mem_ball_zero_iff] at hx
  have hxi : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
  have hLi : (1 : ℝ) ≤ (L i : ℝ) := by exact_mod_cast hL i
  rw [Real.norm_eq_abs] at hxi
  linarith

/-- A point of a dilate of the box is bounded coordinatewise by the dilated half-widths. -/
lemma abs_le_of_mem_smul_realBox {L : Fin d → ℕ} {t : ℝ} (ht : 0 ≤ t) {x : Fin d → ℝ}
    (hx : x ∈ t • realBox L) (i : Fin d) : |x i| ≤ t * (L i : ℝ) := by
  obtain ⟨y, hy, hxy⟩ := hx
  simp only at hxy
  rw [← hxy, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht]
  exact mul_le_mul_of_nonneg_left (hy i) ht

/-! ## The image of a subgroup of `ℤ ^ d` is discrete -/

/-- A nonzero integer vector has sup norm at least one, so the image of any subgroup of `ℤ ^ d`
avoids the unit ball around the origin. -/
lemma discreteTopology_map (Λ : AddSubgroup (Fin d → ℤ)) :
    DiscreteTopology (Λ.map (intCastHom : (Fin d → ℤ) →+ (Fin d → ℝ))) := by
  refine ConvexGeometry.discreteTopology_of_exists_pos_forall_norm_lt ⟨1, one_pos, ?_⟩
  rintro x hx hnorm
  obtain ⟨v, hvΛ, rfl⟩ := AddSubgroup.mem_map.mp hx
  have hv : v = 0 := by
    funext i
    have hi : ‖(intCastHom v : Fin d → ℝ) i‖ ≤ ‖(intCastHom v : Fin d → ℝ)‖ :=
      norm_le_pi_norm _ i
    rw [intCastHom_apply, Real.norm_eq_abs] at hi
    have hint : |v i| < 1 := by
      rw [← Int.cast_lt (R := ℝ), Int.cast_abs, Int.cast_one]
      linarith
    have := abs_lt.mp hint
    rw [Pi.zero_apply]
    omega
  rw [hv, map_zero]

/-! ## The two counts agree -/

/-- The points of `Λ` inside the box of half-widths `L`. -/
def latticeBoxPoints (Λ : AddSubgroup (Fin d → ℤ)) (L : Fin d → ℕ) : Set (Fin d → ℤ) :=
  {v | v ∈ Λ ∧ ∀ i, |v i| ≤ (L i : ℤ)}

lemma ncard_inter_eq (Λ : AddSubgroup (Fin d → ℤ)) (L : Fin d → ℕ) :
    (realBox L ∩ ((Λ.map (intCastHom : (Fin d → ℤ) →+ (Fin d → ℝ))) :
      Set (Fin d → ℝ))).ncard = (latticeBoxPoints Λ L).ncard := by
  have himage : realBox L ∩ ((Λ.map (intCastHom : (Fin d → ℤ) →+ (Fin d → ℝ))) :
      Set (Fin d → ℝ)) = intCastHom '' latticeBoxPoints Λ L := by
    apply Set.ext
    intro x
    constructor
    · intro hx
      obtain ⟨v, hvΛ, rfl⟩ := AddSubgroup.mem_map.mp hx.2
      refine ⟨v, ?_, rfl⟩
      constructor
      · exact hvΛ
      · intro i
        have hi := hx.1 i
        rw [intCastHom_apply, ← Int.cast_abs] at hi
        exact_mod_cast hi
    · rintro ⟨v, hv, rfl⟩
      constructor
      · intro i
        rw [intCastHom_apply, ← Int.cast_abs]
        exact_mod_cast hv.2 i
      · exact AddSubgroup.mem_map.mpr ⟨v, hv.1, rfl⟩
  rw [himage, Set.ncard_image_of_injective _ intCastHom_injective]

/-! ## Comparison of the successive minima

An `ℝ`-independent family of the image is a `ℤ`-independent family of `Λ`, so the discrete minima
are no larger than the real ones. That is the direction the count needs: a smaller minimum makes
the bound weaker, and the factors of an index admitting no independent family are one on both
sides. -/

/-- An independent short family of the image comes from an independent short family of `Λ`. -/
lemma hasIndependentShort_of_map {Λ : AddSubgroup (Fin d → ℤ)} {L : Fin d → ℕ} {k : ℕ} {t : ℝ}
    (ht : 0 ≤ t)
    (h : ConvexGeometry.HasIndependentShort
      (Λ.map (intCastHom : (Fin d → ℤ) →+ (Fin d → ℝ))) (realBox L) k t) :
    HasIndependentShort Λ L k t := by
  obtain ⟨w, hwindep, hw⟩ := h
  choose v hvΛ hvw using fun j ↦ AddSubgroup.mem_map.mp (hw j).1
  refine ⟨v, ?_, ?_⟩
  · refine Fintype.linearIndependent_iff.mpr ?_
    intro c hc j
    have hsum := congrArg (intCastHom (d := d)) hc
    rw [map_sum, map_zero] at hsum
    simp only [intCastHom_zsmul, hvw] at hsum
    exact_mod_cast Fintype.linearIndependent_iff.mp hwindep (fun j ↦ (c j : ℝ)) hsum j
  · intro j
    constructor
    · exact hvΛ j
    · intro i
      have hi := abs_le_of_mem_smul_realBox ht (hw j).2 i
      rw [← hvw j, intCastHom_apply] at hi
      exact hi

/-- The first minimum of a subgroup of `ℤ ^ d` with respect to a box of positive half-widths is
positive, hence so is every minimum realized by an independent family. -/
lemma successiveMinimum_pos {Λ : AddSubgroup (Fin d → ℤ)} {L : Fin d → ℕ} {k : ℕ} (hk : 1 ≤ k)
    (hne : ∃ t, 0 ≤ t ∧ HasIndependentShort Λ L k t) : 0 < successiveMinimum Λ L k := by
  have hBpos : (0 : ℝ) < ((Finset.univ.sup L : ℕ) : ℝ) + 1 := by positivity
  have hlt : 1 / (((Finset.univ.sup L : ℕ) : ℝ) + 1) * ((Finset.univ.sup L : ℕ) : ℝ) < 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_lt_one hBpos]
    linarith
  have hne1 : ∃ s, 0 ≤ s ∧ HasIndependentShort Λ L 1 s := by
    obtain ⟨t, ht, hshort⟩ := hne
    exact ⟨t, ht, hshort.of_le hk⟩
  have hpos : (0 : ℝ) < 1 / (((Finset.univ.sup L : ℕ) : ℝ) + 1) := by positivity
  exact lt_of_lt_of_le hpos (le_trans (le_successiveMinimum_one
    (fun i ↦ Finset.le_sup (Finset.mem_univ i)) hlt hne1) (successiveMinimum_mono hk hne))

/-- Each factor of the real bound is at most the corresponding factor of the discrete bound. -/
lemma div_successiveMinimum_le (Λ : AddSubgroup (Fin d → ℤ)) (L : Fin d → ℕ) {c : ℝ} (hc : 0 ≤ c)
    {k : ℕ} (hk : 1 ≤ k) :
    c / ConvexGeometry.successiveMinimum
        (Λ.map (intCastHom : (Fin d → ℤ) →+ (Fin d → ℝ))) (realBox L) k
      ≤ c / successiveMinimum Λ L k := by
  rcases eq_or_lt_of_le (ConvexGeometry.successiveMinimum_nonneg
    (Λ.map (intCastHom : (Fin d → ℤ) →+ (Fin d → ℝ))) (realBox L) k) with hzero | hpos
  · rw [← hzero, div_zero]
    exact div_nonneg hc (successiveMinimum_nonneg Λ L k)
  obtain ⟨t₀, ht₀, hshort₀⟩ := ConvexGeometry.exists_of_successiveMinimum_pos hpos
  have hle : successiveMinimum Λ L k ≤ ConvexGeometry.successiveMinimum
      (Λ.map (intCastHom : (Fin d → ℤ) →+ (Fin d → ℝ))) (realBox L) k :=
    ConvexGeometry.le_successiveMinimum ⟨t₀, ht₀, hshort₀⟩ fun s hs hss ↦
      successiveMinimum_le hs (hasIndependentShort_of_map hs hss)
  exact div_le_div_of_nonneg_left hc
    (successiveMinimum_pos hk ⟨t₀, ht₀, hasIndependentShort_of_map ht₀ hshort₀⟩) hle

/-! ## The count -/

/-- **The lattice point count for a box**, statement `(†)`: a subgroup
of `ℤ ^ d` has at most `∏ᵢ (2 ^ (d + 1) / λᵢ + 1)` points in the box of half-widths `L`, where
`λ₁ ≤ ⋯ ≤ λ_d` are its successive minima with respect to that box.

This is the lattice point count that the rank reduction of properization consumes; it does not need
the volume form of Minkowski's second theorem, and neither its proof nor the transport uses any
measure theory. -/
theorem ncard_latticeBoxPoints_le (Λ : AddSubgroup (Fin d → ℤ)) {L : Fin d → ℕ}
    (hL : ∀ i, 0 < L i) :
    ((latticeBoxPoints Λ L).ncard : ℝ) ≤
      ∏ i : Fin d, ((2 : ℝ) ^ (d + 1) / successiveMinimum Λ L ((i : ℕ) + 1) + 1) := by
  haveI := discreteTopology_map Λ
  have hcount := ConvexGeometry.ncard_inter_le_prod_successiveMinimum
    (Λ.map (intCastHom : (Fin d → ℤ) →+ (Fin d → ℝ))) (realBox L) (convex_realBox L)
    (isClosed_realBox L) (realBox_mem_nhds hL) (isBounded_realBox L) (neg_mem_realBox L)
  rw [Module.finrank_fin_fun, ncard_inter_eq] at hcount
  refine hcount.trans (Finset.prod_le_prod ?_ ?_)
  · intro i _
    exact le_trans zero_le_one
      (ConvexGeometry.one_le_div_successiveMinimum_add_one _ _ (by positivity) _)
  · intro i _
    have := div_successiveMinimum_le Λ L (c := (2 : ℝ) ^ (d + 1)) (k := (i : ℕ) + 1)
      (by positivity) (Nat.le_add_left 1 (i : ℕ))
    linarith

end

end BoxLattice

end DenseSetsWithoutLargeSumsets
