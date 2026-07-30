/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Int.Interval
import Mathlib.Data.Pi.Interval
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.Chang.GapToolkit

/-! # Geometry of numbers for the relation lattice of a progression

This file develops the geometry of numbers needed by the properization of generalized arithmetic
progressions, in the discrete form in which properization consumes it: the ambient lattice is
`ℤ ^ d`, the convex body is a box, and the sublattice is the lattice of relations among the steps
of a progression.

Working discretely is not a loss of generality here, and it avoids measure theory entirely:
Blichfeldt's lemma becomes the pigeonhole principle on a finite box of integer points, and the
volume comparisons become cardinality comparisons between boxes.

The main pieces are:

- `intBox` and `natBox`, the symmetric and the nonnegative integer boxes, with their cardinalities;
- `exists_ne_zero_mem_ker_of_card_lt`, Blichfeldt's lemma, and `exists_ne_zero_mem_of_index_lt`,
  **Minkowski's first theorem** for a finite-index subgroup of `ℤ ^ d`;
- `card_mul_prod_le_of_separated` and `card_mul_prod_le_of_eq_zero_of_mem_intBox`, the **packing
  bound**: a subgroup whose only short vector is `0` has few points in any box;
- `successiveMinimum`, the **successive minima** of a subgroup with respect to a box, together
  with `exists_witness_successiveMinimum` for the attainment of the infimum defining them,
  `le_successiveMinimum_one` for the positivity of the first minimum and
  `successiveMinimum_one_le_of_index_lt` for Minkowski's first theorem in that language.

`Chang.Properization` reads all of this through the coefficient box of a progression, as
`GAP.exists_ne_zero_mem_relations` and `GAP.card_twoBoxRelations_le_of_proper`.

Minkowski's *second* theorem, `λ₁ ⋯ λ_d vol K ≤ 2 ^ d covol Λ`, is **not** proved here, and it is
not needed: what properization consumes is the lattice point count `|Λ ∩ B| ≲ ∏ᵢ max (1, C / λᵢ)`,
which is proved in `Chang.ConvexGeometry` and transported back to the present setting, as
`BoxLattice.ncard_latticeBoxPoints_le`, in `Chang.BoxLatticePoints`. That count is not a counting
argument in the sense of this file — it projects along a shortest lattice vector, and the image of
a box under such a projection is not a box — which is why it is proved in a real normed space, in
`Chang.ConvexGeometry`.
-/

namespace DenseSetsWithoutLargeSumsets

noncomputable section

/-! ## Integer boxes -/

section Box

variable {d : ℕ}

/-- The symmetric box of integer vectors with `|v i| ≤ m i`. -/
def intBox (m : Fin d → ℕ) : Finset (Fin d → ℤ) :=
  Finset.Icc (fun i ↦ -(m i : ℤ)) fun i ↦ (m i : ℤ)

/-- The nonnegative box of integer vectors with `0 ≤ v i ≤ m i`. -/
def natBox (m : Fin d → ℕ) : Finset (Fin d → ℤ) :=
  Finset.Icc 0 fun i ↦ (m i : ℤ)

lemma mem_intBox {m : Fin d → ℕ} {v : Fin d → ℤ} : v ∈ intBox m ↔ ∀ i, |v i| ≤ (m i : ℤ) := by
  simp only [intBox, Finset.mem_Icc, Pi.le_def, abs_le, ← forall_and]

lemma mem_natBox {m : Fin d → ℕ} {v : Fin d → ℤ} :
    v ∈ natBox m ↔ ∀ i, 0 ≤ v i ∧ v i ≤ (m i : ℤ) := by
  simp only [natBox, Finset.mem_Icc, Pi.le_def, Pi.zero_apply, ← forall_and]

@[simp] lemma zero_mem_intBox (m : Fin d → ℕ) : (0 : Fin d → ℤ) ∈ intBox m :=
  mem_intBox.mpr fun i ↦ by simp

lemma card_intBox (m : Fin d → ℕ) : (intBox m).card = ∏ i, (2 * m i + 1) := by
  rw [intBox, Pi.card_Icc]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Int.card_Icc]
  omega

lemma card_natBox (m : Fin d → ℕ) : (natBox m).card = ∏ i, (m i + 1) := by
  rw [natBox, Pi.card_Icc]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Int.card_Icc]
  simp

lemma natBox_subset_intBox (m : Fin d → ℕ) : natBox m ⊆ intBox m := by
  intro v hv
  rw [mem_natBox] at hv
  refine mem_intBox.mpr fun i ↦ ?_
  rw [abs_of_nonneg (hv i).1]
  exact (hv i).2

/-- A difference of two points of a box lies in the symmetric box of the same half-widths. -/
lemma sub_mem_intBox {m : Fin d → ℕ} {v w : Fin d → ℤ} (hv : v ∈ natBox m) (hw : w ∈ natBox m) :
    v - w ∈ intBox m := by
  rw [mem_natBox] at hv hw
  refine mem_intBox.mpr fun i ↦ ?_
  have := hv i
  have := hw i
  simp only [Pi.sub_apply, abs_le]
  omega

/-- Translating a box by a point of a smaller box lands in the box of the added half-widths. -/
lemma add_mem_intBox {m m' : Fin d → ℕ} {v w : Fin d → ℤ} (hv : v ∈ intBox m)
    (hw : w ∈ natBox m') : v + w ∈ intBox fun i ↦ m i + m' i := by
  rw [mem_intBox] at hv
  rw [mem_natBox] at hw
  refine mem_intBox.mpr fun i ↦ ?_
  have := abs_le.mp (hv i)
  have := hw i
  simp only [Pi.add_apply, abs_le, Nat.cast_add]
  omega

end Box

/-! ## Blichfeldt's lemma and Minkowski's first theorem -/

section Minkowski

variable {d : ℕ}

/-- Blichfeldt's lemma, discrete form: if a homomorphism maps the nonnegative box into a set with
fewer elements than the box has points, then two of them collide, and their difference is a nonzero
kernel vector inside the symmetric box.

This is the pigeonhole principle in the place where a continuous treatment would use Blichfeldt's
lemma on the volume of a fundamental domain. -/
theorem exists_ne_zero_mem_ker_of_card_lt {H : Type*} [AddCommGroup H]
    (f : (Fin d → ℤ) →+ H) {m : Fin d → ℕ} {s : Finset H} (hmaps : ∀ v ∈ natBox m, f v ∈ s)
    (hcard : s.card < ∏ i, (m i + 1)) :
    ∃ v, f v = 0 ∧ v ≠ 0 ∧ ∀ i, |v i| ≤ (m i : ℤ) := by
  obtain ⟨a, ha, b, hb, hab, hfab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by rwa [card_natBox]) hmaps
  exact ⟨a - b, by rw [map_sub, hfab, sub_self], sub_ne_zero_of_ne hab,
    mem_intBox.mp (sub_mem_intBox ha hb)⟩

/-- Blichfeldt's lemma in counting form: if a homomorphism maps the nonnegative box into a set `s`,
then the box has a fibre with more than `n` points as soon as `n * |s|` is smaller than the box, and
the differences inside that fibre are that many kernel vectors of the symmetric box.

The case `n = 1` is `exists_ne_zero_mem_ker_of_card_lt`; the general case is what a lower bound on
the number of lattice points of a box needs. -/
theorem exists_card_lt_forall_mem_ker_of_mul_card_lt {H : Type*} [AddCommGroup H]
    (f : (Fin d → ℤ) →+ H) {m : Fin d → ℕ} {s : Finset H} (hmaps : ∀ v ∈ natBox m, f v ∈ s)
    {n : ℕ} (hcard : n * s.card < ∏ i, (m i + 1)) :
    ∃ F : Finset (Fin d → ℤ), n < F.card ∧ ∀ v ∈ F, f v = 0 ∧ ∀ i, |v i| ≤ (m i : ℤ) := by
  classical
  obtain ⟨y, -, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps
    (by rw [card_natBox, mul_comm]; exact hcard)
  obtain ⟨v₀, hv₀⟩ := Finset.card_pos.mp (Nat.zero_le n |>.trans_lt hy)
  rw [Finset.mem_filter] at hv₀
  refine ⟨{v ∈ natBox m | f v = y}.image (· - v₀), ?_, ?_⟩
  · rwa [Finset.card_image_of_injective _ (fun u v huv ↦ sub_left_injective huv)]
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    rw [Finset.mem_filter] at hu
    exact ⟨by rw [map_sub, hu.2, hv₀.2, sub_self], mem_intBox.mp (sub_mem_intBox hu.1 hv₀.1)⟩

/-- Minkowski's first theorem for a finite-index subgroup of `ℤ ^ d`: a box with more points than
the index of the subgroup contains a nonzero point of the subgroup. -/
theorem exists_ne_zero_mem_of_index_lt (Λ : AddSubgroup (Fin d → ℤ)) [Λ.FiniteIndex]
    {m : Fin d → ℕ} (hindex : Λ.index < ∏ i, (m i + 1)) :
    ∃ v ∈ Λ, v ≠ 0 ∧ ∀ i, |v i| ≤ (m i : ℤ) := by
  classical
  haveI : Fintype ((Fin d → ℤ) ⧸ Λ) :=
    AddSubgroup.fintypeOfIndexNeZero AddSubgroup.FiniteIndex.index_ne_zero
  have hcard : (Finset.univ : Finset ((Fin d → ℤ) ⧸ Λ)).card < ∏ i, (m i + 1) := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact hindex
  obtain ⟨v, hv, hne, hbox⟩ :=
    exists_ne_zero_mem_ker_of_card_lt (QuotientAddGroup.mk' Λ) (fun _ _ ↦ Finset.mem_univ _) hcard
  exact ⟨v, (QuotientAddGroup.eq_zero_iff v).mp hv, hne, hbox⟩

end Minkowski

/-! ## The packing bound

A set of integer points that are pairwise far apart in the box metric is sparse: the translates of
a box of half-widths `m` by its elements are disjoint, hence fit in the enlarged box. This is the
counting form of the volume packing argument, and it is the one place where the geometry of numbers
gives an upper bound on the number of lattice points of a box. -/

section Packing

variable {d : ℕ}

/-- The packing bound: if distinct points of `s` are never within `m` of each other, and `s` lies
in the box of half-widths `M`, then `s` is small. -/
theorem card_mul_prod_le_of_separated {s : Finset (Fin d → ℤ)} {m M : Fin d → ℕ}
    (hbox : ∀ u ∈ s, ∀ i, |u i| ≤ (M i : ℤ))
    (hsep : ∀ u ∈ s, ∀ w ∈ s, u ≠ w → ∃ i, (m i : ℤ) < |u i - w i|) :
    s.card * ∏ i, (m i + 1) ≤ ∏ i, (2 * (M i + m i) + 1) := by
  classical
  rw [← card_natBox, ← Finset.card_product, ← card_intBox]
  refine Finset.card_le_card_of_injOn (fun p ↦ p.1 + p.2) ?_ ?_
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_product] at hp
    exact add_mem_intBox (mem_intBox.mpr (hbox p.1 hp.1)) hp.2
  · rintro ⟨u, a⟩ hp ⟨u', a'⟩ hp' hsum
    simp only [Finset.mem_coe, Finset.mem_product] at hp hp'
    simp only at hsum
    have hfst : u = u' := by
      by_contra hne
      obtain ⟨i, hi⟩ := hsep u hp.1 u' hp'.1 hne
      have hclose := abs_le.mp (mem_intBox.mp (sub_mem_intBox hp.2 hp'.2) i)
      have hcoord := congr_fun hsum i
      simp only [Pi.add_apply, Pi.sub_apply] at hclose hcoord
      rcases lt_abs.mp hi with h | h <;> omega
    rw [hfst] at hsum ⊢
    rw [add_left_cancel hsum]

/-- The packing bound for a subgroup: if `0` is the only point of `Λ` in the box of half-widths
`m`, then `Λ` has at most `∏ (2 (M i + m i) + 1) / ∏ (m i + 1)` points in the box of
half-widths `M`. -/
theorem card_mul_prod_le_of_eq_zero_of_mem_intBox {Λ : AddSubgroup (Fin d → ℤ)} {m M : Fin d → ℕ}
    (hm : ∀ v ∈ Λ, (∀ i, |v i| ≤ (m i : ℤ)) → v = 0) (s : Finset (Fin d → ℤ))
    (hs : ∀ v ∈ s, v ∈ Λ) (hbox : ∀ v ∈ s, ∀ i, |v i| ≤ (M i : ℤ)) :
    s.card * ∏ i, (m i + 1) ≤ ∏ i, (2 * (M i + m i) + 1) := by
  refine card_mul_prod_le_of_separated hbox fun u hu w hw huw ↦ ?_
  by_contra hcon
  push Not at hcon
  exact huw (sub_eq_zero.mp (hm _ (Λ.sub_mem (hs u hu) (hs w hw)) hcon))

end Packing

/-! ## Successive minima

The `k`-th successive minimum of a subgroup `Λ` of `ℤ ^ d` with respect to the box of half-widths
`L` is the least dilation factor of the box whose points contain `k` linearly independent vectors
of `Λ`. Linear independence is taken over `ℤ`, which for integer vectors is the same as linear
independence over `ℝ`.

As in the literature the minima are defined as infima, and as in the literature the infimum is
attained, `exists_witness_successiveMinimum`. Both that and the positivity of the first minimum,
`le_successiveMinimum_one`, come from discreteness of `ℤ ^ d` rather than from compactness. -/

section SuccessiveMinima

variable {d : ℕ}

/-- `IsShort L t v` says that `v` lies in the `t`-dilate of the box of half-widths `L`. -/
def IsShort (L : Fin d → ℕ) (t : ℝ) (v : Fin d → ℤ) : Prop := ∀ i, |(v i : ℝ)| ≤ t * L i

lemma IsShort.mono {L : Fin d → ℕ} {t t' : ℝ} {v : Fin d → ℤ} (h : IsShort L t v) (htt' : t ≤ t') :
    IsShort L t' v := fun i ↦
  (h i).trans (mul_le_mul_of_nonneg_right htt' (Nat.cast_nonneg _))

lemma isShort_of_abs_le {L m : Fin d → ℕ} {t : ℝ} {v : Fin d → ℤ}
    (hv : ∀ i, |v i| ≤ (m i : ℤ)) (hm : ∀ i, (m i : ℝ) ≤ t * L i) : IsShort L t v := by
  intro i
  rw [← Int.cast_abs]
  exact ((Int.cast_le (R := ℝ)).mpr (hv i)).trans (hm i)

/-- `HasIndependentShort Λ L k t` says that the `t`-dilate of the box of half-widths `L` contains
`k` linearly independent vectors of `Λ`. -/
def HasIndependentShort (Λ : AddSubgroup (Fin d → ℤ)) (L : Fin d → ℕ) (k : ℕ) (t : ℝ) : Prop :=
  ∃ v : Fin k → (Fin d → ℤ), LinearIndependent ℤ v ∧ ∀ j, v j ∈ Λ ∧ IsShort L t (v j)

lemma HasIndependentShort.mono {Λ : AddSubgroup (Fin d → ℤ)} {L : Fin d → ℕ} {k : ℕ} {t t' : ℝ}
    (h : HasIndependentShort Λ L k t) (htt' : t ≤ t') : HasIndependentShort Λ L k t' := by
  obtain ⟨v, hindep, hv⟩ := h
  exact ⟨v, hindep, fun j ↦ ⟨(hv j).1, (hv j).2.mono htt'⟩⟩

lemma HasIndependentShort.of_le {Λ : AddSubgroup (Fin d → ℤ)} {L : Fin d → ℕ} {k k' : ℕ} {t : ℝ}
    (h : HasIndependentShort Λ L k t) (hk : k' ≤ k) : HasIndependentShort Λ L k' t := by
  obtain ⟨v, hindep, hv⟩ := h
  exact ⟨v ∘ Fin.castLE hk, hindep.comp _ (Fin.castLE_injective hk), fun j ↦ hv _⟩

/-- The `k`-th successive minimum of `Λ` with respect to the box of half-widths `L`. -/
def successiveMinimum (Λ : AddSubgroup (Fin d → ℤ)) (L : Fin d → ℕ) (k : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ HasIndependentShort Λ L k t}

lemma bddBelow_dilations (Λ : AddSubgroup (Fin d → ℤ)) (L : Fin d → ℕ) (k : ℕ) :
    BddBelow {t : ℝ | 0 ≤ t ∧ HasIndependentShort Λ L k t} :=
  ⟨0, fun _ ht ↦ ht.1⟩

lemma successiveMinimum_nonneg (Λ : AddSubgroup (Fin d → ℤ)) (L : Fin d → ℕ) (k : ℕ) :
    0 ≤ successiveMinimum Λ L k :=
  Real.sInf_nonneg fun _ ht ↦ ht.1

/-- Any dilation factor realizing `k` independent vectors bounds the `k`-th minimum. -/
lemma successiveMinimum_le {Λ : AddSubgroup (Fin d → ℤ)} {L : Fin d → ℕ} {k : ℕ} {t : ℝ}
    (ht : 0 ≤ t) (h : HasIndependentShort Λ L k t) : successiveMinimum Λ L k ≤ t :=
  csInf_le (bddBelow_dilations Λ L k) ⟨ht, h⟩

/-- The successive minima increase with the number of independent vectors required. -/
lemma successiveMinimum_mono {Λ : AddSubgroup (Fin d → ℤ)} {L : Fin d → ℕ} {k k' : ℕ}
    (hk : k ≤ k') (hne : ∃ t, 0 ≤ t ∧ HasIndependentShort Λ L k' t) :
    successiveMinimum Λ L k ≤ successiveMinimum Λ L k' := by
  refine le_csInf hne fun t ht ↦ successiveMinimum_le ht.1 (ht.2.of_le hk)

/-- A dilation factor smaller than every minimum bounds it from below. -/
lemma le_successiveMinimum {Λ : AddSubgroup (Fin d → ℤ)} {L : Fin d → ℕ} {k : ℕ} {t : ℝ}
    (hne : ∃ s, 0 ≤ s ∧ HasIndependentShort Λ L k s)
    (h : ∀ s, 0 ≤ s → HasIndependentShort Λ L k s → t ≤ s) : t ≤ successiveMinimum Λ L k :=
  le_csInf hne fun s hs ↦ h s hs.1 hs.2

/-! ### Minkowski's first theorem in terms of the first minimum -/

/-- A nonzero integer vector has a coordinate of absolute value at least one, so it is short only
for dilation factors that reach one length. -/
lemma exists_one_le_mul_of_hasIndependentShort {Λ : AddSubgroup (Fin d → ℤ)} {L : Fin d → ℕ}
    {t : ℝ} (h : HasIndependentShort Λ L 1 t) : ∃ i, 1 ≤ t * L i := by
  obtain ⟨v, hindep, hv⟩ := h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (hindep.ne_zero 0)
  rw [Pi.zero_apply] at hi
  refine ⟨i, le_trans ?_ ((hv 0).2 i)⟩
  rw [← Int.cast_abs, ← Int.cast_one, Int.cast_le]
  exact Int.one_le_abs hi

/-- The first minimum is positive: a dilation factor `t` with `t * B < 1`, where `B` bounds every
length, is below it. Discreteness of `ℤ ^ d` replaces the compactness argument that gives
positivity of the first minimum for a general lattice. -/
lemma le_successiveMinimum_one {Λ : AddSubgroup (Fin d → ℤ)} {L : Fin d → ℕ} {B : ℕ} {t : ℝ}
    (hB : ∀ i, L i ≤ B) (ht : t * B < 1)
    (hne : ∃ s, 0 ≤ s ∧ HasIndependentShort Λ L 1 s) : t ≤ successiveMinimum Λ L 1 := by
  refine le_successiveMinimum hne fun s hs hshort ↦ ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨i, hi⟩ := exists_one_le_mul_of_hasIndependentShort hshort
  have hLB : (L i : ℝ) ≤ B := Nat.cast_le.mpr (hB i)
  nlinarith [Nat.cast_nonneg (α := ℝ) (L i)]

/-! ### Attainment of the minima

The ratios `|v i| / L i` that a family of integer vectors realizes all have the common denominator
`∏ L`, so the dilation factors that carry an independent family form a set of multiples of
`1 / ∏ L`. Such a set has a least element, which is the discrete substitute for the compactness
argument that attains the minima of a general convex body. -/

/-- The largest coefficient of a family of integer vectors, measured over the common denominator
`∏ L`: it is the numerator of `max (j, i), |v j i| / L i`. -/
def scaledSup (L : Fin d → ℕ) {k : ℕ} (v : Fin k → (Fin d → ℤ)) : ℕ :=
  Finset.univ.sup fun p : Fin k × Fin d ↦ (v p.1 p.2).natAbs * ((∏ i, L i) / L p.2)

lemma le_scaledSup (L : Fin d → ℕ) {k : ℕ} (v : Fin k → (Fin d → ℤ)) (j : Fin k) (i : Fin d) :
    (v j i).natAbs * ((∏ i, L i) / L i) ≤ scaledSup L v :=
  Finset.le_sup (f := fun p : Fin k × Fin d ↦ (v p.1 p.2).natAbs * ((∏ i, L i) / L p.2))
    (Finset.mem_univ (j, i))

lemma prod_pos_of_length_pos {L : Fin d → ℕ} (hL : ∀ i, 0 < L i) :
    (0 : ℝ) < ((∏ i, L i : ℕ) : ℝ) := by
  exact_mod_cast Finset.prod_pos fun i _ ↦ hL i

/-- A family whose scaled supremum is at most `a` is short for the dilation factor `a / ∏ L`. -/
lemma isShort_of_scaledSup_le {L : Fin d → ℕ} {k : ℕ} (hL : ∀ i, 0 < L i)
    {v : Fin k → (Fin d → ℤ)} {a : ℕ} (ha : scaledSup L v ≤ a) (j : Fin k) :
    IsShort L ((a : ℝ) / ((∏ i, L i : ℕ) : ℝ)) (v j) := by
  intro i
  have hnat : (v j i).natAbs * ∏ i, L i ≤ a * L i := by
    rw [← Nat.div_mul_cancel (Finset.dvd_prod_of_mem L (Finset.mem_univ i)), ← mul_assoc]
    exact Nat.mul_le_mul_right _ (le_trans (le_scaledSup L v j i) ha)
  rw [div_mul_eq_mul_div, le_div_iff₀ (prod_pos_of_length_pos hL), ← Int.cast_abs,
    ← Nat.cast_natAbs]
  exact_mod_cast hnat

/-- A family short for the dilation factor `s` has scaled supremum at most `s * ∏ L`. -/
lemma scaledSup_le_mul {L : Fin d → ℕ} {k : ℕ} {v : Fin k → (Fin d → ℤ)} {s : ℝ} (hs : 0 ≤ s)
    (hv : ∀ j, IsShort L s (v j)) : (scaledSup L v : ℝ) ≤ s * ((∏ i, L i : ℕ) : ℝ) := by
  refine le_trans (Nat.cast_le.mpr (Finset.sup_le fun p _ ↦ Nat.le_floor ?_))
    (Nat.floor_le (mul_nonneg hs (Nat.cast_nonneg _)))
  have hcancel : ((∏ i, L i : ℕ) : ℝ) = ((L p.2 : ℕ) : ℝ) * (((∏ i, L i) / L p.2 : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (Finset.dvd_prod_of_mem L (Finset.mem_univ p.2))]
  rw [Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs, hcancel, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hv p.1 p.2) (Nat.cast_nonneg _)

/-- The infimum defining a successive minimum is attained: some family of `k` independent vectors
of `Λ` is short for the dilation factor `successiveMinimum Λ L k` itself. -/
theorem exists_witness_successiveMinimum {Λ : AddSubgroup (Fin d → ℤ)} {L : Fin d → ℕ} {k : ℕ}
    (hL : ∀ i, 0 < L i) (hne : ∃ t, 0 ≤ t ∧ HasIndependentShort Λ L k t) :
    HasIndependentShort Λ L k (successiveMinimum Λ L k) := by
  classical
  have hQ : ∃ a : ℕ, ∃ v : Fin k → (Fin d → ℤ), LinearIndependent ℤ v ∧ (∀ j, v j ∈ Λ) ∧
      scaledSup L v ≤ a := by
    obtain ⟨t, -, v, hindep, hv⟩ := hne
    exact ⟨scaledSup L v, v, hindep, fun j ↦ (hv j).1, le_rfl⟩
  obtain ⟨v₀, hindep₀, hmem₀, hsup₀⟩ := Nat.find_spec hQ
  have hmin : successiveMinimum Λ L k = (Nat.find hQ : ℝ) / ((∏ i, L i : ℕ) : ℝ) := by
    refine le_antisymm (successiveMinimum_le (by positivity)
      ⟨v₀, hindep₀, fun j ↦ ⟨hmem₀ j, isShort_of_scaledSup_le hL hsup₀ j⟩⟩) ?_
    refine le_successiveMinimum hne fun s hs hshort ↦ ?_
    obtain ⟨v, hindep, hv⟩ := hshort
    rw [div_le_iff₀ (prod_pos_of_length_pos hL)]
    refine le_trans (Nat.cast_le.mpr (Nat.find_min' hQ
      ⟨v, hindep, fun j ↦ (hv j).1, le_rfl⟩)) ?_
    exact scaledSup_le_mul hs fun j ↦ (hv j).2
  rw [hmin]
  exact ⟨v₀, hindep₀, fun j ↦ ⟨hmem₀ j, isShort_of_scaledSup_le hL hsup₀ j⟩⟩

/-- Minkowski's first theorem in terms of successive minima: a dilate of the box with more integer
points than the index of `Λ` reaches the first minimum. -/
theorem successiveMinimum_one_le_of_index_lt {Λ : AddSubgroup (Fin d → ℤ)} [Λ.FiniteIndex]
    {L m : Fin d → ℕ} {t : ℝ} (ht : 0 ≤ t) (hm : ∀ i, (m i : ℝ) ≤ t * L i)
    (hindex : Λ.index < ∏ i, (m i + 1)) : successiveMinimum Λ L 1 ≤ t := by
  obtain ⟨v, hv, hne, hbox⟩ := exists_ne_zero_mem_of_index_lt Λ hindex
  refine successiveMinimum_le ht ⟨fun _ ↦ v, ?_, fun _ ↦ ⟨hv, isShort_of_abs_le hbox hm⟩⟩
  exact linearIndependent_unique_iff.mpr hne

/-! ### Adapted families

`exists_witness_successiveMinimum` produces `k` independent vectors that are all short for the
`k`-th minimum. Constructing a progression inside a lattice neighborhood needs instead one vector
per minimum: an independent family whose `i`-th member is short for the `i`-th minimum. Such a
family is built by extending an adapted family of length `i` with a member of a witness family for
the `(i + 1)`-st minimum, which is possible because `i + 1` independent vectors never all depend on
`i` given ones. -/

/-- An independent family of `i + 1` vectors has a member that extends any independent family of
`i` vectors. Over `ℤ` this is a rank comparison: if every member depended on the shorter family,
a nonzero multiple of it would lie in a submodule of rank at most `i`. -/
lemma exists_linearIndependent_snoc {i : ℕ} {v : Fin i → (Fin d → ℤ)}
    {w : Fin (i + 1) → (Fin d → ℤ)} (hv : LinearIndependent ℤ v) (hw : LinearIndependent ℤ w) :
    ∃ j, LinearIndependent ℤ (Fin.snoc v (w j)) := by
  by_contra hcon
  push Not at hcon
  have key : ∀ j, ∃ c : ℤ, c ≠ 0 ∧ c • w j ∈ Submodule.span ℤ (Set.range v) := by
    intro j
    obtain ⟨g, hg, m, hm⟩ := Fintype.not_linearIndependent_iff.mp (hcon j)
    rw [Fin.sum_univ_castSucc] at hg
    simp only [Fin.snoc_castSucc, Fin.snoc_last] at hg
    have hlast : g (Fin.last i) ≠ 0 := by
      intro hzero
      rw [hzero, zero_smul, add_zero] at hg
      refine hm (Fin.lastCases hzero (fun m ↦ ?_) m)
      exact Fintype.linearIndependent_iff.mp hv (fun m ↦ g m.castSucc) hg m
    refine ⟨g (Fin.last i), hlast, ?_⟩
    rw [eq_neg_of_add_eq_zero_right hg]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ fun m _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩))
  choose c hc hmem using key
  have hscaled : LinearIndependent ℤ fun j ↦ c j • w j := by
    refine Fintype.linearIndependent_iff.mpr fun a ha j ↦ ?_
    refine (mul_eq_zero.mp
      (Fintype.linearIndependent_iff.mp hw (fun j ↦ a j * c j) ?_ j)).resolve_right (hc j)
    rw [← ha]
    exact Finset.sum_congr rfl fun j _ ↦ mul_smul (a j) (c j) (w j)
  have hindep : LinearIndependent ℤ
      fun j ↦ (⟨c j • w j, hmem j⟩ : Submodule.span ℤ (Set.range v)) := by
    refine LinearIndependent.of_comp (Submodule.span ℤ (Set.range v)).subtype ?_
    simpa [Function.comp_def] using hscaled
  have hrank := LinearIndependent.cardinal_le_rank hindep
  rw [Cardinal.mk_fin] at hrank
  have hle : ((i + 1 : ℕ) : Cardinal) ≤ ((i : ℕ) : Cardinal) :=
    hrank.trans ((rank_span_le _).trans (Cardinal.mk_range_le.trans_eq (Cardinal.mk_fin i)))
  rw [Nat.cast_le] at hle
  omega

/-- **An adapted family of short vectors**: a subgroup of full rank has `d` independent vectors
whose `i`-th member is short for the `i`-th successive minimum. -/
theorem exists_adapted_shortFamily {Λ : AddSubgroup (Fin d → ℤ)} {L : Fin d → ℕ}
    (hL : ∀ i, 0 < L i) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (hfull : HasIndependentShort Λ L d t₀) :
    ∃ v : Fin d → (Fin d → ℤ), LinearIndependent ℤ v ∧
      ∀ i : Fin d, v i ∈ Λ ∧ IsShort L (successiveMinimum Λ L ((i : ℕ) + 1)) (v i) := by
  suffices h : ∀ m : ℕ, m ≤ d → ∃ v : Fin m → (Fin d → ℤ), LinearIndependent ℤ v ∧
      ∀ i : Fin m, v i ∈ Λ ∧ IsShort L (successiveMinimum Λ L ((i : ℕ) + 1)) (v i) from
    h d le_rfl
  intro m
  induction m with
  | zero => exact fun _ ↦ ⟨Fin.elim0, linearIndependent_empty_type, fun i ↦ i.elim0⟩
  | succ m ih =>
      intro hm
      obtain ⟨v, hvindep, hv⟩ := ih (Nat.le_of_succ_le hm)
      obtain ⟨w, hwindep, hw⟩ :=
        exists_witness_successiveMinimum (k := m + 1) hL ⟨t₀, ht₀, hfull.of_le hm⟩
      obtain ⟨j, hsnoc⟩ := exists_linearIndependent_snoc hvindep hwindep
      refine ⟨Fin.snoc v (w j), hsnoc, Fin.lastCases ?_ fun i ↦ ?_⟩
      · rw [Fin.snoc_last, Fin.val_last]
        exact hw j
      · rw [Fin.snoc_castSucc, Fin.val_castSucc]
        exact hv i

end SuccessiveMinima

end

end DenseSetsWithoutLargeSumsets
