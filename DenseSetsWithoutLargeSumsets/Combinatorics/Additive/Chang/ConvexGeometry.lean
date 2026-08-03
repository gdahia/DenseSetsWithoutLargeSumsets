/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import Mathlib.Analysis.Convex.Gauge
import Mathlib.MeasureTheory.Group.GeometryOfNumbers

/-! # Successive minima of a lattice with respect to a symmetric convex body

This file develops the successive minima of a discrete subgroup of a real normed space with respect
to a symmetric convex body, in the generality required by the geometry of numbers behind
properization. It is the real counterpart of `Chang.GeometryOfNumbers`, which does the same for a
box of integer points, and it supplies the geometric foundation for the properization theorem in
`Chang.Properization`.

The main pieces are:

- `setOf_mem_smul_eq_Ici` and `mem_smul_iff_gauge_le`, which identify the dilation factors whose
  dilate of `K` contains a given point with the closed half-line above its gauge. Everything else
  rests on this: it is what makes the minima behave like minima rather than like infima;
- `successiveMinimum`, the `k`-th successive minimum, with its basic API;
- `le_successiveMinimum_one`, positivity of the first minimum, from discreteness of the lattice;
- `exists_witness_successiveMinimum`, attainment of the infimum defining the minima;
- `successiveMinimum_one_le_of_measure_lt`, **Minkowski's first theorem** in terms of the first
  minimum, derived from Mathlib's convex body theorem, and
  `ofReal_pow_successiveMinimum_one_mul_measure_le`, its quantitative form
  `λ₁ ^ d vol K ≤ 2 ^ d covol L`;
- `ncard_setOf_add_smul_mem_le`, `exists_intCast_smul_eq_of_gauge_min`,
  `hasIndependentShort_succ_of_map`, `hasIndependentShort_succ_of_isCompl` and
  `gauge_le_two_mul_of_mem_map`, the steps of the projection induction: a fibre of the projection
  carries few lattice points, a shortest vector is primitive, and the successive minima of the
  projected lattice are comparable with those of the lattice in both directions,
  `λ_{i+1} ≤ max (λ₁, λ̄ᵢ + λ₁ / 2)` and `λ₁ ≤ 2 λ̄ᵢ`;
- `ncard_inter_le_prod_successiveMinimum`, **the lattice point count**
  `|Λ ∩ K| ≤ ∏ᵢ (2 ^ (d + 1) / λᵢ + 1)`, proved by the descending induction on the dimension that
  those steps assemble into: project along a shortest lattice vector, count the fibres, and recurse
  in a complement of its line. The uniform numerator `2 ^ (d + 1)` is what survives the descent,
  since each projection only gives `λ_{i+1} ≤ 2 λ̄ᵢ`.

That count, and not the volume form of Minkowski's second theorem, is what the properization
argument in `Chang.Properization` consumes. Its proof uses no
measure theory:
`convex_image`, `neg_mem_image`, `gauge_image_le` and `isVonNBounded_image` say that the projected
body is a convex body again, and `exists_pos_forall_norm_apply_lt` together with
`discreteTopology_of_exists_pos_forall_norm_lt` says the projected lattice is again a discrete
subgroup. `Chang.BoxLatticePoints` transports the count to a subgroup of `ℤ ^ d` and a box, which
is the form the properization consumes.
-/

namespace DenseSetsWithoutLargeSumsets

namespace ConvexGeometry

open scoped Pointwise Topology

open Metric MeasureTheory Module

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}

/-! ## Dilates of a convex body

A symmetric convex body is a closed, bounded, convex neighbourhood of the origin. For such a body
the gauge decides which dilates contain a given point. -/

/-- The dilation factors whose dilate of `K` contains `x` form the closed half-line above the gauge
of `x`. -/
lemma setOf_mem_smul_eq_Ici (hconv : Convex ℝ K) (hclosed : IsClosed K) (hK₀ : K ∈ 𝓝 0)
    (hbdd : Bornology.IsVonNBounded ℝ K) (x : E) :
    {t : ℝ | 0 ≤ t ∧ x ∈ t • K} = Set.Ici (gauge K x) := by
  apply Set.ext
  intro t
  constructor
  · intro ht
    exact gauge_le_of_mem ht.1 ht.2
  · intro ht
    refine ⟨(gauge_nonneg x).trans ht, ?_⟩
    rcases eq_or_ne x 0 with rfl | hx
    · rw [← smul_zero t]
      exact Set.smul_mem_smul_set (mem_of_mem_nhds hK₀)
    · have htpos : 0 < t :=
        lt_of_lt_of_le ((gauge_pos (absorbent_nhds_zero hK₀) hbdd).mpr hx) ht
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ htpos.ne', ← hclosed.closure_eq,
        ← gauge_le_one_iff_mem_closure hconv hK₀, gauge_smul_of_nonneg (inv_nonneg.mpr htpos.le),
        smul_eq_mul, inv_mul_le_one₀ htpos]
      exact ht

/-- Membership in a dilate of a convex body is decided by the gauge. -/
lemma mem_smul_iff_gauge_le (hconv : Convex ℝ K) (hclosed : IsClosed K) (hK₀ : K ∈ 𝓝 0)
    (hbdd : Bornology.IsVonNBounded ℝ K) {t : ℝ} (ht : 0 ≤ t) (x : E) :
    x ∈ t • K ↔ gauge K x ≤ t := by
  constructor
  · exact gauge_le_of_mem ht
  · intro h
    have hmem : t ∈ {t : ℝ | 0 ≤ t ∧ x ∈ t • K} := by
      rw [setOf_mem_smul_eq_Ici hconv hclosed hK₀ hbdd]
      exact h
    exact hmem.2

/-- Membership in a dilate is monotone in the dilation factor. -/
lemma mem_smul_of_le (hconv : Convex ℝ K) (hclosed : IsClosed K) (hK₀ : K ∈ 𝓝 0)
    (hbdd : Bornology.IsVonNBounded ℝ K) {x : E} {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hx : x ∈ s • K) : x ∈ t • K :=
  (mem_smul_iff_gauge_le hconv hclosed hK₀ hbdd (hs.trans hst) x).mpr
    (le_trans ((mem_smul_iff_gauge_le hconv hclosed hK₀ hbdd hs x).mp hx) hst)

/-! ## Successive minima -/

/-- `HasIndependentShort L K k t` says that the `t`-dilate of `K` contains `k` linearly independent
vectors of `L`. -/
def HasIndependentShort (L : AddSubgroup E) (K : Set E) (k : ℕ) (t : ℝ) : Prop :=
  ∃ v : Fin k → E, LinearIndependent ℝ v ∧ ∀ j, v j ∈ L ∧ v j ∈ t • K

/-- The `k`-th successive minimum of `L` with respect to `K`: the least dilation factor of `K`
whose points contain `k` linearly independent vectors of `L`. -/
def successiveMinimum (L : AddSubgroup E) (K : Set E) (k : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ HasIndependentShort L K k t}

variable {L : AddSubgroup E} {k : ℕ}

lemma HasIndependentShort.of_le {k' : ℕ} {t : ℝ} (h : HasIndependentShort L K k t) (hk : k' ≤ k) :
    HasIndependentShort L K k' t := by
  obtain ⟨v, hindep, hv⟩ := h
  exact ⟨v ∘ Fin.castLE hk, hindep.comp _ (Fin.castLE_injective hk), fun j ↦ hv _⟩

lemma bddBelow_dilations (L : AddSubgroup E) (K : Set E) (k : ℕ) :
    BddBelow {t : ℝ | 0 ≤ t ∧ HasIndependentShort L K k t} :=
  ⟨0, fun _ ht ↦ ht.1⟩

lemma successiveMinimum_nonneg (L : AddSubgroup E) (K : Set E) (k : ℕ) :
    0 ≤ successiveMinimum L K k :=
  Real.sInf_nonneg fun _ ht ↦ ht.1

/-- Any dilation factor carrying `k` independent lattice vectors bounds the `k`-th minimum. -/
lemma successiveMinimum_le {t : ℝ} (ht : 0 ≤ t) (h : HasIndependentShort L K k t) :
    successiveMinimum L K k ≤ t :=
  csInf_le (bddBelow_dilations L K k) ⟨ht, h⟩

/-- A dilation factor below every one that carries `k` independent lattice vectors is below the
`k`-th minimum. -/
lemma le_successiveMinimum {t : ℝ} (hne : ∃ s, 0 ≤ s ∧ HasIndependentShort L K k s)
    (h : ∀ s, 0 ≤ s → HasIndependentShort L K k s → t ≤ s) : t ≤ successiveMinimum L K k :=
  le_csInf hne fun s hs ↦ h s hs.1 hs.2

/-- The successive minima increase with the number of independent vectors required. -/
lemma successiveMinimum_mono {k' : ℕ} (hk : k ≤ k')
    (hne : ∃ t, 0 ≤ t ∧ HasIndependentShort L K k' t) :
    successiveMinimum L K k ≤ successiveMinimum L K k' :=
  le_csInf hne fun _ ht ↦ successiveMinimum_le ht.1 (ht.2.of_le hk)

/-! ## Positivity of the first minimum -/

omit [NormedSpace ℝ E] in
/-- A discrete subgroup meets a small enough ball around the origin only at the origin. -/
lemma exists_pos_forall_norm_lt (L : AddSubgroup E) [DiscreteTopology L] :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ L, ‖x‖ < r → x = 0 := by
  obtain ⟨U, hUopen, hUL⟩ :=
    isOpen_inter_eq_singleton_of_mem_discrete (s := (L : Set E)) DiscreteTopology.isDiscrete
      (zero_mem L)
  have h0U : (0 : E) ∈ U ∩ (L : Set E) := by
    rw [hUL]
    exact Set.mem_singleton 0
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hUopen 0 h0U.1
  refine ⟨r, hr, ?_⟩
  intro x hx hnorm
  have hxU : x ∈ U ∩ (L : Set E) :=
    ⟨hball (by simpa only [Metric.mem_ball, dist_zero_right] using hnorm), hx⟩
  rw [hUL] at hxU
  exact hxU

/-- The first minimum is positive: a dilation factor whose dilate of `K` stays inside a ball that
the lattice meets only at the origin is below it. -/
lemma le_successiveMinimum_one [DiscreteTopology L] {R r t : ℝ} (hR : K ⊆ closedBall 0 R)
    (hr : ∀ x ∈ L, ‖x‖ < r → x = 0) (ht : 0 ≤ t) (htR : t * R < r)
    (hne : ∃ s, 0 ≤ s ∧ HasIndependentShort L K 1 s) : t ≤ successiveMinimum L K 1 := by
  apply le_successiveMinimum hne
  intro s hs hshort
  by_contra! hlt
  obtain ⟨v, hindep, hv⟩ := hshort
  obtain ⟨y, hy, hyv⟩ := (hv 0).2
  refine hindep.ne_zero 0 (hr _ (hv 0).1 ?_)
  rw [← hyv, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  have hyR : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hR hy
  nlinarith [norm_nonneg y]

/-! ## Attainment of the minima -/

/-- The lattice points inside a dilate of a bounded body form a finite set. -/
lemma finite_lattice_inter_smul [ProperSpace E] (L : AddSubgroup E) [DiscreteTopology L]
    (hbdd : Bornology.IsBounded K) (t : ℝ) : Set.Finite (t • K ∩ (L : Set E)) :=
  Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
    (Bornology.IsBounded.smul₀ hbdd t) AddSubgroup.isClosed_of_discrete

/-- The infimum defining a successive minimum is attained: some family of `k` independent vectors
of `L` lies in the dilate of `K` by `successiveMinimum L K k` itself.

Discreteness bounds the number of candidate families, and `setOf_mem_smul_eq_Ici` turns each
family's set of admissible dilation factors into a closed half-line, so the infimum lies in a
finite union of closed half-lines. -/
theorem exists_witness_successiveMinimum [ProperSpace E] [DiscreteTopology L]
    (hconv : Convex ℝ K) (hclosed : IsClosed K) (hK₀ : K ∈ 𝓝 0) (hbdd : Bornology.IsBounded K)
    (hne : ∃ t, 0 ≤ t ∧ HasIndependentShort L K k t) :
    HasIndependentShort L K k (successiveMinimum L K k) := by
  classical
  set T := {t : ℝ | 0 ≤ t ∧ HasIndependentShort L K k t} with hT
  set lam := successiveMinimum L K k with hlam
  have hTne : T.Nonempty := by
    obtain ⟨t, ht⟩ := hne
    exact ⟨t, ht⟩
  have hvonN : Bornology.IsVonNBounded ℝ K := (NormedSpace.isVonNBounded_iff ℝ).mpr hbdd
  set Fams := {v : Fin k → E |
    (∀ j, v j ∈ (lam + 1) • K ∩ (L : Set E)) ∧ LinearIndependent ℝ v} with hFams
  have hFamsfin : Fams.Finite :=
    Set.Finite.subset (Set.Finite.pi fun _ ↦ finite_lattice_inter_smul L hbdd (lam + 1))
      fun v hv ↦ Set.mem_univ_pi.mpr hv.1
  have hsub : T ⊆ (⋃ v ∈ Fams, ⋂ j, Set.Ici (gauge K (v j))) ∪ Set.Ici (lam + 1) := by
    intro t ht
    rcases le_or_gt (lam + 1) t with hle | hlt
    · exact Or.inr hle
    obtain ⟨v, hindep, hv⟩ := ht.2
    refine Or.inl (Set.mem_iUnion₂.mpr ⟨v, ?_, ?_⟩)
    · constructor
      · intro j
        constructor
        · exact mem_smul_of_le hconv hclosed hK₀ hvonN ht.1 hlt.le (hv j).2
        · exact (hv j).1
      · exact hindep
    · exact Set.mem_iInter.mpr fun j ↦
        (mem_smul_iff_gauge_le hconv hclosed hK₀ hvonN ht.1 (v j)).mp (hv j).2
  have hmem : lam ∈ (⋃ v ∈ Fams, ⋂ j, Set.Ici (gauge K (v j))) ∪ Set.Ici (lam + 1) :=
    ((hFamsfin.isClosed_biUnion fun _ _ ↦
      isClosed_iInter fun _ ↦ isClosed_Ici).union isClosed_Ici).closure_subset_iff.mpr hsub
      ((Real.isGLB_sInf hTne (bddBelow_dilations L K k)).mem_closure hTne)
  obtain hmem | hmem := hmem
  · obtain ⟨v, hv, hvlam⟩ := Set.mem_iUnion₂.mp hmem
    exact ⟨v, hv.2, fun j ↦ ⟨(hv.1 j).2, (mem_smul_iff_gauge_le hconv hclosed hK₀ hvonN
      (successiveMinimum_nonneg L K k) (v j)).mpr (Set.mem_iInter.mp hvlam j)⟩⟩
  · exact absurd (Set.mem_Ici.mp hmem) (not_le.mpr (by linarith))

/-! ## Ingredients for the lattice point count

The results below are the elementary steps of the induction which bounds the number of lattice
points of a symmetric convex body by a product over the successive minima; the induction itself is
`ncard_inter_le_prod_successiveMinimum` below. That
count, and not the volume form of Minkowski's second theorem, is what the properization of
`Chang.Properization` consumes, and the induction proving it uses no measure theory: it projects
along a shortest lattice vector and needs only the statements below about the body and its gauge.
The same steps also give the volume form, with a constant `exp (O (n ^ 2))`, once the covolume of a
quotient lattice is available. -/

/-- Half the difference of two points of a symmetric convex body lies in the body. This is what
makes the central fibre of a body the longest one. -/
lemma smul_sub_mem (hconv : Convex ℝ K) (hsymm : ∀ x ∈ K, -x ∈ K) {a b : E} (ha : a ∈ K)
    (hb : b ∈ K) : (2 : ℝ)⁻¹ • (a - b) ∈ K := by
  rw [smul_sub, sub_eq_add_neg, ← smul_neg]
  exact hconv ha (hsymm b hb) (by norm_num) (by norm_num) (by norm_num)

/-- The gauge of a symmetric body does not see signs. -/
lemma gauge_smul_abs (hsymm : ∀ x ∈ K, -x ∈ K) (m : ℝ) (x : E) :
    gauge K (m • x) = |m| * gauge K x := by
  rcases le_or_gt 0 m with hm | hm
  · rw [gauge_smul_of_nonneg hm, smul_eq_mul, abs_of_nonneg hm]
  · rw [← gauge_neg hsymm, ← neg_smul, gauge_smul_of_nonneg (by linarith : (0 : ℝ) ≤ -m),
      smul_eq_mul, abs_of_neg hm]

lemma gauge_zsmul_le (hsymm : ∀ x ∈ K, -x ∈ K) (m : ℝ) (x : E) :
    gauge K (m • x) ≤ |m| * gauge K x := (gauge_smul_abs hsymm m x).le

/-- **The fibre bound.** Two points of a symmetric convex body that differ by a multiple of `v`
differ by at most `2 / gauge K v` of it.

Counting the integer points of such a fibre is the step that replaces Minkowski's second theorem in
the lattice point count below: a fibre of `Λ ∩ K` over the projection along
a shortest vector `v` has at most `2 / λ₁ + 1` points. -/
lemma abs_sub_mul_gauge_le_two (hconv : Convex ℝ K) (hsymm : ∀ x ∈ K, -x ∈ K) {y v : E} {a b : ℝ}
    (ha : y + a • v ∈ K) (hb : y + b • v ∈ K) : |a - b| * gauge K v ≤ 2 := by
  have hmem : ((a - b) / 2) • v ∈ K := by
    refine Set.mem_of_eq_of_mem ?_ (smul_sub_mem hconv hsymm ha hb)
    rw [add_sub_add_left_eq_sub, ← sub_smul, smul_smul, div_eq_inv_mul]
  have hgauge := gauge_le_one_of_mem hmem
  rw [gauge_smul_abs hsymm, abs_div] at hgauge
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))] at hgauge
  nlinarith [gauge_nonneg (s := K) v, abs_nonneg (a - b)]

/-- **The fibre bound, in integer coordinates.** The integer multiples of `v` that keep a point
inside a symmetric convex body form an interval of length at most `4 / gauge K v`, centred at any
one of them. -/
lemma setOf_add_smul_mem_subset_Icc (hconv : Convex ℝ K) (hsymm : ∀ x ∈ K, -x ∈ K) {v : E}
    (hv : 0 < gauge K v) {y : E} {m₀ : ℤ} (hm₀ : y + (m₀ : ℝ) • v ∈ K) :
    {m : ℤ | y + (m : ℝ) • v ∈ K} ⊆
      Set.Icc (m₀ - ⌊2 / gauge K v⌋₊) (m₀ + ⌊2 / gauge K v⌋₊) := by
  intro m hm
  have hbound := abs_sub_mul_gauge_le_two hconv hsymm hm hm₀
  have hfloor : ((m - m₀).natAbs : ℤ) ≤ (⌊2 / gauge K v⌋₊ : ℤ) := by
    refine Int.ofNat_le.mpr (Nat.le_floor ?_)
    rw [le_div_iff₀ hv, Nat.cast_natAbs, Int.cast_abs]
    push_cast
    exact hbound
  simp only [Set.mem_Icc]
  omega

/-- **The fibre count.** A line through a symmetric convex body meets the integer multiples of `v`
on it in at most `2 ⌊2 / gauge K v⌋ + 1 ≤ 4 / gauge K v + 1` points.

Applied with `v` a shortest lattice vector, this bounds each fibre of `Λ ∩ K` over the projection
along `v`, and it is the step of the lattice point induction that replaces the volume
comparison of Minkowski's second theorem. -/
lemma ncard_setOf_add_smul_mem_le (hconv : Convex ℝ K) (hsymm : ∀ x ∈ K, -x ∈ K) {v : E}
    (hv : 0 < gauge K v) (y : E) :
    {m : ℤ | y + (m : ℝ) • v ∈ K}.ncard ≤ 2 * ⌊2 / gauge K v⌋₊ + 1 := by
  classical
  rcases Set.eq_empty_or_nonempty {m : ℤ | y + (m : ℝ) • v ∈ K} with hempty | ⟨m₀, hm₀⟩
  · rw [hempty, Set.ncard_empty]
    omega
  refine le_trans (Set.ncard_le_ncard (t := ↑(Finset.Icc (m₀ - ⌊2 / gauge K v⌋₊)
    (m₀ + ⌊2 / gauge K v⌋₊)) )
    (by simpa only [Finset.coe_Icc] using setOf_add_smul_mem_subset_Icc hconv hsymm hv hm₀)
    (Finset.finite_toSet _)) (le_of_eq ?_)
  rw [Set.ncard_coe_finset, Int.card_Icc]
  omega

/-- Reduction along a lattice direction: a point differing from a point of gauge at most `t` by a
real multiple of `v` can be moved by an *integer* multiple of `v` to a point of gauge at most
`t + gauge K v / 2`.

This is the step that compares the successive minima of a quotient lattice with those of the
lattice itself: applied with `v` a shortest vector, it shows that a short vector of the quotient
lifts to a lattice vector that is short by at most `λ₁ / 2`. -/
lemma exists_int_gauge_sub_zsmul_le (hconv : Convex ℝ K) (hK₀ : K ∈ 𝓝 0)
    (hsymm : ∀ x ∈ K, -x ∈ K) {t : ℝ} {y z v : E} {s : ℝ} (hz : gauge K z ≤ t)
    (hy : y = z + s • v) : ∃ m : ℤ, gauge K (y - (m : ℝ) • v) ≤ t + gauge K v / 2 := by
  use round s
  rw [hy, add_sub_assoc, ← sub_smul]
  apply le_trans (gauge_add_le hconv (absorbent_nhds_zero hK₀) _ _)
  refine add_le_add hz (le_trans (gauge_zsmul_le hsymm _ _) ?_)
  rw [div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_right ?_ (gauge_nonneg v)
  simpa only [one_div] using abs_sub_round s

/-- A nonzero lattice vector of least gauge is primitive: every lattice point on its line is an
integer multiple of it.

This is the step of the induction that lets the projection along `v` carry the lattice to a
lattice. -/
lemma exists_intCast_smul_eq_of_gauge_min (hsymm : ∀ x ∈ K, -x ∈ K) {v w : E} (hv : v ∈ L)
    (hvpos : 0 < gauge K v) (hmin : ∀ y ∈ L, y ≠ 0 → gauge K v ≤ gauge K y) (hw : w ∈ L)
    {s : ℝ} (hws : w = s • v) : ∃ m : ℤ, w = (m : ℝ) • v := by
  use round s
  by_contra hne
  refine absurd (hmin _ (L.sub_mem hw ?_) (sub_ne_zero_of_ne hne)) (not_le.mpr ?_)
  · rw [Int.cast_smul_eq_zsmul]
    exact L.zsmul_mem hv _
  · rw [hws, ← sub_smul]
    apply lt_of_le_of_lt (gauge_zsmul_le hsymm _ _)
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right (abs_sub_round s) (gauge_nonneg v))
    rw [one_div]
    linarith

/-- **Lifting a single short vector.** A vector of the projected lattice inside the `t`-dilate of
the projected body lifts to a lattice vector of gauge at most `t + gauge K v / 2`: any lift differs
from a point of the `t`-dilate by a multiple of `v`, and rounding that multiple costs
`gauge K v / 2`. -/
lemma exists_mem_gauge_le_of_mem_map {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hconv : Convex ℝ K) (hK₀ : K ∈ 𝓝 0) (hsymm : ∀ x ∈ K, -x ∈ K) (π : E →ₗ[ℝ] F) {v : E}
    (hv : v ∈ L) (hπv : π v = 0) (hker : ∀ x : E, π x = 0 → ∃ s : ℝ, x = s • v) {t : ℝ}
    (ht : 0 ≤ t) {w : F} (hwL : w ∈ L.map (π : E →+ F)) (hwK : w ∈ t • (π '' K)) :
    ∃ y, y ∈ L ∧ π y = w ∧ gauge K y ≤ t + gauge K v / 2 := by
  obtain ⟨y, hyL, hyw⟩ := AddSubgroup.mem_map.mp hwL
  obtain ⟨p, ⟨x, hxK, hxp⟩, hpw⟩ := hwK
  simp only at hpw
  have hkerx : π (y - t • x) = 0 := by
    rw [map_sub, map_smul, hxp, sub_eq_zero]
    exact hyw.trans hpw.symm
  obtain ⟨s, hs⟩ := hker _ hkerx
  obtain ⟨m, hm⟩ := exists_int_gauge_sub_zsmul_le hconv hK₀ hsymm
    (gauge_le_of_mem ht (Set.smul_mem_smul_set hxK)) (sub_eq_iff_eq_add'.mp hs)
  refine ⟨y - (m : ℝ) • v, L.sub_mem hyL ?_, ?_, hm⟩
  · rw [Int.cast_smul_eq_zsmul]
    exact L.zsmul_mem hv _
  · rw [map_sub, map_smul, hπv, smul_zero, sub_zero]
    exact hyw

/-- A nonzero vector of the projected lattice is at least half as long as the shortest lattice
vector: its lift is a nonzero lattice vector of gauge at most `t + gauge K v / 2`.

This is the second half of the comparison of successive minima: together with
`hasIndependentShort_succ_of_map` it gives `λ_{i+1} ≤ 2 λ̄ᵢ`. -/
lemma gauge_le_two_mul_of_mem_map {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hconv : Convex ℝ K) (hK₀ : K ∈ 𝓝 0) (hsymm : ∀ x ∈ K, -x ∈ K) (π : E →ₗ[ℝ] F) {v : E}
    (hv : v ∈ L) (hπv : π v = 0) (hker : ∀ x : E, π x = 0 → ∃ s : ℝ, x = s • v)
    (hmin : ∀ y ∈ L, y ≠ 0 → gauge K v ≤ gauge K y) {t : ℝ} (ht : 0 ≤ t)
    (h : HasIndependentShort (L.map (π : E →+ F)) (π '' K) 1 t) : gauge K v ≤ 2 * t := by
  obtain ⟨w, hwindep, hw⟩ := h
  obtain ⟨y, hyL, hyπ, hygauge⟩ :=
    exists_mem_gauge_le_of_mem_map hconv hK₀ hsymm π hv hπv hker ht (hw 0).1 (hw 0).2
  have hyne : y ≠ 0 := fun hzero ↦ hwindep.ne_zero 0 (by rw [← hyπ, hzero, map_zero])
  have := hmin y hyL hyne
  linarith

/-- **Lifting through a projection.** If the kernel of a linear map `π` is the line through a
lattice vector `v`, then `i` independent vectors of the projected lattice inside the `t`-dilate of
the projected body lift to `i + 1` independent lattice vectors inside the dilate by
`max (gauge K v) (t + gauge K v / 2)`.

With `v` a shortest lattice vector this reads `λ_{i+1} ≤ max (λ₁, λ̄ᵢ + λ₁ / 2)`, the comparison of
successive minima that the lattice point induction needs. -/
theorem hasIndependentShort_succ_of_map {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hconv : Convex ℝ K) (hclosed : IsClosed K) (hK₀ : K ∈ 𝓝 0)
    (hbdd : Bornology.IsVonNBounded ℝ K) (hsymm : ∀ x ∈ K, -x ∈ K) (π : E →ₗ[ℝ] F) {v : E}
    (hv : v ∈ L) (hvne : v ≠ 0) (hπv : π v = 0) (hker : ∀ x : E, π x = 0 → ∃ s : ℝ, x = s • v)
    {i : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (h : HasIndependentShort (L.map (π : E →+ F)) (π '' K) i t) :
    HasIndependentShort L K (i + 1) (max (gauge K v) (t + gauge K v / 2)) := by
  obtain ⟨w, hwindep, hw⟩ := h
  choose y hyL hyπ hygauge using fun j ↦
    exists_mem_gauge_le_of_mem_map hconv hK₀ hsymm π hv hπv hker ht (hw j).1 (hw j).2
  have hyindep : LinearIndependent ℝ y := by
    apply LinearIndependent.of_comp π
    rwa [show (π : E → F) ∘ y = w from funext hyπ]
  have hmax : 0 ≤ max (gauge K v) (t + gauge K v / 2) := le_max_of_le_left (gauge_nonneg v)
  refine ⟨Fin.cons v y, linearIndependent_finCons.mpr ⟨hyindep, ?_⟩, ?_⟩
  · intro hspan
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hspan
    have hcw : ∑ j, c j • w j = 0 := by
      rw [← hπv, ← hc, map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, hyπ]
    apply hvne
    rw [← hc, Finset.sum_eq_zero fun j _ ↦ ?_]
    rw [Fintype.linearIndependent_iff.mp hwindep c hcw j, zero_smul]
  · refine Fin.cases ?_ ?_
    · constructor
      · simpa using hv
      · apply (mem_smul_iff_gauge_le hconv hclosed hK₀ hbdd hmax v).mpr
        exact le_max_left (gauge K v) (t + gauge K v / 2)
    · intro j
      constructor
      · simpa using hyL j
      · apply (mem_smul_iff_gauge_le hconv hclosed hK₀ hbdd hmax _).mpr
        simpa using le_trans (hygauge j) (le_max_right (gauge K v) (t + gauge K v / 2))

/-- The lifting theorem for the projection onto a complement of the line through `v`.

Taking the complement rather than the quotient keeps the projected lattice and body inside a normed
space, namely a subspace of `E`, so the lattice point induction never has to leave
the category in which the minima are defined. -/
theorem hasIndependentShort_succ_of_isCompl {W : Submodule ℝ E} {v : E}
    (hcompl : IsCompl W (Submodule.span ℝ {v})) (hconv : Convex ℝ K) (hclosed : IsClosed K)
    (hK₀ : K ∈ 𝓝 0) (hbdd : Bornology.IsVonNBounded ℝ K) (hsymm : ∀ x ∈ K, -x ∈ K)
    (hv : v ∈ L) (hvne : v ≠ 0) {i : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (h : HasIndependentShort (L.map ((Submodule.projectionOnto W _ hcompl : E →ₗ[ℝ] W) : E →+ W))
      (Submodule.projectionOnto W _ hcompl '' K) i t) :
    HasIndependentShort L K (i + 1) (max (gauge K v) (t + gauge K v / 2)) := by
  refine hasIndependentShort_succ_of_map hconv hclosed hK₀ hbdd hsymm _ hv hvne ?_ ?_ ht h
  · exact Submodule.projectionOnto_apply_of_mem_right _ (Submodule.mem_span_singleton_self v)
  · intro x hx
    have hxker : x ∈ Submodule.span ℝ {v} := by
      rw [← Submodule.ker_projectionOnto hcompl]
      exact LinearMap.mem_ker.mpr hx
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hxker
    exact ⟨s, hs.symm⟩

/-! ### The projected body

The induction applies its hypothesis to the image of `K` under the projection, so that image has to
be a symmetric convex body again, and its gauge has to be controlled by the gauge of `K`. -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma convex_image (hconv : Convex ℝ K) (π : E →ₗ[ℝ] F) : Convex ℝ (π '' K) :=
  hconv.linear_image π

lemma neg_mem_image (hsymm : ∀ x ∈ K, -x ∈ K) (π : E →ₗ[ℝ] F) :
    ∀ y ∈ π '' K, -y ∈ π '' K := by
  rintro y ⟨x, hx, rfl⟩
  exact ⟨-x, hsymm x hx, map_neg π x⟩

/-- Projecting does not increase the gauge. -/
lemma gauge_image_le (hK₀ : Absorbent ℝ K) (π : E →ₗ[ℝ] F) (x : E) :
    gauge (π '' K) (π x) ≤ gauge K x := by
  apply csInf_le_csInf ⟨0, fun _ hr ↦ hr.1.le⟩ hK₀.gauge_set_nonempty
  intro r hr
  obtain ⟨y, hy, hyx⟩ := hr.2
  simp only at hyx
  refine ⟨hr.1, π y, ⟨y, hy, rfl⟩, ?_⟩
  simp only
  rw [← map_smul, hyx]

/-- The image of a convex body under a continuous linear map is bounded, so the projected body is
again a convex body. -/
lemma isVonNBounded_image (hbdd : Bornology.IsVonNBounded ℝ K) (π : E →L[ℝ] F) :
    Bornology.IsVonNBounded ℝ (π '' K) :=
  Bornology.IsVonNBounded.image hbdd π

/-- **Discreteness of the projected lattice.** If a projection `p` kills a lattice vector `v` and
splits every vector as its image plus a multiple of `v`, then the images of the lattice avoid a ball
around the origin.

Reducing modulo `ℤv` moves a lattice vector with small image into a fixed bounded set, which meets
the lattice in finitely many points, so only finitely many images are in play. -/
theorem exists_pos_forall_norm_apply_lt [ProperSpace E] [DiscreteTopology L] (p : E →ₗ[ℝ] E)
    {v : E} (hv : v ∈ L) (hpv : p v = 0) (hsplit : ∀ y : E, ∃ s : ℝ, y - p y = s • v) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ L, ‖p y‖ < r → p y = 0 := by
  classical
  have hAfin : (closedBall (0 : E) (‖v‖ + 1) ∩ (L : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete isBounded_closedBall
      AddSubgroup.isClosed_of_discrete
  set N := (hAfin.toFinset.image fun y ↦ ‖p y‖).filter (0 < ·) with hN
  refine ⟨if hne : N.Nonempty then min (N.min' hne) 1 else 1, ?_, ?_⟩
  · split
    · exact lt_min (Finset.mem_filter.mp (N.min'_mem _)).2 one_pos
    · exact one_pos
  · intro y hy hylt
    by_contra hpy
    obtain ⟨s, hs⟩ := hsplit y
    have hyv : y - (round s : ℝ) • v ∈ closedBall (0 : E) (‖v‖ + 1) ∩ (L : Set E) := by
      constructor
      · have hrw : y - (round s : ℝ) • v = p y + (s - (round s : ℝ)) • v := by
          rw [sub_smul, ← hs]
          abel
        rw [mem_closedBall, dist_zero_right, hrw]
        apply le_trans (norm_add_le _ _)
        rw [norm_smul, Real.norm_eq_abs]
        have hround := abs_sub_round s
        have hrle : ‖p y‖ ≤ 1 := by
          apply le_trans hylt.le
          split
          · exact min_le_right _ _
          · exact le_rfl
        nlinarith [norm_nonneg v, norm_nonneg (p y)]
      · rw [Int.cast_smul_eq_zsmul]
        exact L.sub_mem hy (L.zsmul_mem hv _)
    have hpeq : p (y - (round s : ℝ) • v) = p y := by
      rw [map_sub, map_smul, hpv, smul_zero, sub_zero]
    have hmemN : ‖p y‖ ∈ N := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨_, ?_, congrArg norm hpeq⟩, ?_⟩
      · exact hAfin.mem_toFinset.mpr hyv
      · exact norm_pos_iff.mpr hpy
    refine absurd hylt (not_lt.mpr ?_)
    rw [dif_pos ⟨_, hmemN⟩]
    exact min_le_of_left_le (N.min'_le _ hmemN)

omit [NormedSpace ℝ E] in
/-- Conversely, a subgroup that avoids a ball around the origin is discrete. Together with
`exists_pos_forall_norm_apply_lt` this feeds the projected lattice back into the induction, whose
hypotheses are stated with `DiscreteTopology`. -/
lemma discreteTopology_of_exists_pos_forall_norm_lt {G : AddSubgroup E}
    (h : ∃ r : ℝ, 0 < r ∧ ∀ x ∈ G, ‖x‖ < r → x = 0) : DiscreteTopology G := by
  obtain ⟨r, hr, hG⟩ := h
  rw [discreteTopology_iff_isOpen_singleton_zero]
  refine isOpen_induced_iff.mpr ⟨Metric.ball (0 : E) r, Metric.isOpen_ball, ?_⟩
  apply Set.ext
  intro x
  simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff]
  constructor
  · intro hx
    exact Subtype.ext (hG x x.2 hx)
  · intro hx
    rw [hx]
    simpa using hr

/-! ## The lattice point count

The lattice point induction. Everything above is one of its steps; what follows is
the induction itself. It descends on the dimension of the ambient space by projecting along a
shortest lattice vector, so it has to quantify over all spaces at once, and it is stated with the
uniform constant `2 ^ (d + 1)`, which is what makes the constant survive the passage to the
projected lattice: the projected minima only satisfy `λ_{i+1} ≤ 2 λ̄ᵢ`, so each descent costs a
factor two in the numerator. No measure theory is involved. -/

universe u

/-- Every factor of the lattice point count is at least one, whether or not the corresponding
minimum exists. -/
lemma one_le_div_successiveMinimum_add_one (L : AddSubgroup E) (K : Set E) {c : ℝ} (hc : 0 ≤ c)
    (k : ℕ) : (1 : ℝ) ≤ c / successiveMinimum L K k + 1 := by
  have := div_nonneg hc (successiveMinimum_nonneg L K k)
  linarith

/-- A positive successive minimum witnesses an independent family: an index admitting none has
minimum `sInf ∅ = 0`. This is what lets the count ignore the indices beyond the rank of the
lattice instead of tracking that rank. -/
lemma exists_of_successiveMinimum_pos (hpos : 0 < successiveMinimum L K k) :
    ∃ t, 0 ≤ t ∧ HasIndependentShort L K k t := by
  by_contra! hcon
  have hempty : {t : ℝ | 0 ≤ t ∧ HasIndependentShort L K k t} = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun t ht ↦ hcon t ht.1 ht.2
  refine absurd hpos (not_lt.mpr (le_of_eq ?_))
  rw [successiveMinimum, hempty, Real.sInf_empty]

/-- **The lattice point count**, in the form its induction proves: a symmetric convex body contains
at most `∏ᵢ (2 ^ (d + 1) / λᵢ + 1)` points of a discrete subgroup of a `d`-dimensional space.

The statement quantifies over all spaces of a given dimension because the induction replaces the
ambient space by a complement of the line through a shortest lattice vector. -/
theorem ncard_inter_le_prod_aux :
    ∀ (n : ℕ) {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (L : AddSubgroup E) [DiscreteTopology L] (K : Set E), finrank ℝ E = n →
      Convex ℝ K → IsClosed K → K ∈ 𝓝 0 → Bornology.IsBounded K → (∀ x ∈ K, -x ∈ K) →
      ((K ∩ (L : Set E)).ncard : ℝ) ≤
        ∏ i : Fin n, ((2 : ℝ) ^ (n + 1) / successiveMinimum L K ((i : ℕ) + 1) + 1) := by
  intro n
  induction n with
  | zero =>
    intro E _ _ _ L _ K hrank _ _ _ _ _
    haveI : Subsingleton E := Module.finrank_zero_iff.mp hrank
    rw [Fin.prod_univ_zero]
    have hle : (K ∩ (L : Set E)).ncard ≤ 1 :=
      (Set.ncard_le_one (Set.toFinite _)).mpr fun a _ b _ ↦ Subsingleton.elim a b
    exact_mod_cast hle
  | succ m ih =>
    intro E _ _ _ L _ K hrank hconv hclosed hK₀ hbdd hsymm
    classical
    have hvonN : Bornology.IsVonNBounded ℝ K := (NormedSpace.isVonNBounded_iff ℝ).mpr hbdd
    have hSfin : (K ∩ (L : Set E)).Finite :=
      Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hbdd
        AddSubgroup.isClosed_of_discrete
    by_cases hex : ∃ x, x ∈ K ∧ x ∈ L ∧ x ≠ 0
    swap
    · -- The lattice meets the body only at the origin, and every factor is at least one.
      push Not at hex
      refine le_trans ?_ (Finset.one_le_prod fun i _ ↦
        one_le_div_successiveMinimum_add_one L K (by positivity) _)
      have hle : (K ∩ (L : Set E)).ncard ≤ 1 :=
        (Set.ncard_le_one hSfin).mpr fun a ha b hb ↦ (hex a ha.1 ha.2).trans (hex b hb.1 hb.2).symm
      exact_mod_cast hle
    -- A shortest nonzero lattice vector of the body.
    obtain ⟨v₀, hv₀K, hv₀L, hv₀ne⟩ := hex
    have hne1 : ∃ t : ℝ, 0 ≤ t ∧ HasIndependentShort L K 1 t :=
      ⟨1, zero_le_one, fun _ ↦ v₀, linearIndependent_unique_iff.mpr hv₀ne, fun _ ↦
        ⟨hv₀L, (mem_smul_iff_gauge_le hconv hclosed hK₀ hvonN zero_le_one v₀).mpr
          (gauge_le_one_of_mem hv₀K)⟩⟩
    obtain ⟨w, hwindep, hw⟩ :=
      exists_witness_successiveMinimum (k := 1) (L := L) hconv hclosed hK₀ hbdd hne1
    let v : E := w 0
    have hvL : v ∈ L := (hw 0).1
    have hvne : v ≠ 0 := hwindep.ne_zero 0
    have hgaugele : gauge K v ≤ successiveMinimum L K 1 :=
      (mem_smul_iff_gauge_le hconv hclosed hK₀ hvonN (successiveMinimum_nonneg L K 1) v).mp (hw 0).2
    have hfirst : ∀ y ∈ L, y ≠ 0 → successiveMinimum L K 1 ≤ gauge K y := fun y hy hyne ↦
      successiveMinimum_le (gauge_nonneg y) ⟨fun _ ↦ y, linearIndependent_unique_iff.mpr hyne,
        fun _ ↦ ⟨hy, (mem_smul_iff_gauge_le hconv hclosed hK₀ hvonN (gauge_nonneg y) y).mpr le_rfl⟩⟩
    have hmin : ∀ y ∈ L, y ≠ 0 → gauge K v ≤ gauge K y := fun y hy hyne ↦
      hgaugele.trans (hfirst y hy hyne)
    have hgauge : gauge K v = successiveMinimum L K 1 :=
      le_antisymm hgaugele (hfirst v hvL hvne)
    have hlampos : 0 < successiveMinimum L K 1 := by
      obtain ⟨R, hR⟩ := hbdd.subset_closedBall (0 : E)
      obtain ⟨r, hrpos, hr⟩ := exists_pos_forall_norm_lt L
      have hmaxpos : (0 : ℝ) < max R 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
      have hxpos : 0 < r / (2 * max R 1) := div_pos hrpos (by positivity)
      have hcancel : r / (2 * max R 1) * (2 * max R 1) = r := div_mul_cancel₀ r (by positivity)
      refine lt_of_lt_of_le hxpos (le_successiveMinimum_one
        (hR.trans (closedBall_subset_closedBall (le_max_left R 1))) hr hxpos.le ?_ hne1)
      nlinarith [mul_pos hxpos hmaxpos]
    have hvpos : 0 < gauge K v := hgauge ▸ hlampos
    -- Project along the line through it.
    obtain ⟨W, hWcompl⟩ := (Submodule.span ℝ {v}).exists_isCompl
    have hcompl : IsCompl W (Submodule.span ℝ {v}) := hWcompl.symm
    let π : E →ₗ[ℝ] W := Submodule.projectionOnto W (Submodule.span ℝ {v}) hcompl
    let p : E →ₗ[ℝ] E := Submodule.projection W (Submodule.span ℝ {v}) hcompl
    have hπv : π v = 0 :=
      Submodule.projectionOnto_apply_of_mem_right hcompl (Submodule.mem_span_singleton_self v)
    have hker : ∀ x : E, π x = 0 → ∃ s : ℝ, x = s • v := by
      intro x hx
      have hmem : x ∈ Submodule.span ℝ {v} := by
        rw [← Submodule.ker_projectionOnto hcompl]
        exact LinearMap.mem_ker.mpr hx
      obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hmem
      exact ⟨s, hs.symm⟩
    have hWrank : finrank ℝ W = m := by
      have hsum := Submodule.finrank_add_eq_of_isCompl hWcompl
      rw [finrank_span_singleton hvne, hrank] at hsum
      omega
    -- The projected body is again a symmetric convex body.
    have hπcont : Continuous π := LinearMap.continuous_of_finiteDimensional π
    have hKcompact : IsCompact K := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
    have hKbar₀ : π '' K ∈ 𝓝 (0 : W) := by
      have hpre : (fun x : W ↦ (x : E)) ⁻¹' K ∈ 𝓝 (0 : W) := by
        apply continuous_subtype_val.continuousAt.preimage_mem_nhds
        simpa using hK₀
      apply Filter.mem_of_superset hpre
      intro x hx
      exact ⟨(x : E), hx, Submodule.projectionOnto_apply_left hcompl x⟩
    -- The projected lattice is again discrete.
    have hpv : p v = 0 :=
      Submodule.projection_apply_of_mem_right hcompl (Submodule.mem_span_singleton_self v)
    have hsplit : ∀ y : E, ∃ s : ℝ, y - p y = s • v := by
      intro y
      have hmem : y - p y ∈ Submodule.span ℝ {v} := by
        rw [← Submodule.ker_projection hcompl]
        apply LinearMap.mem_ker.mpr
        rw [map_sub, Submodule.projection_apply_of_mem_left hcompl
          (Submodule.projection_apply_mem hcompl y), sub_self]
      obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hmem
      exact ⟨s, hs.symm⟩
    haveI : DiscreteTopology (L.map (π : E →+ W)) := by
      apply discreteTopology_of_exists_pos_forall_norm_lt
      obtain ⟨r, hrpos, hr⟩ := exists_pos_forall_norm_apply_lt (L := L) p hvL hpv hsplit
      refine ⟨r, hrpos, ?_⟩
      rintro x hx hnorm
      obtain ⟨y, hyL, rfl⟩ := AddSubgroup.mem_map.mp hx
      exact Subtype.ext (hr y hyL hnorm)
    have hTfin : ((π '' K) ∩ ((L.map (π : E →+ W)) : Set W)).Finite :=
      Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
        (hKcompact.image hπcont).isBounded AddSubgroup.isClosed_of_discrete
    have hIH := ih (L.map (π : E →+ W)) (π '' K) hWrank (convex_image hconv π)
      (hKcompact.image hπcont).isClosed hKbar₀ (hKcompact.image hπcont).isBounded
      (neg_mem_image hsymm π)
    -- Each fibre of the projection carries at most `2 ⌊2 / λ₁⌋ + 1` lattice points.
    have hcount : (K ∩ (L : Set E)).ncard ≤
        (2 * ⌊2 / gauge K v⌋₊ + 1) * ((π '' K) ∩ ((L.map (π : E →+ W)) : Set W)).ncard := by
      rw [Set.ncard_eq_toFinset_card _ hSfin, Set.ncard_eq_toFinset_card _ hTfin]
      refine Finset.card_le_mul_card_image_of_maps_to (f := fun x ↦ π x) ?_ _ ?_
      · intro a ha
        rw [Set.Finite.mem_toFinset] at ha ⊢
        exact ⟨⟨a, ha.1, rfl⟩, AddSubgroup.mem_map.mpr ⟨a, ha.2, rfl⟩⟩
      · intro b _
        rcases Finset.eq_empty_or_nonempty {a ∈ hSfin.toFinset | π a = b} with hempty | ⟨x₀, hx₀⟩
        · simp [hempty]
        rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hx₀
        have hbase : x₀ + ((0 : ℤ) : ℝ) • v ∈ K := by simpa using hx₀.1.1
        have hkey : ∀ x : E, ∃ mz : ℤ,
            x ∈ ({a ∈ hSfin.toFinset | π a = b} : Finset E) → x = x₀ + (mz : ℝ) • v := by
          intro x
          by_cases hx : x ∈ ({a ∈ hSfin.toFinset | π a = b} : Finset E)
          swap
          · exact ⟨0, fun hcon ↦ absurd hcon hx⟩
          rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hx
          have hsubker : π (x - x₀) = 0 := by rw [map_sub, hx.2, hx₀.2, sub_self]
          obtain ⟨s, hs⟩ := hker _ hsubker
          obtain ⟨mz, hmz⟩ := exists_intCast_smul_eq_of_gauge_min hsymm hvL hvpos hmin
            (L.sub_mem hx.1.2 hx₀.1.2) hs
          refine ⟨mz, ?_⟩
          intro _
          rw [← hmz]
          abel
        choose g hg using hkey
        refine le_trans (Finset.card_le_card_of_injOn (t := Finset.Icc (-(⌊2 / gauge K v⌋₊ : ℤ))
          (⌊2 / gauge K v⌋₊ : ℤ)) g ?_ ?_) (le_of_eq ?_)
        · intro x hx
          have hxmem := Finset.mem_coe.mp hx
          have hmemK : x₀ + ((g x : ℤ) : ℝ) • v ∈ K := by
            rw [← hg x hxmem]
            rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hxmem
            exact hxmem.1.1
          have hIcc := setOf_add_smul_mem_subset_Icc hconv hsymm hvpos hbase hmemK
          rw [Set.mem_Icc] at hIcc
          rw [Finset.mem_coe, Finset.mem_Icc]
          omega
        · intro a ha b' hb' hab
          rw [hg a (Finset.mem_coe.mp ha), hg b' (Finset.mem_coe.mp hb'), hab]
        · rw [Int.card_Icc]
          omega
    -- The minima of the projected lattice are comparable with those of the lattice.
    have hstep : ∀ j : ℕ,
        (2 : ℝ) ^ (m + 1) / successiveMinimum (L.map (π : E →+ W)) (π '' K) (j + 1) + 1 ≤
          (2 : ℝ) ^ (m + 1 + 1) / successiveMinimum L K (j + 1 + 1) + 1 := by
      intro j
      rcases eq_or_lt_of_le
        (successiveMinimum_nonneg (L.map (π : E →+ W)) (π '' K) (j + 1)) with hbar | hbar
      · rw [← hbar, div_zero]
        have := div_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ (m + 1 + 1))
          (successiveMinimum_nonneg L K (j + 1 + 1))
        linarith
      obtain ⟨t₀, ht₀, hshort₀⟩ := exists_of_successiveMinimum_pos hbar
      have hlift : ∀ t : ℝ, 0 ≤ t →
          HasIndependentShort (L.map (π : E →+ W)) (π '' K) (j + 1) t →
          successiveMinimum L K (j + 1 + 1) ≤ 2 * t := by
        intro t ht hshort
        have h2 : gauge K v ≤ 2 * t :=
          gauge_le_two_mul_of_mem_map hconv hK₀ hsymm π hvL hπv hker hmin ht
            (hshort.of_le (Nat.le_add_left 1 j))
        refine le_trans (successiveMinimum_le (le_max_of_le_left (gauge_nonneg v))
          (hasIndependentShort_succ_of_isCompl hcompl hconv hclosed hK₀ hvonN hsymm hvL hvne ht
            hshort)) (max_le h2 ?_)
        linarith
      have hpos2 : 0 < successiveMinimum L K (j + 1 + 1) := by
        refine lt_of_lt_of_le hlampos (successiveMinimum_mono (by omega)
          ⟨max (gauge K v) (t₀ + gauge K v / 2), le_max_of_le_left (gauge_nonneg v), ?_⟩)
        exact hasIndependentShort_succ_of_isCompl hcompl hconv hclosed hK₀ hvonN hsymm hvL hvne ht₀
          hshort₀
      have hhalf : successiveMinimum L K (j + 1 + 1) / 2 ≤
          successiveMinimum (L.map (π : E →+ W)) (π '' K) (j + 1) := by
        apply le_successiveMinimum ⟨t₀, ht₀, hshort₀⟩
        intro s hs hss
        have := hlift s hs hss
        linarith
      have hpow : (2 : ℝ) ^ (m + 1 + 1) = 2 ^ (m + 1) * 2 := by ring
      have hmain : (2 : ℝ) ^ (m + 1) / successiveMinimum (L.map (π : E →+ W)) (π '' K) (j + 1) ≤
          (2 : ℝ) ^ (m + 1 + 1) / successiveMinimum L K (j + 1 + 1) := by
        rw [div_le_div_iff₀ hbar hpos2, hpow, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
      linarith
    -- Assemble.
    rw [Fin.prod_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, zero_add]
    have hcountR : ((K ∩ (L : Set E)).ncard : ℝ) ≤ (2 * (⌊2 / gauge K v⌋₊ : ℝ) + 1) *
        (((π '' K) ∩ ((L.map (π : E →+ W)) : Set W)).ncard : ℝ) := by
      exact_mod_cast hcount
    refine hcountR.trans (mul_le_mul ?_ ?_ (Nat.cast_nonneg _)
      (le_trans zero_le_one (one_le_div_successiveMinimum_add_one L K (by positivity) 1)))
    · rw [← hgauge]
      have hfloor : ((⌊2 / gauge K v⌋₊ : ℕ) : ℝ) ≤ 2 / gauge K v := Nat.floor_le (by positivity)
      have hpow : (4 : ℝ) ≤ 2 ^ (m + 1 + 1) := by
        have h2 : (2 : ℝ) ^ 2 ≤ 2 ^ (m + 1 + 1) := pow_le_pow_right₀ one_le_two (by omega)
        norm_num at h2
        exact h2
      have hdiv : (4 : ℝ) / gauge K v ≤ 2 ^ (m + 1 + 1) / gauge K v :=
        div_le_div_of_nonneg_right hpow hvpos.le
      have hfour : (4 : ℝ) / gauge K v = 2 * (2 / gauge K v) := by ring
      linarith
    · refine hIH.trans (Finset.prod_le_prod ?_ fun i _ ↦ hstep i)
      intro i _
      exact le_trans zero_le_one (one_le_div_successiveMinimum_add_one _ _ (by positivity) _)

/-- **The lattice point count.** A symmetric convex body contains at most
`∏ᵢ (2 ^ (d + 1) / λᵢ + 1)` points of a discrete subgroup of a `d`-dimensional real normed space,
where `λ₁ ≤ ⋯ ≤ λ_d` are the successive minima of the subgroup with respect to the body.

This is the statement `(†)` that the rank reduction of properization
consumes; the volume form of Minkowski's second theorem is not needed for it, and its proof uses no
measure theory. Indices beyond the rank of the subgroup contribute a factor one, because their
minimum is the infimum of an empty set. -/
theorem ncard_inter_le_prod_successiveMinimum {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (L : AddSubgroup E) [DiscreteTopology L] (K : Set E)
    (hconv : Convex ℝ K) (hclosed : IsClosed K) (hK₀ : K ∈ 𝓝 0) (hbdd : Bornology.IsBounded K)
    (hsymm : ∀ x ∈ K, -x ∈ K) :
    ((K ∩ (L : Set E)).ncard : ℝ) ≤
      ∏ i : Fin (finrank ℝ E),
        ((2 : ℝ) ^ (finrank ℝ E + 1) / successiveMinimum L K ((i : ℕ) + 1) + 1) :=
  ncard_inter_le_prod_aux _ L K rfl hconv hclosed hK₀ hbdd hsymm

/-! ## Minkowski's first theorem -/

/-- **Minkowski's first theorem** in terms of the first minimum: a dilate of `K` whose volume
exceeds `2 ^ d` times the covolume of `L` reaches the first minimum. -/
theorem successiveMinimum_one_le_of_measure_lt [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Countable L] {μ : Measure E} [μ.IsAddHaarMeasure] {F : Set E}
    (fund : IsAddFundamentalDomain L F μ) (hsymm : ∀ x ∈ K, -x ∈ K) (hconv : Convex ℝ K) {t : ℝ}
    (ht : 0 ≤ t) (hvol : μ F * 2 ^ finrank ℝ E < μ (t • K)) :
    successiveMinimum L K 1 ≤ t := by
  have hsymm' : ∀ y ∈ t • K, -y ∈ t • K := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨-z, hsymm z hz, by simp only [smul_neg]⟩
  obtain ⟨x, hx, hxK⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure fund hsymm' (hconv.smul t) hvol
  refine successiveMinimum_le ht ⟨fun _ ↦ (x : E), ?_, ?_⟩
  · apply linearIndependent_unique_iff.mpr
    simpa only [ne_eq, ZeroMemClass.coe_eq_zero] using hx
  · intro _
    exact ⟨x.2, hxK⟩

/-- **Minkowski's first theorem** in the quantitative form that Minkowski's second theorem
generalizes: `λ₁ ^ d * vol K ≤ 2 ^ d * covol L`.

The second theorem replaces the power `λ₁ ^ d` by the product `λ₁ ⋯ λ_d` of all the minima. It is
used by the saturated quotient proof of `exists_twoProperGAP_container` in
`Chang.Properization`. -/
theorem ofReal_pow_successiveMinimum_one_mul_measure_le [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Countable L] {μ : Measure E} [μ.IsAddHaarMeasure] {F : Set E}
    (fund : IsAddFundamentalDomain L F μ) (hsymm : ∀ x ∈ K, -x ∈ K) (hconv : Convex ℝ K)
    (hbdd : Bornology.IsBounded K) (hne : ∃ t, 0 ≤ t ∧ HasIndependentShort L K 1 t) :
    ENNReal.ofReal (successiveMinimum L K 1 ^ finrank ℝ E) * μ K ≤ 2 ^ finrank ℝ E * μ F := by
  have hdpos : 0 < finrank ℝ E := by
    obtain ⟨-, -, v, hindep, -⟩ := hne
    exact Module.finrank_pos_iff.mpr ⟨⟨v 0, 0, hindep.ne_zero 0⟩⟩
  have hKtop : μ K ≠ ⊤ :=
    ((measure_mono subset_closure).trans_lt hbdd.isCompact_closure.measure_lt_top).ne
  have hstep : ∀ t : ℝ, 0 ≤ t → t < successiveMinimum L K 1 →
      ENNReal.ofReal (t ^ finrank ℝ E) * μ K ≤ 2 ^ finrank ℝ E * μ F := by
    intro t ht hlt
    by_contra! hcon
    refine absurd (successiveMinimum_one_le_of_measure_lt fund hsymm hconv ht ?_) (not_le.mpr hlt)
    rw [μ.addHaar_smul_of_nonneg ht K, mul_comm (μ F)]
    exact hcon
  rcases eq_or_lt_of_le (successiveMinimum_nonneg L K 1) with hlam | hlam
  · rw [← hlam, zero_pow hdpos.ne', ENNReal.ofReal_zero, zero_mul]
    simp
  · refine le_of_tendsto (f := fun t : ℝ ↦ ENNReal.ofReal (t ^ finrank ℝ E) * μ K)
      (x := nhdsWithin (successiveMinimum L K 1) (Set.Iio (successiveMinimum L K 1)))
      (ENNReal.Tendsto.mul_const (((ENNReal.continuous_ofReal.comp
        (continuous_pow (finrank ℝ E))).tendsto _).mono_left nhdsWithin_le_nhds)
        (Or.inr hKtop)) ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_gt_nhds hlam)] with t htlt htpos
    exact hstep t htpos.le htlt

end

end ConvexGeometry

end DenseSetsWithoutLargeSumsets
