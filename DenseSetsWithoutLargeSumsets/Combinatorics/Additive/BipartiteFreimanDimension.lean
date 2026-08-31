/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.FreimanDimensionSumsetBounds
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Bipartite Freiman dimension

This file formalizes the bipartite relation space associated with two finite sets.  Unlike the
usual Freiman relation space, it records only relations with one summand on each shore.
-/

namespace DenseSetsWithoutLargeSumsets

open scoped BigOperators Pointwise

noncomputable section

/-- The lower bound supplied by Ruzsa's asymmetric theorem to a fiber of size `c`. -/
private def bipartiteFiberBound (s k c : ℕ) : ℕ :=
  k + (Finset.Ico 1 c).sum (fun t ↦ min s (k - t))

private lemma bipartiteFiberWeight_antitone (s k : ℕ) :
    Antitone (fun t ↦ min s (k - t)) := by
  intro a b hab
  exact min_le_min_left s (Nat.sub_le_sub_left hab k)

private lemma sum_Ico_shift_le_of_antitone (w : ℕ → ℕ) (hw : Antitone w)
    {a b : ℕ} (ha : 1 ≤ a) :
    (Finset.Ico a (a + b)).sum w ≤ (Finset.Ico 1 (1 + b)).sum w := by
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  apply Finset.sum_le_sum
  intro t ht
  apply hw
  omega

/-- Merging two nonempty fibers cannot increase the concave fiber lower bound. -/
private lemma bipartiteFiberBound_merge {s k a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (_hab : a + b - 1 ≤ k) :
    bipartiteFiberBound s k (a + b - 1) + bipartiteFiberBound s k 1 ≤
      bipartiteFiberBound s k a + bipartiteFiberBound s k b := by
  simp only [bipartiteFiberBound, Finset.Ico_self, Finset.sum_empty, add_zero]
  rw [← Finset.sum_Ico_consecutive (fun t ↦ min s (k - t)) ha]
  · have hrewrite : a + b - 1 = a + (b - 1) := by omega
    have hshift := sum_Ico_shift_le_of_antitone (fun t ↦ min s (k - t))
      (bipartiteFiberWeight_antitone s k) (a := a) (b := b - 1) ha
    have hbwrite : 1 + (b - 1) = b := by omega
    rw [hrewrite]
    rw [hbwrite] at hshift
    simpa [add_assoc, add_left_comm, add_comm] using hshift
  · omega

/-- Discrete concavity: among positive fibers with fixed total, one large fiber and singleton
fibers minimize the sum of the asymmetric lower bounds. -/
private lemma bipartiteFiberBound_list (s k : ℕ) (cs : List ℕ)
    (hne : cs ≠ []) (hpos : ∀ c ∈ cs, 1 ≤ c) (hsum : cs.sum ≤ k) :
    bipartiteFiberBound s k (cs.sum - cs.length + 1) + (cs.length - 1) * k ≤
      (cs.map (bipartiteFiberBound s k)).sum := by
  induction cs using List.twoStepInduction with
  | nil => exact (hne rfl).elim
  | singleton c =>
      have hc : 1 ≤ c := hpos c (by simp)
      simp [Nat.sub_add_cancel hc]
  | cons_cons a b cs ih₀ ih₁ =>
      have ha : 1 ≤ a := hpos a (by simp)
      have hb : 1 ≤ b := hpos b (by simp)
      let merged := a + b - 1
      have hmerged : 1 ≤ merged := by dsimp [merged]; omega
      have htailpos : ∀ c ∈ merged :: cs, 1 ≤ c := by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hmerged
        · exact hpos c (by simp [hc])
      have hmergedSum : (merged :: cs).sum ≤ k := by
        dsimp [merged]
        simp only [List.sum_cons] at hsum ⊢
        omega
      have hrec := ih₁ merged (by simp) htailpos hmergedSum
      have hmerge := bipartiteFiberBound_merge (s := s) (k := k) ha hb
        (by simp only [List.sum_cons] at hsum; omega)
      have hlen : cs.length ≤ cs.sum :=
        List.length_le_sum_of_one_le cs (fun c hc ↦ hpos c (by simp [hc]))
      simp only [List.sum_cons, List.length_cons, List.map_cons] at hrec ⊢
      dsimp [merged] at hrec
      have hindex :
          a + (b + cs.sum) - (cs.length + 1 + 1) + 1 =
            a + b - 1 + cs.sum - (cs.length + 1) + 1 := by omega
      rw [hindex]
      have hone : bipartiteFiberBound s k 1 = k := by simp [bipartiteFiberBound]
      rw [hone] at hmerge
      simp only [Nat.add_sub_cancel, Nat.succ_mul] at hrec ⊢
      omega

private lemma twice_mul_le_twice_sum_min {s p k : ℕ} (hp : 1 ≤ p) (hps : p ≤ s)
    (hsk : s + 1 ≤ k) :
    k * (s - p + 1) ≤ 2 * (Finset.Ico p k).sum (fun h ↦ min s h) := by
  refine Nat.le_induction (m := s + 1) ?_ ?_ k hsk
  · have hmin : (Finset.Ico p (s + 1)).sum (fun h ↦ min s h) =
        (Finset.Ico p (s + 1)).sum id := by
      apply Finset.sum_congr rfl
      intro h hh
      simp only [Finset.mem_Ico] at hh
      exact Nat.min_eq_right (by omega)
    rw [hmin]
    have hdecomp := Finset.sum_Ico_consecutive id (Nat.zero_le p) (by omega : p ≤ s + 1)
    have hzero (n : ℕ) : Finset.Ico 0 n = Finset.range n := by ext; simp
    rw [hzero, hzero] at hdecomp
    change (∑ i ∈ Finset.range p, i) + (Finset.Ico p (s + 1)).sum id =
      ∑ i ∈ Finset.range (s + 1), i at hdecomp
    rw [Finset.sum_range_id, Finset.sum_range_id] at hdecomp
    have consecutive_even (n : ℕ) : 2 ∣ n * (n - 1) :=
      (Nat.even_mul_pred_self n).two_dvd
    have hdiv1 : 2 * ((s + 1) * s / 2) = (s + 1) * s := by
      have h := Nat.mul_div_cancel' (consecutive_even (s + 1))
      simpa only [Nat.add_sub_cancel] using h
    have hdiv2 : 2 * (p * (p - 1) / 2) = p * (p - 1) := by
      exact Nat.mul_div_cancel' (consecutive_even p)
    norm_num only [Nat.add_sub_cancel] at hdecomp
    have hdecomp2 := congrArg (fun x : ℕ ↦ 2 * x) hdecomp
    rw [Nat.mul_add, hdiv2, hdiv1] at hdecomp2
    have hsub : s - p + p = s := Nat.sub_add_cancel hps
    generalize hq : s - p = q at *
    have hs : s = q + p := by omega
    subst s
    generalize hr : p - 1 = r at *
    have hp' : p = r + 1 := by omega
    subst p
    nlinarith
  · intro n hsn hn
    rw [Finset.sum_Ico_succ_top (a := p) (b := n) (hps.trans (by omega))]
    rw [Nat.min_eq_left (by omega : s ≤ n)]
    have hinc : s - p + 1 ≤ 2 * s := by omega
    calc
      (n + 1) * (s - p + 1) = n * (s - p + 1) + (s - p + 1) := by
        rw [Nat.add_mul, one_mul]
      _ ≤ 2 * (Finset.Ico p n).sum (fun h ↦ min s h) + 2 * s :=
        Nat.add_le_add hn hinc
      _ = 2 * ((Finset.Ico p n).sum (fun h ↦ min s h) + s) := by
        rw [Nat.mul_add]

private lemma bipartite_geometric_numerical {s p k : ℕ} (hp : 1 ≤ p) (_hpk : p ≤ k)
    (hsk : s + 1 ≤ k) :
    k * (s + p + 1) ≤
      2 * (p * k + (Finset.Ico p k).sum (fun h ↦ min s h)) := by
  by_cases hps : p ≤ s
  · have hsum := twice_mul_le_twice_sum_min hp hps hsk
    generalize hq : s - p = q at *
    have hs : s = q + p := by omega
    subst s
    calc
      k * (q + p + p + 1) = 2 * (p * k) + k * (q + 1) := by ring
      _ ≤ 2 * (p * k) + 2 * (Finset.Ico p k).sum (fun h ↦ min (q + p) h) :=
        Nat.add_le_add_left hsum _
      _ = 2 * (p * k + (Finset.Ico p k).sum (fun h ↦ min (q + p) h)) := by ring
  · have hsp : s + 1 ≤ p := by omega
    have hmain : k * (s + p + 1) ≤ 2 * (p * k) := by nlinarith
    exact hmain.trans (Nat.mul_le_mul_left 2 (Nat.le_add_right _ _))

private lemma bipartiteFiberBound_extreme {s p k : ℕ} (hp : 1 ≤ p) (hpk : p ≤ k) :
    bipartiteFiberBound s k (k - p + 1) + (p - 1) * k =
      p * k + (Finset.Ico p k).sum (fun h ↦ min s h) := by
  have hreflect := Finset.sum_Ico_reflect (fun h ↦ min s h) 1
    (m := k - p + 1) (n := k) (by omega : k - p + 1 ≤ k + 1)
  have hlower : k + 1 - (k - p + 1) = p := by omega
  have hupper : k + 1 - 1 = k := by omega
  rw [hlower, hupper] at hreflect
  simp only [bipartiteFiberBound]
  rw [hreflect]
  generalize hr : p - 1 = r at *
  have hp' : p = r + 1 := by omega
  subst p
  ring

/-- Arithmetic interface for the quotient-fiber proof of the geometric lemma. -/
private lemma bipartite_geometric_of_fiber_cards {s d k : ℕ} (cs : List ℕ)
    (_hk : 1 ≤ k) (hne : cs ≠ []) (hpos : ∀ c ∈ cs, 1 ≤ c)
    (hsum : cs.sum = k) (hs : s + 1 ≤ k) (hd : d ≤ s + cs.length - 1)
    {N : ℕ} (hruzsa : (cs.map (bipartiteFiberBound s k)).sum ≤ N) :
    k * (d + 2) ≤ 2 * N := by
  let p := cs.length
  have hp : 1 ≤ p := List.length_pos_of_ne_nil hne
  have hpk : p ≤ k := by
    dsimp [p]
    rw [← hsum]
    exact List.length_le_sum_of_one_le cs hpos
  have hconcave := bipartiteFiberBound_list s k cs hne hpos hsum.le
  rw [hsum] at hconcave
  have hextreme := bipartiteFiberBound_extreme (s := s) hp hpk
  have hnumeric := bipartite_geometric_numerical (s := s) hp hpk hs
  have hdim : k * (d + 2) ≤ k * (s + p + 1) := by
    apply Nat.mul_le_mul_left
    dsimp [p] at hd ⊢
    omega
  calc
    k * (d + 2) ≤ k * (s + p + 1) := hdim
    _ ≤ 2 * (p * k + (Finset.Ico p k).sum (fun h ↦ min s h)) := hnumeric
    _ = 2 * (bipartiteFiberBound s k (k - p + 1) + (p - 1) * k) := by
      rw [hextreme]
    _ ≤ 2 * (cs.map (bipartiteFiberBound s k)).sum := Nat.mul_le_mul_left 2 hconcave
    _ ≤ 2 * N := Nat.mul_le_mul_left 2 hruzsa

section GeometricFibers

variable {D : ℕ}

/-- The direction of the affine span of a finite set. -/
private def finiteDirection (S : Finset (Fin D → ℝ)) : Submodule ℝ (Fin D → ℝ) :=
  (affineSpan ℝ (S : Set (Fin D → ℝ))).direction

/-- A fiber of `C` modulo the direction generated by `E`. -/
private def directionFiber (C E : Finset (Fin D → ℝ))
    (z : (Fin D → ℝ) ⧸ finiteDirection E) : Finset (Fin D → ℝ) := by
  classical
  exact C.filter (fun c ↦ (Submodule.mkQ (finiteDirection E)) c = z)

/-- The finite image of `C` in the quotient by the direction generated by `E`. -/
private def directionQuotientImage (C E : Finset (Fin D → ℝ)) :
    Finset ((Fin D → ℝ) ⧸ finiteDirection E) := by
  classical
  exact C.image (Submodule.mkQ (finiteDirection E))

/-- Cardinalities of the nonempty fibers of `C` modulo the direction generated by `E`. -/
private def directionFiberCards (C E : Finset (Fin D → ℝ)) : List ℕ := by
  classical
  exact ((directionQuotientImage C E).toList.map fun z ↦ (directionFiber C E z).card)

private lemma directionFiber_nonempty {C E : Finset (Fin D → ℝ)}
    {z : (Fin D → ℝ) ⧸ finiteDirection E}
    (hz : z ∈ directionQuotientImage C E) :
    (directionFiber C E z).Nonempty := by
  classical
  rw [directionQuotientImage] at hz
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨c, Finset.mem_filter.2 ⟨hc, rfl⟩⟩

private lemma directionFiberCards_ne_nil {C E : Finset (Fin D → ℝ)}
    (hC : C.Nonempty) : directionFiberCards C E ≠ [] := by
  classical
  intro hnil
  have : directionQuotientImage C E = ∅ := by
    simpa [directionFiberCards] using congrArg List.length hnil
  rw [directionQuotientImage] at this
  exact (Finset.image_nonempty.2 hC).ne_empty this

private lemma one_le_of_mem_directionFiberCards {C E : Finset (Fin D → ℝ)}
    {c : ℕ} (hc : c ∈ directionFiberCards C E) : 1 ≤ c := by
  classical
  simp only [directionFiberCards, List.mem_map, Finset.mem_toList] at hc
  obtain ⟨z, hz, rfl⟩ := hc
  exact Finset.card_pos.mpr (directionFiber_nonempty hz)

private lemma sum_directionFiberCards (C E : Finset (Fin D → ℝ)) :
    (directionFiberCards C E).sum = C.card := by
  classical
  let π := Submodule.mkQ (finiteDirection E)
  have h := Finset.card_eq_sum_card_fiberwise
    (s := C) (t := directionQuotientImage C E) (f := π)
    (fun c hc ↦ by
      rw [directionQuotientImage]
      exact Finset.mem_image.2 ⟨c, hc, rfl⟩)
  simpa [directionFiberCards, directionFiber, π] using h.symm

private lemma length_directionFiberCards (C E : Finset (Fin D → ℝ)) :
    (directionFiberCards C E).length =
      (directionQuotientImage C E).card := by
  classical
  simp [directionFiberCards]

private lemma quotient_eq_of_mem {E : Finset (Fin D → ℝ)} {x y : Fin D → ℝ}
    (hx : x ∈ E) (hy : y ∈ E) :
    (Submodule.mkQ (finiteDirection E)) x = (Submodule.mkQ (finiteDirection E)) y := by
  change (Submodule.Quotient.mk x : (Fin D → ℝ) ⧸ finiteDirection E) =
    Submodule.Quotient.mk y
  rw [Submodule.Quotient.eq]
  exact (affineSpan ℝ (E : Set (Fin D → ℝ))).vsub_mem_direction
    (subset_affineSpan ℝ (E : Set (Fin D → ℝ)) hx)
    (subset_affineSpan ℝ (E : Set (Fin D → ℝ)) hy)

private lemma directionFiber_add_pairwiseDisjoint (C E : Finset (Fin D → ℝ)) :
    (directionQuotientImage C E : Set ((Fin D → ℝ) ⧸ finiteDirection E)).PairwiseDisjoint
      (fun z ↦ directionFiber C E z + E) := by
  classical
  intro z hz z' hz' hzz'
  change Disjoint (directionFiber C E z + E) (directionFiber C E z' + E)
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [Finset.mem_add] at hx hx'
  obtain ⟨c, hc, e, he, rfl⟩ := hx
  obtain ⟨c', hc', e', he', hsum⟩ := hx'
  rw [directionFiber, Finset.mem_filter] at hc hc'
  apply hzz'
  rw [← hc.2, ← hc'.2]
  have hq := congrArg (Submodule.mkQ (finiteDirection E)) hsum
  simp only [map_add] at hq
  rw [quotient_eq_of_mem he he'] at hq
  exact (add_right_cancel hq).symm

private lemma biUnion_directionFiber_add (C E : Finset (Fin D → ℝ)) :
    (directionQuotientImage C E).biUnion (fun z ↦ directionFiber C E z + E) = C + E := by
  classical
  ext x
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨z, hz, hx⟩
    rw [Finset.mem_add] at hx ⊢
    obtain ⟨c, hc, e, he, rfl⟩ := hx
    exact ⟨c, (Finset.mem_filter.mp hc).1, e, he, rfl⟩
  · intro hx
    rw [Finset.mem_add] at hx
    obtain ⟨c, hc, e, he, rfl⟩ := hx
    let z := (Submodule.mkQ (finiteDirection E)) c
    refine ⟨z, ?_, Finset.add_mem_add ?_ he⟩
    · rw [directionQuotientImage]
      exact Finset.mem_image.2 ⟨c, hc, rfl⟩
    · exact Finset.mem_filter.2 ⟨hc, rfl⟩

private lemma card_add_eq_sum_directionFibers (C E : Finset (Fin D → ℝ)) :
    (C + E).card =
      (directionQuotientImage C E).sum (fun z ↦ (directionFiber C E z + E).card) := by
  classical
  rw [← biUnion_directionFiber_add C E,
    Finset.card_biUnion (directionFiber_add_pairwiseDisjoint C E)]

private lemma finsetAffineDim_le_finrank_of_vsub {S : Finset (Fin D → ℝ)}
    (U : Submodule ℝ (Fin D → ℝ)) {p : Fin D → ℝ} (hp : p ∈ S)
    (hmem : ∀ x ∈ S, x - p ∈ U) : finsetAffineDim S ≤ Module.finrank ℝ U := by
  unfold finsetAffineDim
  rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ
    (s := (S : Set (Fin D → ℝ))) (p := p) hp]
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro z ⟨x, hx, rfl⟩
  simpa [vsub_eq_sub] using hmem x hx

private lemma finsetAffineDim_image_add_left (S : Finset (Fin D → ℝ)) (c : Fin D → ℝ) :
    finsetAffineDim (S.image fun x ↦ c + x) = finsetAffineDim S := by
  have hcoe :
      (((S.image fun x ↦ c + x : Finset (Fin D → ℝ)) : Set (Fin D → ℝ))) =
        c +ᵥ (S : Set (Fin D → ℝ)) := by
    ext x
    simp only [Finset.coe_image, Set.mem_image, Set.mem_vadd_set]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  unfold finsetAffineDim
  rw [direction_affineSpan, direction_affineSpan, hcoe, vectorSpan_vadd]

private lemma finsetAffineDim_directionFiber_add (C E : Finset (Fin D → ℝ))
    (hE : E.Nonempty) {z : (Fin D → ℝ) ⧸ finiteDirection E}
    (hz : z ∈ directionQuotientImage C E) :
    finsetAffineDim (directionFiber C E z + E) = finsetAffineDim E := by
  classical
  obtain ⟨c₀, hc₀⟩ := directionFiber_nonempty hz
  obtain ⟨e₀, he₀⟩ := hE
  apply Nat.le_antisymm
  · apply finsetAffineDim_le_finrank_of_vsub (finiteDirection E)
      (Finset.add_mem_add hc₀ he₀)
    intro x hx
    rw [Finset.mem_add] at hx
    obtain ⟨c, hc, e, he, rfl⟩ := hx
    have hcc : c - c₀ ∈ finiteDirection E := by
      rw [directionFiber, Finset.mem_filter] at hc hc₀
      have hq := hc.2.trans hc₀.2.symm
      change (Submodule.Quotient.mk c : (Fin D → ℝ) ⧸ finiteDirection E) =
        Submodule.Quotient.mk c₀ at hq
      rw [Submodule.Quotient.eq] at hq
      exact hq
    have hee : e - e₀ ∈ finiteDirection E :=
      (affineSpan ℝ (E : Set (Fin D → ℝ))).vsub_mem_direction
        (subset_affineSpan ℝ (E : Set (Fin D → ℝ)) he)
        (subset_affineSpan ℝ (E : Set (Fin D → ℝ)) he₀)
    have hmem := (finiteDirection E).add_mem hcc hee
    convert hmem using 1
    ring
  · rw [← finsetAffineDim_image_add_left E c₀]
    apply finsetAffineDim_mono
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨e, he, rfl⟩ := hx
    exact Finset.add_mem_add hc₀ he

private lemma bipartiteFiberBound_le_card_add_directionFiber
    (C E : Finset (Fin D → ℝ)) (hCcard : C.card = E.card) (hE : E.Nonempty)
    {z : (Fin D → ℝ) ⧸ finiteDirection E} (hz : z ∈ directionQuotientImage C E) :
    bipartiteFiberBound (finsetAffineDim E) E.card (directionFiber C E z).card ≤
      (directionFiber C E z + E).card := by
  classical
  have hfiber : (directionFiber C E z).Nonempty := directionFiber_nonempty hz
  have hcard : (directionFiber C E z).card ≤ E.card := by
    rw [← hCcard]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hruzsa := card_add_lower_bound_of_affineDim E (directionFiber C E z)
    hfiber hcard (by
      simpa [add_comm] using finsetAffineDim_directionFiber_add C E hE hz)
  have hend : (directionFiber C E z).card - 1 + 1 = (directionFiber C E z).card :=
    Nat.sub_add_cancel (Finset.card_pos.mpr hfiber)
  rw [← Finset.Ico_add_one_right_eq_Icc 1 ((directionFiber C E z).card - 1), hend]
    at hruzsa
  simpa [bipartiteFiberBound, add_comm] using hruzsa

private lemma sum_bipartiteFiberBounds_le_card_add
    (C E : Finset (Fin D → ℝ)) (hCcard : C.card = E.card)
    (hE : E.Nonempty) :
    ((directionFiberCards C E).map
      (bipartiteFiberBound (finsetAffineDim E) E.card)).sum ≤ (C + E).card := by
  classical
  rw [card_add_eq_sum_directionFibers]
  simpa [directionFiberCards] using
    Finset.sum_le_sum (fun z hz ↦
      bipartiteFiberBound_le_card_add_directionFiber C E hCcard hE hz)

/-- A chosen representative in `C` of a quotient fiber. -/
private def directionRepresentative (C E : Finset (Fin D → ℝ))
    (z : directionQuotientImage C E) : Fin D → ℝ := by
  classical
  have hz : (z : (Fin D → ℝ) ⧸ finiteDirection E) ∈
      C.image (Submodule.mkQ (finiteDirection E)) := by
    simpa [directionQuotientImage] using z.2
  exact Classical.choose (Finset.mem_image.mp hz)

private lemma directionRepresentative_mem (C E : Finset (Fin D → ℝ))
    (z : directionQuotientImage C E) : directionRepresentative C E z ∈ C := by
  classical
  exact (Classical.choose_spec (Finset.mem_image.mp (by
    simpa [directionQuotientImage] using z.2))).1

private lemma mkQ_directionRepresentative (C E : Finset (Fin D → ℝ))
    (z : directionQuotientImage C E) :
    (Submodule.mkQ (finiteDirection E)) (directionRepresentative C E z) = z := by
  classical
  exact (Classical.choose_spec (Finset.mem_image.mp (by
    simpa [directionQuotientImage] using z.2))).2

private lemma directionRepresentative_injective (C E : Finset (Fin D → ℝ)) :
    Function.Injective (directionRepresentative C E) := by
  intro z z' h
  apply Subtype.ext
  rw [← mkQ_directionRepresentative C E z, ← mkQ_directionRepresentative C E z', h]

/-- One chosen representative from every quotient fiber. -/
private def directionRepresentatives (C E : Finset (Fin D → ℝ)) :
    Finset (Fin D → ℝ) := by
  classical
  exact Finset.univ.image (directionRepresentative C E)

private lemma card_directionRepresentatives (C E : Finset (Fin D → ℝ)) :
    (directionRepresentatives C E).card = (directionQuotientImage C E).card := by
  classical
  rw [directionRepresentatives, Finset.card_image_of_injective _
    (directionRepresentative_injective C E), Finset.card_univ, Fintype.card_coe]

private lemma mem_directionRepresentatives (C E : Finset (Fin D → ℝ))
    (z : directionQuotientImage C E) :
    directionRepresentative C E z ∈ directionRepresentatives C E := by
  classical
  rw [directionRepresentatives]
  exact Finset.mem_image.2 ⟨z, Finset.mem_univ _, rfl⟩

private lemma finsetAffineDim_add_le_direction_add_fibers
    (C E : Finset (Fin D → ℝ)) (hC : C.Nonempty) (hE : E.Nonempty) :
    finsetAffineDim (C + E) ≤
      finsetAffineDim E + (directionQuotientImage C E).card - 1 := by
  classical
  have hQ : (directionQuotientImage C E).Nonempty := by
    rw [directionQuotientImage, Finset.image_nonempty]
    exact hC
  let z₀ := hQ.choose
  let r₀ := directionRepresentative C E ⟨z₀, hQ.choose_spec⟩
  let R := directionRepresentatives C E
  let T := (R.erase r₀).image (fun r ↦ r - r₀)
  let W : Submodule ℝ (Fin D → ℝ) := Submodule.span ℝ (T : Set (Fin D → ℝ))
  obtain ⟨e₀, he₀⟩ := hE
  have hr₀C : r₀ ∈ C := directionRepresentative_mem C E ⟨z₀, hQ.choose_spec⟩
  have hdim : finsetAffineDim (C + E) ≤ Module.finrank ℝ
      ↥((finiteDirection E : Submodule ℝ (Fin D → ℝ)) ⊔ W) := by
    apply finsetAffineDim_le_finrank_of_vsub
      ((finiteDirection E : Submodule ℝ (Fin D → ℝ)) ⊔ W)
      (Finset.add_mem_add hr₀C he₀)
    intro x hx
    rw [Finset.mem_add] at hx
    obtain ⟨c, hc, e, he, rfl⟩ := hx
    have hzc : (Submodule.mkQ (finiteDirection E)) c ∈ directionQuotientImage C E := by
      rw [directionQuotientImage]
      exact Finset.mem_image.2 ⟨c, hc, rfl⟩
    let zc : directionQuotientImage C E :=
      ⟨(Submodule.mkQ (finiteDirection E)) c, hzc⟩
    let r := directionRepresentative C E zc
    have hcr : c - r ∈ finiteDirection E := by
      have hq : (Submodule.mkQ (finiteDirection E)) c =
          (Submodule.mkQ (finiteDirection E)) r := by
        change (zc : (Fin D → ℝ) ⧸ finiteDirection E) =
          (Submodule.mkQ (finiteDirection E)) r
        exact (mkQ_directionRepresentative C E zc).symm
      change (Submodule.Quotient.mk c : (Fin D → ℝ) ⧸ finiteDirection E) =
        Submodule.Quotient.mk r at hq
      rw [Submodule.Quotient.eq] at hq
      exact hq
    have hee : e - e₀ ∈ finiteDirection E :=
      (affineSpan ℝ (E : Set (Fin D → ℝ))).vsub_mem_direction
        (subset_affineSpan ℝ (E : Set (Fin D → ℝ)) he)
        (subset_affineSpan ℝ (E : Set (Fin D → ℝ)) he₀)
    have hrr : r - r₀ ∈ W := by
      by_cases hrr₀ : r = r₀
      · simp [hrr₀, W]
      · apply Submodule.subset_span
        rw [Finset.mem_coe]
        change r - r₀ ∈ (R.erase r₀).image (fun u ↦ u - r₀)
        rw [Finset.mem_image]
        exact ⟨r, Finset.mem_erase.2 ⟨hrr₀, mem_directionRepresentatives C E zc⟩, rfl⟩
    have hV : c - r + (e - e₀) ∈ finiteDirection E :=
      (finiteDirection E).add_mem hcr hee
    have hsum := ((finiteDirection E : Submodule ℝ (Fin D → ℝ)) ⊔ W).add_mem
      ((le_sup_left : finiteDirection E ≤
        (finiteDirection E : Submodule ℝ (Fin D → ℝ)) ⊔ W) hV)
      ((le_sup_right : W ≤
        (finiteDirection E : Submodule ℝ (Fin D → ℝ)) ⊔ W) hrr)
    convert hsum using 1
    ring
  apply hdim.trans
  apply (Submodule.finrank_add_le_finrank_add_finrank (finiteDirection E) W).trans
  have hTcard : T.card = (directionQuotientImage C E).card - 1 := by
    dsimp [T]
    rw [Finset.card_image_of_injective]
    · rw [Finset.card_erase_of_mem]
      · rw [card_directionRepresentatives]
      · exact mem_directionRepresentatives C E ⟨z₀, hQ.choose_spec⟩
    · intro x y hxy
      exact sub_left_injective hxy
  have hW : Module.finrank ℝ W ≤ (directionQuotientImage C E).card - 1 :=
    (finrank_span_finset_le_card T).trans_eq hTcard
  have hQpos : 1 ≤ (directionQuotientImage C E).card := Finset.card_pos.mpr hQ
  rw [show finsetAffineDim E + (directionQuotientImage C E).card - 1 =
    finsetAffineDim E + ((directionQuotientImage C E).card - 1) by omega]
  exact Nat.add_le_add (by rfl) hW

/-- Equal-shore geometric sumset bound. This is the geometric lemma in the manuscript, written
without division so that its natural-number content is explicit. -/
theorem card_mul_affineDim_add_two_le_two_mul_card_add
    (C E : Finset (Fin D → ℝ)) (hC : C.Nonempty) (hE : E.Nonempty)
    (hcard : C.card = E.card) :
    C.card * (finsetAffineDim (C + E) + 2) ≤ 2 * (C + E).card := by
  let cs := directionFiberCards C E
  apply bipartite_geometric_of_fiber_cards (s := finsetAffineDim E) (cs := cs)
  · exact Finset.card_pos.mpr hC
  · exact directionFiberCards_ne_nil hC
  · intro c hc
    exact one_le_of_mem_directionFiberCards hc
  · exact (sum_directionFiberCards C E).trans rfl
  · simpa [hcard] using finsetAffineDim_add_one_le_card E hE
  · dsimp [cs]
    rw [length_directionFiberCards]
    exact finsetAffineDim_add_le_direction_add_fibers C E hC hE
  · simpa [cs, hcard] using sum_bipartiteFiberBounds_le_card_add C E hcard hE

end GeometricFibers

/-- The ambient space of pairs of real-valued functions on two finite shores. -/
abbrev BipartiteFunctionSpace {G : Type*} (A B : Finset G) :=
  (A → ℝ) × (B → ℝ)

/-- Pairs of functions preserving every additive relation with one term in each shore. -/
def bipartiteFreimanHom {G : Type*} [Add G] (A B : Finset G) :
    Submodule ℝ (BipartiteFunctionSpace A B) where
  carrier := {p | ∀ a a' : A, ∀ b b' : B,
    (a : G) + b = a' + b' → p.1 a + p.2 b = p.1 a' + p.2 b'}
  zero_mem' := by simp
  add_mem' := by
    rintro f g hf hg a a' b b' hab
    dsimp
    calc
      f.1 a + g.1 a + (f.2 b + g.2 b) =
          (f.1 a + f.2 b) + (g.1 a + g.2 b) := by ring
      _ = (f.1 a' + f.2 b') + (g.1 a' + g.2 b') := by
        rw [hf a a' b b' hab, hg a a' b b' hab]
      _ = f.1 a' + g.1 a' + (f.2 b' + g.2 b') := by ring
  smul_mem' := by
    rintro c f hf a a' b b' hab
    dsimp
    calc
      c * f.1 a + c * f.2 b = c * (f.1 a + f.2 b) := by ring
      _ = c * (f.1 a' + f.2 b') := by rw [hf a a' b b' hab]
      _ = c * f.1 a' + c * f.2 b' := by ring

/-- The dimension of the bipartite Freiman-homomorphism space. -/
def bipartiteFreimanHomDim {G : Type*} [Add G] (A B : Finset G) : ℕ :=
  Module.finrank ℝ (bipartiteFreimanHom A B)

/-- The bipartite Freiman dimension, with the two independent constant directions removed. -/
def bipartiteFreimanDim {G : Type*} [Add G] (A B : Finset G) : ℕ :=
  bipartiteFreimanHomDim A B - 2

/-- Independently constant functions on the two shores are bipartite Freiman homomorphisms. -/
def bipartiteConstants {G : Type*} [Add G] (A B : Finset G) :
    (ℝ × ℝ) →ₗ[ℝ] bipartiteFreimanHom A B where
  toFun c := ⟨(fun _ ↦ c.1, fun _ ↦ c.2), by
    intro a a' b b' _
    rfl⟩
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

lemma bipartiteConstants_injective {G : Type*} [Add G] {A B : Finset G}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    Function.Injective (bipartiteConstants A B) := by
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hx := congrFun (congrArg (fun z : bipartiteFreimanHom A B ↦ z.1.1) h) ⟨a, ha⟩
  have hy := congrFun (congrArg (fun z : bipartiteFreimanHom A B ↦ z.1.2) h) ⟨b, hb⟩
  exact Prod.ext hx hy

lemma two_le_bipartiteFreimanHomDim {G : Type*} [Add G] {A B : Finset G}
    (hA : A.Nonempty) (hB : B.Nonempty) : 2 ≤ bipartiteFreimanHomDim A B := by
  unfold bipartiteFreimanHomDim
  have hle := LinearMap.finrank_le_finrank_of_injective (bipartiteConstants_injective hA hB)
  simpa using hle

lemma bipartiteFreimanDim_add_two {G : Type*} [Add G] {A B : Finset G}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    bipartiteFreimanDim A B + 2 = bipartiteFreimanHomDim A B := by
  exact Nat.sub_add_cancel (two_le_bipartiteFreimanHomDim hA hB)

/-- Evaluation at a point of the left shore, as a functional on the relation space. -/
def bipartiteEvalLeft {G : Type*} [Add G] (A B : Finset G) (a : A) :
    Module.Dual ℝ (bipartiteFreimanHom A B) where
  toFun f := f.1.1 a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation at a point of the right shore, as a functional on the relation space. -/
def bipartiteEvalRight {G : Type*} [Add G] (A B : Finset G) (b : B) :
    Module.Dual ℝ (bipartiteFreimanHom A B) where
  toFun f := f.1.2 b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma bipartiteEval_add_eq_add_of_relation {G : Type*} [Add G]
    (A B : Finset G) {a a' : A} {b b' : B}
    (h : (a : G) + b = a' + b') :
    bipartiteEvalLeft A B a + bipartiteEvalRight A B b =
      bipartiteEvalLeft A B a' + bipartiteEvalRight A B b' := by
  ext f
  exact f.2 a a' b b' h

/-- For subsets of the reals, the universal evaluation model creates no new cross-relations. -/
lemma relation_of_bipartiteEval_add_eq_add (A B : Finset ℝ) {a a' : A} {b b' : B}
    (h : bipartiteEvalLeft A B a + bipartiteEvalRight A B b =
      bipartiteEvalLeft A B a' + bipartiteEvalRight A B b') :
    (a : ℝ) + b = a' + b' := by
  let idHom : bipartiteFreimanHom A B :=
    ⟨(fun x ↦ (x : ℝ), fun y ↦ (y : ℝ)), by
      intro x x' y y' hxy
      exact hxy⟩
  exact LinearMap.congr_fun h idHom

lemma bipartiteEval_add_eq_add_iff (A B : Finset ℝ) {a a' : A} {b b' : B} :
    bipartiteEvalLeft A B a + bipartiteEvalRight A B b =
        bipartiteEvalLeft A B a' + bipartiteEvalRight A B b' ↔
      (a : ℝ) + b = a' + b' := by
  exact ⟨relation_of_bipartiteEval_add_eq_add A B,
    bipartiteEval_add_eq_add_of_relation A B⟩

lemma bipartiteEvalLeft_injective (A B : Finset ℝ) :
    Function.Injective (bipartiteEvalLeft A B) := by
  intro a a' h
  apply Subtype.ext
  let idHom : bipartiteFreimanHom A B :=
    ⟨(fun x ↦ (x : ℝ), fun y ↦ (y : ℝ)), by
      intro x x' y y' hxy
      exact hxy⟩
  exact LinearMap.congr_fun h idHom

lemma bipartiteEvalRight_injective (A B : Finset ℝ) :
    Function.Injective (bipartiteEvalRight A B) := by
  intro b b' h
  apply Subtype.ext
  let idHom : bipartiteFreimanHom A B :=
    ⟨(fun x ↦ (x : ℝ), fun y ↦ (y : ℝ)), by
      intro x x' y y' hxy
      exact hxy⟩
  exact LinearMap.congr_fun h idHom

/-- The left shore of the universal bipartite Freiman model. -/
def bipartiteUniversalLeft (A B : Finset ℝ) :
    Finset (Module.Dual ℝ (bipartiteFreimanHom A B)) := by
  classical
  exact Finset.univ.image (bipartiteEvalLeft A B)

/-- The right shore of the universal bipartite Freiman model. -/
def bipartiteUniversalRight (A B : Finset ℝ) :
    Finset (Module.Dual ℝ (bipartiteFreimanHom A B)) := by
  classical
  exact Finset.univ.image (bipartiteEvalRight A B)

/-- The sumset in the universal bipartite Freiman model. -/
def bipartiteUniversalSum (A B : Finset ℝ) :
    Finset (Module.Dual ℝ (bipartiteFreimanHom A B)) := by
  classical
  exact bipartiteUniversalLeft A B + bipartiteUniversalRight A B

@[simp] lemma card_bipartiteUniversalLeft (A B : Finset ℝ) :
    (bipartiteUniversalLeft A B).card = A.card := by
  classical
  rw [bipartiteUniversalLeft, Finset.card_image_of_injective _
    (bipartiteEvalLeft_injective A B), Finset.card_univ, Fintype.card_coe]

@[simp] lemma card_bipartiteUniversalRight (A B : Finset ℝ) :
    (bipartiteUniversalRight A B).card = B.card := by
  classical
  rw [bipartiteUniversalRight, Finset.card_image_of_injective _
    (bipartiteEvalRight_injective A B), Finset.card_univ, Fintype.card_coe]

/-- The universal model preserves the cross-addition table, including its cardinality. -/
theorem card_add_bipartiteUniversal (A B : Finset ℝ) :
    (bipartiteUniversalSum A B).card = (A + B).card := by
  classical
  let P : Finset (A × B) := Finset.univ
  let original : A × B → ℝ := fun p ↦ (p.1 : ℝ) + p.2
  let model : A × B → Module.Dual ℝ (bipartiteFreimanHom A B) :=
    fun p ↦ bipartiteEvalLeft A B p.1 + bipartiteEvalRight A B p.2
  have hmodel : bipartiteUniversalSum A B = P.image model := by
    ext z
    simp only [bipartiteUniversalSum, bipartiteUniversalLeft, bipartiteUniversalRight,
      Finset.mem_add, Finset.mem_image, Finset.mem_univ, true_and, P, model]
    constructor
    · rintro ⟨x, ⟨a, rfl⟩, y, ⟨b, rfl⟩, rfl⟩
      exact ⟨(a, b), rfl⟩
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
  have horiginal : A + B = P.image original := by
    ext z
    simp only [Finset.mem_add, Finset.mem_image, Finset.mem_univ, true_and, P, original]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨a, a.2, b, b.2, rfl⟩
  rw [hmodel, horiginal]
  apply card_image_eq_of_kernel_iff
  intro x _ y _
  exact bipartiteEval_add_eq_add_iff A B

/-- The space generated by differences within the two shores of the universal model. -/
def bipartiteDifferenceSpan (A B : Finset ℝ) :
    Submodule ℝ (Module.Dual ℝ (bipartiteFreimanHom A B)) :=
  Submodule.span ℝ
    ({φ | ∃ a a' : A, φ = bipartiteEvalLeft A B a - bipartiteEvalLeft A B a'} ∪
      {φ | ∃ b b' : B, φ = bipartiteEvalRight A B b - bipartiteEvalRight A B b'})

lemma mem_dualCoannihilator_bipartiteDifferenceSpan_iff
    (A B : Finset ℝ) (f : bipartiteFreimanHom A B) :
    f ∈ (bipartiteDifferenceSpan A B).dualCoannihilator ↔
      (∀ a a' : A, f.1.1 a = f.1.1 a') ∧
      (∀ b b' : B, f.1.2 b = f.1.2 b') := by
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro h
    constructor
    · intro a a'
      have hw : bipartiteEvalLeft A B a - bipartiteEvalLeft A B a' ∈
          bipartiteDifferenceSpan A B := by
        apply Submodule.subset_span
        exact Or.inl ⟨a, a', rfl⟩
      exact sub_eq_zero.mp (by simpa [bipartiteEvalLeft] using h _ hw)
    · intro b b'
      have hw : bipartiteEvalRight A B b - bipartiteEvalRight A B b' ∈
          bipartiteDifferenceSpan A B := by
        apply Submodule.subset_span
        exact Or.inr ⟨b, b', rfl⟩
      exact sub_eq_zero.mp (by simpa [bipartiteEvalRight] using h _ hw)
  · rintro ⟨hleft, hright⟩ φ hφ
    induction hφ using Submodule.span_induction with
    | mem φ hφ =>
      rcases hφ with ⟨a, a', rfl⟩ | ⟨b, b', rfl⟩
      · simp [bipartiteEvalLeft, hleft a a']
      · simp [bipartiteEvalRight, hright b b']
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]

lemma dualCoannihilator_bipartiteDifferenceSpan_eq_range_constants
    (A B : Finset ℝ) (hA : A.Nonempty) (hB : B.Nonempty) :
    (bipartiteDifferenceSpan A B).dualCoannihilator =
      LinearMap.range (bipartiteConstants A B) := by
  ext f
  rw [mem_dualCoannihilator_bipartiteDifferenceSpan_iff, LinearMap.mem_range]
  constructor
  · rintro ⟨hleft, hright⟩
    obtain ⟨a₀, ha₀⟩ := hA
    obtain ⟨b₀, hb₀⟩ := hB
    refine ⟨(f.1.1 ⟨a₀, ha₀⟩, f.1.2 ⟨b₀, hb₀⟩), ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · funext a
      exact (hleft a ⟨a₀, ha₀⟩).symm
    · funext b
      exact (hright b ⟨b₀, hb₀⟩).symm
  · rintro ⟨c, rfl⟩
    exact ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

lemma finrank_bipartiteDifferenceSpan_add_two
    (A B : Finset ℝ) (hA : A.Nonempty) (hB : B.Nonempty) :
    Module.finrank ℝ (bipartiteDifferenceSpan A B) + 2 = bipartiteFreimanHomDim A B := by
  unfold bipartiteFreimanHomDim
  rw [← Subspace.finrank_add_finrank_dualCoannihilator_eq (bipartiteDifferenceSpan A B),
    dualCoannihilator_bipartiteDifferenceSpan_eq_range_constants A B hA hB]
  congr 1
  rw [LinearMap.finrank_range_of_inj (bipartiteConstants_injective hA hB)]
  simp

lemma finrank_bipartiteDifferenceSpan
    (A B : Finset ℝ) (hA : A.Nonempty) (hB : B.Nonempty) :
    Module.finrank ℝ (bipartiteDifferenceSpan A B) = bipartiteFreimanDim A B := by
  rw [bipartiteFreimanDim]
  have h := finrank_bipartiteDifferenceSpan_add_two A B hA hB
  omega

/-- Coordinates on the finite-dimensional dual relation space. -/
def bipartiteDualCoordinates (A B : Finset ℝ) :
    Module.Dual ℝ (bipartiteFreimanHom A B) ≃ₗ[ℝ]
      (Fin (Module.finrank ℝ (Module.Dual ℝ (bipartiteFreimanHom A B))) → ℝ) :=
  (Module.finBasis ℝ (Module.Dual ℝ (bipartiteFreimanHom A B))).repr ≪≫ₗ
    Finsupp.linearEquivFunOnFinite ℝ ℝ _

/-- The coordinate realization of the left shore of the universal model. -/
def bipartiteCoordinateLeft (A B : Finset ℝ) :
    Finset (Fin (Module.finrank ℝ (Module.Dual ℝ (bipartiteFreimanHom A B))) → ℝ) := by
  classical
  exact (bipartiteUniversalLeft A B).image (bipartiteDualCoordinates A B)

/-- The coordinate realization of the right shore of the universal model. -/
def bipartiteCoordinateRight (A B : Finset ℝ) :
    Finset (Fin (Module.finrank ℝ (Module.Dual ℝ (bipartiteFreimanHom A B))) → ℝ) := by
  classical
  exact (bipartiteUniversalRight A B).image (bipartiteDualCoordinates A B)

@[simp] lemma card_bipartiteCoordinateLeft (A B : Finset ℝ) :
    (bipartiteCoordinateLeft A B).card = A.card := by
  classical
  rw [bipartiteCoordinateLeft, Finset.card_image_of_injective _
    (bipartiteDualCoordinates A B).injective, card_bipartiteUniversalLeft]

@[simp] lemma card_bipartiteCoordinateRight (A B : Finset ℝ) :
    (bipartiteCoordinateRight A B).card = B.card := by
  classical
  rw [bipartiteCoordinateRight, Finset.card_image_of_injective _
    (bipartiteDualCoordinates A B).injective, card_bipartiteUniversalRight]

lemma card_add_bipartiteCoordinates (A B : Finset ℝ) :
    (bipartiteCoordinateLeft A B + bipartiteCoordinateRight A B).card = (A + B).card := by
  classical
  rw [bipartiteCoordinateLeft, bipartiteCoordinateRight, ← Finset.image_add]
  · rw [Finset.card_image_of_injective _ (bipartiteDualCoordinates A B).injective,
      ← bipartiteUniversalSum, card_add_bipartiteUniversal]

lemma direction_bipartiteCoordinate_add
    (A B : Finset ℝ) (hA : A.Nonempty) (hB : B.Nonempty) :
    finiteDirection (bipartiteCoordinateLeft A B + bipartiteCoordinateRight A B) =
      (bipartiteDifferenceSpan A B).map (bipartiteDualCoordinates A B).toLinearMap := by
  classical
  obtain ⟨a₀, ha₀⟩ := hA
  obtain ⟨b₀, hb₀⟩ := hB
  let a0 : A := ⟨a₀, ha₀⟩
  let b0 : B := ⟨b₀, hb₀⟩
  let e := bipartiteDualCoordinates A B
  have hleft (a : A) : e (bipartiteEvalLeft A B a) ∈ bipartiteCoordinateLeft A B := by
    rw [bipartiteCoordinateLeft, Finset.mem_image]
    refine ⟨bipartiteEvalLeft A B a, ?_, rfl⟩
    rw [bipartiteUniversalLeft, Finset.mem_image]
    exact ⟨a, Finset.mem_univ _, rfl⟩
  have hright (b : B) : e (bipartiteEvalRight A B b) ∈ bipartiteCoordinateRight A B := by
    rw [bipartiteCoordinateRight, Finset.mem_image]
    refine ⟨bipartiteEvalRight A B b, ?_, rfl⟩
    rw [bipartiteUniversalRight, Finset.mem_image]
    exact ⟨b, Finset.mem_univ _, rfl⟩
  let p := e (bipartiteEvalLeft A B a0) + e (bipartiteEvalRight A B b0)
  have hp : p ∈ bipartiteCoordinateLeft A B + bipartiteCoordinateRight A B := by
    exact Finset.add_mem_add (hleft a0) (hright b0)
  apply le_antisymm
  · rw [finiteDirection, direction_affineSpan,
      vectorSpan_eq_span_vsub_set_right ℝ
        (s := ((bipartiteCoordinateLeft A B + bipartiteCoordinateRight A B :
          Finset _) : Set _)) (p := p) hp]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    rw [Finset.mem_coe, Finset.mem_add] at hx
    obtain ⟨xA, hxA, xB, hxB, rfl⟩ := hx
    rw [bipartiteCoordinateLeft, Finset.mem_image] at hxA
    rw [bipartiteCoordinateRight, Finset.mem_image] at hxB
    obtain ⟨φA, hφA, rfl⟩ := hxA
    obtain ⟨φB, hφB, rfl⟩ := hxB
    rw [bipartiteUniversalLeft, Finset.mem_image] at hφA
    rw [bipartiteUniversalRight, Finset.mem_image] at hφB
    obtain ⟨a, _, rfl⟩ := hφA
    obtain ⟨b, _, rfl⟩ := hφB
    change (e (bipartiteEvalLeft A B a) + e (bipartiteEvalRight A B b)) - p ∈
      (bipartiteDifferenceSpan A B).map e.toLinearMap
    rw [Submodule.mem_map]
    refine ⟨(bipartiteEvalLeft A B a - bipartiteEvalLeft A B a0) +
      (bipartiteEvalRight A B b - bipartiteEvalRight A B b0), ?_, ?_⟩
    · apply (bipartiteDifferenceSpan A B).add_mem
      · apply Submodule.subset_span
        exact Or.inl ⟨a, a0, rfl⟩
      · apply Submodule.subset_span
        exact Or.inr ⟨b, b0, rfl⟩
    · dsimp [p, e]
      simp only [map_add, map_sub]
      ring
  · rw [bipartiteDifferenceSpan, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro y ⟨φ, hφ, rfl⟩
    rcases hφ with ⟨a, a', rfl⟩ | ⟨b, b', rfl⟩
    · have h₁ := Finset.add_mem_add (hleft a) (hright b0)
      have h₂ := Finset.add_mem_add (hleft a') (hright b0)
      have hv := (affineSpan ℝ (_ : Set _)).vsub_mem_direction
        (subset_affineSpan ℝ _ h₁) (subset_affineSpan ℝ _ h₂)
      change e (bipartiteEvalLeft A B a - bipartiteEvalLeft A B a') ∈
        finiteDirection (bipartiteCoordinateLeft A B + bipartiteCoordinateRight A B)
      simpa [finiteDirection, map_sub] using hv
    · have h₁ := Finset.add_mem_add (hleft a0) (hright b)
      have h₂ := Finset.add_mem_add (hleft a0) (hright b')
      have hv := (affineSpan ℝ (_ : Set _)).vsub_mem_direction
        (subset_affineSpan ℝ _ h₁) (subset_affineSpan ℝ _ h₂)
      change e (bipartiteEvalRight A B b - bipartiteEvalRight A B b') ∈
        finiteDirection (bipartiteCoordinateLeft A B + bipartiteCoordinateRight A B)
      simpa [finiteDirection, map_sub] using hv

lemma affineDim_add_bipartiteCoordinates
    (A B : Finset ℝ) (hA : A.Nonempty) (hB : B.Nonempty) :
    finsetAffineDim (bipartiteCoordinateLeft A B + bipartiteCoordinateRight A B) =
      bipartiteFreimanDim A B := by
  unfold finsetAffineDim
  rw [← finiteDirection, direction_bipartiteCoordinate_add A B hA hB,
    (bipartiteDualCoordinates A B).finrank_map_eq,
    finrank_bipartiteDifferenceSpan A B hA hB]

/-- **Bipartite Freiman lemma.** In division-free form, the dimension of the cross-relation
space is at most twice the mixed-sumset cardinality divided by the common shore size. -/
theorem bipartiteFreimanHomDim_mul_card_le_two_mul_card_add
    (A B : Finset ℝ) (hA : A.Nonempty) (hB : B.Nonempty) (hcard : A.card = B.card) :
    A.card * bipartiteFreimanHomDim A B ≤ 2 * (A + B).card := by
  have hgeom := card_mul_affineDim_add_two_le_two_mul_card_add
    (bipartiteCoordinateLeft A B) (bipartiteCoordinateRight A B)
    (Finset.card_pos.mp (by simp [Finset.card_pos.mpr hA]))
    (Finset.card_pos.mp (by simp [Finset.card_pos.mpr hB])) (by simp [hcard])
  rw [card_bipartiteCoordinateLeft, affineDim_add_bipartiteCoordinates A B hA hB,
    bipartiteFreimanDim_add_two hA hB, card_add_bipartiteCoordinates] at hgeom
  exact hgeom

end

end DenseSetsWithoutLargeSumsets
