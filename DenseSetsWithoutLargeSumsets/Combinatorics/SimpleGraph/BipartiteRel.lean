/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import Mathlib.Combinatorics.SimpleGraph.Extremal.Zarankiewicz

/-!
# Bipartite graphs attached to a relation

Given `r : V → W → Prop`, `bipartiteGraphOfRel r` is the bipartite graph on `V ⊕ W` joining
`v : V` to `w : W` exactly when `r v w` holds.  Its edges are in bijection with the pairs
satisfying `r`, so the Zarankiewicz function controls how many pairs a relation without a large
"combinatorial rectangle" can have.

The main result is `exists_forall_rel_of_zarankiewicz_lt`: a relation holding for more than
`zarankiewicz #V #W k k` pairs admits `A : Finset V` and `B : Finset W` of size `k` with `r a b`
for every `a ∈ A` and `b ∈ B`.
-/

namespace DenseSetsWithoutLargeSumsets

open Finset Fintype SimpleGraph

variable {V W : Type*}

/-- The bipartite graph on `V ⊕ W` joining `a : V` to `b : W` exactly when `r a b` holds. -/
def bipartiteGraphOfRel (r : V → W → Prop) : SimpleGraph (V ⊕ W) where
  Adj u v :=
    match u, v with
    | .inl a, .inr b => r a b
    | .inr b, .inl a => r a b
    | _, _ => False
  symm.symm := by rintro (a | a) (b | b) h <;> exact h
  loopless.irrefl := by rintro (a | a) h <;> exact h

@[simp]
lemma bipartiteGraphOfRel_adj_inl_inr (r : V → W → Prop) (a : V) (b : W) :
    (bipartiteGraphOfRel r).Adj (.inl a) (.inr b) ↔ r a b := Iff.rfl

@[simp]
lemma bipartiteGraphOfRel_adj_inr_inl (r : V → W → Prop) (a : V) (b : W) :
    (bipartiteGraphOfRel r).Adj (.inr b) (.inl a) ↔ r a b := Iff.rfl

@[simp]
lemma bipartiteGraphOfRel_adj_inl_inl (r : V → W → Prop) (a a' : V) :
    ¬ (bipartiteGraphOfRel r).Adj (.inl a) (.inl a') := id

@[simp]
lemma bipartiteGraphOfRel_adj_inr_inr (r : V → W → Prop) (b b' : W) :
    ¬ (bipartiteGraphOfRel r).Adj (.inr b) (.inr b') := id

instance (r : V → W → Prop) [DecidableRel r] : DecidableRel (bipartiteGraphOfRel r).Adj
  | .inl _, .inl _ => inferInstanceAs (Decidable False)
  | .inl a, .inr b => inferInstanceAs (Decidable (r a b))
  | .inr b, .inl a => inferInstanceAs (Decidable (r a b))
  | .inr _, .inr _ => inferInstanceAs (Decidable False)

lemma bipartiteGraphOfRel_le (r : V → W → Prop) :
    bipartiteGraphOfRel r ≤ completeBipartiteGraph V W := by
  rintro (a | a) (b | b) h <;> simp_all

/-- The edges of `bipartiteGraphOfRel r` are in bijection with the pairs satisfying `r`. -/
lemma card_edgeFinset_bipartiteGraphOfRel [Fintype V] [Fintype W]
    (r : V → W → Prop) [DecidableRel r] :
    #(bipartiteGraphOfRel r).edgeFinset = #{p ∈ (univ : Finset (V × W)) | r p.1 p.2} := by
  classical
  set P : Finset (V × W) := {p ∈ (univ : Finset (V × W)) | r p.1 p.2} with hP
  set f : V × W → Sym2 (V ⊕ W) := fun p => s(.inl p.1, .inr p.2) with hf
  have hinj : Set.InjOn f ↑P := by
    intro p _ q _ hpq
    simp only [hf, Sym2.eq_iff] at hpq
    simpa [Prod.ext_iff] using hpq
  have himage : P.image f = (bipartiteGraphOfRel r).edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [mem_image, mem_edgeFinset, mem_edgeSet, hP, mem_filter, mem_univ, true_and, hf]
      constructor
      · rintro ⟨p, hp, hpe⟩
        rw [Sym2.eq_iff] at hpe
        rcases hpe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hp
        · exact hp
      · intro hadj
        match u, v with
        | .inl a, .inr b => exact ⟨(a, b), hadj, rfl⟩
        | .inr b, .inl a => exact ⟨(a, b), hadj, Sym2.eq_swap⟩
        | .inl _, .inl _ => exact absurd hadj (by simp)
        | .inr _, .inr _ => exact absurd hadj (by simp)
  rw [← himage, card_image_of_injOn hinj]

/-- Auxiliary step of `exists_forall_rel_of_isCompleteBetween`: a complete bipartite pair of parts
whose left part lies in `V` and whose right part lies in `W` yields sets on the two sides all of
whose pairs satisfy `r`. -/
private lemma exists_forall_rel_of_isCompleteBetween_aux {r : V → W → Prop}
    {left right : Finset (V ⊕ W)}
    (hcomp : (bipartiteGraphOfRel r).IsCompleteBetween ↑left ↑right)
    (hleft : ∀ u ∈ left, ∃ a, u = Sum.inl a) (hright : ∀ v ∈ right, ∃ b, v = Sum.inr b) :
    ∃ (A : Finset V) (B : Finset W), #A = #left ∧ #B = #right ∧ ∀ a ∈ A, ∀ b ∈ B, r a b := by
  classical
  refine ⟨left.preimage Sum.inl Sum.inl_injective.injOn,
    right.preimage Sum.inr Sum.inr_injective.injOn, ?_, ?_, ?_⟩
  · rw [← card_image_of_injective _ (Sum.inl_injective (β := W)), image_preimage,
      filter_true_of_mem fun u hu => by obtain ⟨a, rfl⟩ := hleft u hu; exact ⟨a, rfl⟩]
  · rw [← card_image_of_injective _ (Sum.inr_injective (α := V)), image_preimage,
      filter_true_of_mem fun v hv => by obtain ⟨b, rfl⟩ := hright v hv; exact ⟨b, rfl⟩]
  · intro a ha b hb
    rw [mem_preimage] at ha hb
    exact hcomp ha hb

/-- A pair of parts that is complete in `bipartiteGraphOfRel r` gives sets `A` and `B` on the two
sides, of the same sizes, all of whose pairs satisfy `r`. -/
lemma exists_forall_rel_of_isCompleteBetween {r : V → W → Prop} {left right : Finset (V ⊕ W)}
    {k : ℕ} (hl : #left = k) (hr : #right = k)
    (hcomp : (bipartiteGraphOfRel r).IsCompleteBetween ↑left ↑right) :
    ∃ (A : Finset V) (B : Finset W), #A = k ∧ #B = k ∧ ∀ a ∈ A, ∀ b ∈ B, r a b := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨∅, ∅, rfl, rfl, by simp⟩
  obtain ⟨u₀, hu₀⟩ := card_pos.mp (hl ▸ hk)
  obtain ⟨v₀, hv₀⟩ := card_pos.mp (hr ▸ hk)
  have hadj := hcomp hu₀ hv₀
  match u₀, v₀ with
  | .inl _, .inl _ => exact absurd hadj (by simp)
  | .inr _, .inr _ => exact absurd hadj (by simp)
  | .inl a₀, .inr b₀ =>
    have hsideₗ : ∀ u ∈ left, ∃ a, u = Sum.inl a := by
      rintro (a | b) hu
      · exact ⟨a, rfl⟩
      · exact absurd (hcomp hu hv₀) (by simp)
    have hsideᵣ : ∀ v ∈ right, ∃ b, v = Sum.inr b := by
      rintro (a | b) hv
      · exact absurd (hcomp hu₀ hv) (by simp)
      · exact ⟨b, rfl⟩
    obtain ⟨A, B, hA, hB, hAB⟩ := exists_forall_rel_of_isCompleteBetween_aux hcomp hsideₗ hsideᵣ
    exact ⟨A, B, hA.trans hl, hB.trans hr, hAB⟩
  | .inr b₀, .inl a₀ =>
    have hsideₗ : ∀ u ∈ right, ∃ a, u = Sum.inl a := by
      rintro (a | b) hv
      · exact ⟨a, rfl⟩
      · exact absurd (hcomp hu₀ hv) (by simp)
    have hsideᵣ : ∀ v ∈ left, ∃ b, v = Sum.inr b := by
      rintro (a | b) hu
      · exact absurd (hcomp hu hv₀) (by simp)
      · exact ⟨b, rfl⟩
    obtain ⟨A, B, hA, hB, hAB⟩ :=
      exists_forall_rel_of_isCompleteBetween_aux hcomp.symm hsideₗ hsideᵣ
    exact ⟨A, B, hA.trans hr, hB.trans hl, hAB⟩

/-- **Reduction to the Zarankiewicz function.**  A relation `r : V → W → Prop` holding for more
than `zarankiewicz #V #W k k` pairs contains a `k × k` combinatorial rectangle. -/
theorem exists_forall_rel_of_zarankiewicz_lt [Fintype V] [Fintype W]
    (r : V → W → Prop) [DecidableRel r] {k : ℕ}
    (hz : zarankiewicz (card V) (card W) k k < #{p ∈ (univ : Finset (V × W)) | r p.1 p.2}) :
    ∃ (A : Finset V) (B : Finset W), #A = k ∧ #B = k ∧ ∀ a ∈ A, ∀ b ∈ B, r a b := by
  classical
  have hfree : ¬ (completeBipartiteGraph (Fin k) (Fin k)).Free (bipartiteGraphOfRel r) := by
    intro hfree
    have hle := (zarankiewicz_le_iff (V := V) (W := W) (α := Fin k) (β := Fin k) rfl rfl
      (Fintype.card_fin k) (Fintype.card_fin k) _).mp le_rfl (bipartiteGraphOfRel_le r) hfree
    rw [card_edgeFinset_bipartiteGraphOfRel] at hle
    omega
  rw [not_free, completeBipartiteGraph_isContained_iff] at hfree
  obtain ⟨left, right, hl, hr, hcomp⟩ := hfree
  exact exists_forall_rel_of_isCompleteBetween (by simpa using hl) (by simpa using hr) hcomp

end DenseSetsWithoutLargeSumsets
