/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Extremal.Zarankiewicz

/-!
# The bipartite graph of a relation

For `r : V → W → Prop`, the graph `bipartiteGraphOfRel r` on `V ⊕ W` joins `a : V` to `b : W` when
`r a b` holds. Its edges correspond to the pairs satisfying `r`, so the Zarankiewicz function
bounds the number of such pairs when `r` has no large rectangle.

## Main definitions

* `bipartiteGraphOfRel r`: the bipartite graph of the relation `r`.

## Main statements

* `card_edgeFinset_bipartiteGraphOfRel`: the number of edges is the number of pairs satisfying `r`.
* `exists_forall_rel_of_zarankiewicz_lt`: if more than `zarankiewicz |V| |W| k k` pairs satisfy
  `r`, then there are `A ⊆ V` and `B ⊆ W` of size `k` with `r a b` for all `a ∈ A` and `b ∈ B`.
-/

@[expose] public section

namespace DenseSetsWithoutLargeSumsets

open Finset Fintype SimpleGraph

variable {V W : Type*}

/-- The bipartite graph on `V ⊕ W` in which `a : V` is adjacent to `b : W` when `r a b` holds. -/
def bipartiteGraphOfRel (r : V → W → Prop) : SimpleGraph (V ⊕ W) where
  Adj
  | .inl a, .inr b | .inr b, .inl a => r a b
  | _, _ => False
  symm.symm := by rintro (a | a) (b | b) h <;> exact h

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

instance (r : V → W → Prop) [h : DecidableRel r] : DecidableRel (bipartiteGraphOfRel r).Adj
  | .inl _, .inr _ | .inr _, .inl _ => h _ _
  | .inl _, .inl _ | .inr _, .inr _ => inferInstanceAs (Decidable False)

lemma bipartiteGraphOfRel_le (r : V → W → Prop) :
    bipartiteGraphOfRel r ≤ completeBipartiteGraph V W := by
  rintro (a | a) (b | b) h <;> simp_all

/-- The number of edges of `bipartiteGraphOfRel r` is the number of pairs satisfying `r`. -/
lemma card_edgeFinset_bipartiteGraphOfRel [Fintype V] [Fintype W]
    (r : V → W → Prop) [DecidableRel r] :
    #(bipartiteGraphOfRel r).edgeFinset = #{p ∈ (univ : Finset (V × W)) | r p.1 p.2} := by
  symm
  apply card_bij (fun (a, b) _ ↦ s(.inl a, .inr b)) (fun _ h ↦ by simpa using h) (by grind)
  intro e he
  induction e with | _ v w
  rw [mem_edgeFinset, mem_edgeSet] at he
  match v, w with
  | .inl a, .inr b => exact ⟨(a, b), by simpa using he, rfl⟩
  | .inr b, .inl a => exact ⟨(a, b), by simpa using he, Sym2.eq_swap⟩
  | .inl _, .inl _ | .inr _, .inr _ => simp at he

private lemma exists_forall_rel_of_isCompleteBetween_aux {r : V → W → Prop}
    {left right : Finset (V ⊕ W)}
    (hcomp : (bipartiteGraphOfRel r).IsCompleteBetween ↑left ↑right) {a₀ : V} {b₀ : W}
    (ha : .inl a₀ ∈ left) (hb : .inr b₀ ∈ right) :
    ∃ (A : Finset V) (B : Finset W), #A = #left ∧ #B = #right ∧ ∀ a ∈ A, ∀ b ∈ B, r a b := by
  have hl : left.toRight = ∅ := eq_empty_of_forall_notMem fun b hb' ↦
    bipartiteGraphOfRel_adj_inr_inr r b b₀ (hcomp (mem_toRight.1 hb') hb)
  have hr : right.toLeft = ∅ := eq_empty_of_forall_notMem fun a ha' ↦
    bipartiteGraphOfRel_adj_inl_inl r a₀ a (hcomp ha (mem_toLeft.1 ha'))
  refine ⟨left.toLeft, right.toRight, ?_, ?_, ?_⟩
  · simpa [hl] using card_toLeft_add_card_toRight (u := left)
  · simpa [hr] using card_toLeft_add_card_toRight (u := right)
  · intro a ha b hb
    exact hcomp (mem_toLeft.1 ha) (mem_toRight.1 hb)

/-- Two sets of `k` vertices that are completely joined in `bipartiteGraphOfRel r` give sets
`A ⊆ V` and `B ⊆ W` of size `k` with `r a b` for all `a ∈ A` and `b ∈ B`. -/
lemma exists_forall_rel_of_isCompleteBetween {r : V → W → Prop} {left right : Finset (V ⊕ W)}
    {k : ℕ} (hl : #left = k) (hr : #right = k)
    (hcomp : (bipartiteGraphOfRel r).IsCompleteBetween ↑left ↑right) :
    ∃ (A : Finset V) (B : Finset W), #A = k ∧ #B = k ∧ ∀ a ∈ A, ∀ b ∈ B, r a b := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨∅, ∅, rfl, rfl, by simp⟩
  obtain ⟨u, hu⟩ := card_pos.mp (hl ▸ hk)
  obtain ⟨v, hv⟩ := card_pos.mp (hr ▸ hk)
  have hadj := hcomp hu hv
  match u, v with
  | .inl _, .inl _ | .inr _, .inr _ => simp at hadj
  | .inl _, .inr _ =>
    obtain ⟨A, B, hA, hB, hAB⟩ := exists_forall_rel_of_isCompleteBetween_aux hcomp hu hv
    exact ⟨A, B, hA.trans hl, hB.trans hr, hAB⟩
  | .inr _, .inl _ =>
    obtain ⟨A, B, hA, hB, hAB⟩ := exists_forall_rel_of_isCompleteBetween_aux hcomp.symm hv hu
    exact ⟨A, B, hA.trans hr, hB.trans hl, hAB⟩

/-- A relation `r : V → W → Prop` that holds for more than `zarankiewicz |V| |W| k k` pairs holds
on all of `A × B` for some `A ⊆ V` and `B ⊆ W` of size `k`. -/
lemma exists_forall_rel_of_zarankiewicz_lt [Fintype V] [Fintype W]
    (r : V → W → Prop) [DecidableRel r] {k : ℕ}
    (hz : zarankiewicz (card V) (card W) k k < #{p ∈ (univ : Finset (V × W)) | r p.1 p.2}) :
    ∃ (A : Finset V) (B : Finset W), #A = k ∧ #B = k ∧ ∀ a ∈ A, ∀ b ∈ B, r a b := by
  have hfree : ¬ (completeBipartiteGraph (Fin k) (Fin k)).Free (bipartiteGraphOfRel r) := by
    intro hfree
    rw [← card_edgeFinset_bipartiteGraphOfRel] at hz
    exact hz.not_ge ((zarankiewicz_le_iff rfl rfl (Fintype.card_fin k) (Fintype.card_fin k) _).mp
      le_rfl (bipartiteGraphOfRel_le r) hfree)
  rw [not_free, completeBipartiteGraph_isContained_iff] at hfree
  obtain ⟨left, right, hl, hr, hcomp⟩ := hfree
  exact exists_forall_rel_of_isCompleteBetween (by simpa using hl) (by simpa using hr) hcomp

end DenseSetsWithoutLargeSumsets
