/-
Copyright (c) 2026 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Bipartite graphs: additions from Mathlib pull request #25841

The lemmas that the pull request
[#25841](https://github.com/leanprover-community/mathlib4/pull/25841) of Mitchell Horner adds to
`Mathlib/Combinatorics/SimpleGraph/Bipartite.lean` and that its proof of the Kővári–Sós–Turán
theorem uses, copied at commit `1ed83fcfe430778431dfa20c92663db040a98772`. Delete this file when
Mathlib has them.
-/

public section

namespace SimpleGraph

section IsBipartiteWith

variable {V : Type*} {G : SimpleGraph V} {s t : Set V}

/-- A subgraph of a graph that is bipartite with parts `s` and `t` is bipartite with the same
parts. -/
theorem IsBipartiteWith.anti {G' : SimpleGraph V} (h : G.IsBipartiteWith s t) (hle : G' ≤ G) :
    G'.IsBipartiteWith s t := ⟨h.disjoint, fun _ _ hadj ↦ h.mem_of_adj (hle hadj)⟩

end IsBipartiteWith

section completeBipartiteGraph

variable {V W : Type*}

/-- A complete bipartite graph is empty iff one of its parts is empty. -/
theorem completeBipartiteGraph_eq_bot_iff :
    completeBipartiteGraph V W = ⊥ ↔ IsEmpty V ∨ IsEmpty W := by
  simp [SimpleGraph.ext_iff, funext_iff, Sum.forall, isEmpty_iff,
    (by tauto : ((V → W → False) ∧ (W → V → False)) ↔ ((V → False) ∨ (W → False)))]

/-- A complete bipartite graph whose left part is empty is empty. -/
theorem completeBipartiteGraph_eq_bot_of_isEmpty_left [IsEmpty V] :
    completeBipartiteGraph V W = ⊥ := completeBipartiteGraph_eq_bot_iff.mpr (.inl ‹_›)

/-- A complete bipartite graph whose right part is empty is empty. -/
theorem completeBipartiteGraph_eq_bot_of_isEmpty_right [IsEmpty W] :
    completeBipartiteGraph V W = ⊥ := completeBipartiteGraph_eq_bot_iff.mpr (.inr ‹_›)

end completeBipartiteGraph

end SimpleGraph
