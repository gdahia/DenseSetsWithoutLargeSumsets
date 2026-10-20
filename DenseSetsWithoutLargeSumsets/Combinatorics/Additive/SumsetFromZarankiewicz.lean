/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DenseSetsWithoutLargeSumsets.Common
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Zarankiewicz
import DenseSetsWithoutLargeSumsets.Combinatorics.SimpleGraph.BipartiteRel

/-!
# Sumsets in dense sets from the Zarankiewicz function

Let `S ⊆ [n]` and `m ≤ n`. Every `s ∈ S` with `s ≥ 2` is a difference `s = (j + 1) - i` for each
`0 ≤ i < m`, with `i < j < n + m`. So the relation `i < j ∧ j + 1 - i ∈ S` between `j < n + m` and
`i < m` holds for at least `m * |{s ∈ S | 2 ≤ s}|` pairs. If it holds on `J × I`, and `M` is the
maximum of `I`, then the sets `A = {M + 1 - i | i ∈ I}` and `B = {j - M | j ∈ J}` are contained in
`[n]` and `A + B ⊆ S`.

## Main statements

* `exists_pairEvent_of_zarankiewicz_lt`: if `zarankiewicz (n + m) m k k < m * |{s ∈ S | 2 ≤ s}|`,
  then `S` contains `A + B` with `A, B ⊆ [n]` and `|A|, |B| ≥ k`.
* `exists_pairEvent_of_zarankiewicz_add_lt`: the same with the hypothesis
  `zarankiewicz (n + m) m k k + m < m * |S|`.
-/

public section

namespace DenseSetsWithoutLargeSumsets

open Finset SimpleGraph
open scoped Pointwise

private lemma pairEvent_of_forall_sub_mem {n m k : ℕ} {S I J : Finset ℕ} (hS : S ⊆ interval n)
    (hmn : m ≤ n) (hI : ∀ i ∈ I, i < m) (hIk : k ≤ #I) (hJk : k ≤ #J)
    (h : ∀ j ∈ J, ∀ i ∈ I, i < j ∧ j + 1 - i ∈ S) : pairEvent n k S := by
  rcases I.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, ∅, by simp, by simp, by simpa using hIk, by simpa using hIk, by simp⟩
  obtain ⟨M, hM, hle⟩ : ∃ M ∈ I, ∀ i ∈ I, i ≤ M := ⟨_, I.max'_mem hne, fun i hi ↦ I.le_max' i hi⟩
  have hS' : ∀ s ∈ S, 1 ≤ s ∧ s ≤ n := fun s hs ↦ mem_Icc.1 (hS hs)
  refine ⟨I.image (M + 1 - ·), J.image (· - M), ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := mem_image.1 ha
    exact mem_Icc.2 (by grind)
  · intro b hb
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hb
    exact mem_Icc.2 (by grind)
  · rw [card_image_of_injOn]
    · exact hIk
    · intro i hi i' hi' heq
      grind
  · rw [card_image_of_injOn]
    · exact hJk
    · intro j hj j' hj' heq
      grind
  · rw [add_subset_iff]
    intro a ha b hb
    obtain ⟨i, hi, rfl⟩ := mem_image.1 ha
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hb
    obtain ⟨-, hji⟩ := h j hj i hi
    convert hji using 1
    grind

private lemma mul_card_filter_le_card_filter {n m : ℕ} {S : Finset ℕ} (hS : S ⊆ interval n) :
    m * #{s ∈ S | 2 ≤ s} ≤ #{p ∈ (univ : Finset (Fin (n + m) × Fin m)) |
      (p.2 : ℕ) < p.1 ∧ (p.1 : ℕ) + 1 - p.2 ∈ S} := by
  rw [← (by simp : #((univ : Finset (Fin m)) ×ˢ {s ∈ S | 2 ≤ s}) = m * #{s ∈ S | 2 ≤ s})]
  apply card_le_card_of_surjOn fun (j, i) ↦ (i, (j : ℕ) + 1 - i)
  rintro ⟨i, s⟩ hq
  obtain ⟨hs, hs₂⟩ : s ∈ S ∧ 2 ≤ s := by simpa using hq
  have hsn := mem_Icc.1 (hS hs)
  refine ⟨(⟨i + s - 1, by grind⟩, i), ?_, ?_⟩
  · simp only [mem_coe, mem_filter, mem_univ, true_and]
    refine ⟨by grind, ?_⟩
    convert hs using 1
    grind
  · simp only [Prod.mk.injEq, true_and]
    grind

/-- If `S ⊆ [n]` and `zarankiewicz (n + m) m k k < m * |{s ∈ S | 2 ≤ s}|` for some `m ≤ n`, then
`S` contains a sumset `A + B` with `A, B ⊆ [n]` and `|A|, |B| ≥ k`. -/
lemma exists_pairEvent_of_zarankiewicz_lt {n m k : ℕ} (hmn : m ≤ n) {S : Finset ℕ}
    (hS : S ⊆ interval n) (hz : zarankiewicz (n + m) m k k < m * #{s ∈ S | 2 ≤ s}) :
    pairEvent n k S := by
  obtain ⟨J, I, hJ, hI, hrel⟩ := exists_forall_rel_of_zarankiewicz_lt
    (fun (j : Fin (n + m)) (i : Fin m) ↦ (i : ℕ) < j ∧ (j : ℕ) + 1 - i ∈ S)
    (by simpa using hz.trans_le (mul_card_filter_le_card_filter hS))
  apply pairEvent_of_forall_sub_mem (I := I.image Fin.val) (J := J.image Fin.val) hS hmn
  · simp
  · rw [card_image_of_injective _ Fin.val_injective, hI]
  · rw [card_image_of_injective _ Fin.val_injective, hJ]
  · simpa using hrel

private lemma card_le_card_filter_add_one {n : ℕ} {S : Finset ℕ} (hS : S ⊆ interval n) :
    #S ≤ #{s ∈ S | 2 ≤ s} + 1 := by
  have hS' : ∀ s ∈ S, 1 ≤ s ∧ s ≤ n := fun s hs ↦ mem_Icc.1 (hS hs)
  rw [← card_filter_add_card_filter_not (s := S) (2 ≤ ·)]
  apply Nat.add_le_add_left
  rw [card_le_one]
  grind

/-- If `S ⊆ [n]` and `zarankiewicz (n + m) m k k + m < m * |S|` for some `m ≤ n`, then `S` contains
a sumset `A + B` with `A, B ⊆ [n]` and `|A|, |B| ≥ k`. The term `m` accounts for the element `1`,
which is not a sum of two positive integers. -/
lemma exists_pairEvent_of_zarankiewicz_add_lt {n m k : ℕ} (hmn : m ≤ n) {S : Finset ℕ}
    (hS : S ⊆ interval n) (hz : zarankiewicz (n + m) m k k + m < m * #S) :
    pairEvent n k S := by
  apply exists_pairEvent_of_zarankiewicz_lt hmn hS
  linarith [Nat.mul_le_mul_left m (card_le_card_filter_add_one hS)]

end DenseSetsWithoutLargeSumsets
