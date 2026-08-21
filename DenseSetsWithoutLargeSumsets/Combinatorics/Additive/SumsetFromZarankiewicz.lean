/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.Combinatorics.SimpleGraph.BipartiteRel
import DenseSetsWithoutLargeSumsets.Common

/-!
# The lower bound for the main question, via the Zarankiewicz function

`dense_subset_without_large_sumsets` constructs, for a suitable range of densities `δ`, a subset
`S ⊆ [n]` with `#S ≥ δ n` containing no sumset `A + B` with `min #A #B ≥ k` for
`k ≈ (3 + γ) log n / log (1 / δ)`.  This file proves the complementary direction: *every*
sufficiently large `S ⊆ [n]` does contain such a sumset, reducing the question to the
Zarankiewicz function `SimpleGraph.zarankiewicz`.

The reduction writes every integer of `[2, m² + 1]` uniquely as `(i + 1) + (j * m + 1)` with
`i, j < m`, that is, in base `m`.  This turns `S` into a bipartite relation on `Fin m × Fin m`
with `#S - 1` pairs, and a `k × k` combinatorial rectangle in that relation is exactly a pair of
`k`-element sets `A`, `B` with `A + B ⊆ S`.  Taking `m = ⌊√n⌋ + 1` covers all of `[n]`, so
`exists_pairEvent_of_zarankiewicz_lt` reads: if
`zarankiewicz (⌊√n⌋ + 1) (⌊√n⌋ + 1) k k + 1 < #S` then `pairEvent n k S`.

Since `zarankiewicz N N k k` is `O(N^(2 - 1/k))` by Kővári–Sós–Turán, this gives sumsets of size
`k` as soon as `δ` exceeds roughly `n^(-1/(2k))`, matching the order `log n / log (1 / δ)` of the
construction up to the constant.
-/

namespace DenseSetsWithoutLargeSumsets

open Finset SimpleGraph

open scoped Pointwise

/-- Base-`m` digits: the pairs `(i, j) ∈ Fin m × Fin m` with `(i + 1) + (j * m + 1) ∈ S` are in
bijection with the elements of `S` that are at least `2`. -/
lemma card_filter_univ_baseRepr_mem {m : ℕ} (hm : 0 < m) {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 (m * m + 1)) :
    #{p ∈ (univ : Finset (Fin m × Fin m)) | (p.1 : ℕ) + (p.2 : ℕ) * m + 2 ∈ S}
      = #{s ∈ S | 2 ≤ s} := by
  refine Finset.card_bij (fun p _ => (p.1 : ℕ) + (p.2 : ℕ) * m + 2) (fun p hp => ?_)
    (fun p _ q _ hpq => ?_) (fun s hs => ?_)
  · simp only [mem_filter, mem_univ, true_and] at hp ⊢
    exact ⟨hp, by omega⟩
  · have hval : (p.1 : ℕ) + (p.2 : ℕ) * m = (q.1 : ℕ) + (q.2 : ℕ) * m := by omega
    have hfst : (p.1 : ℕ) = (q.1 : ℕ) := by
      have := congrArg (· % m) hval
      simpa [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt p.1.isLt,
        Nat.mod_eq_of_lt q.1.isLt] using this
    have hsnd : (p.2 : ℕ) = (q.2 : ℕ) := by
      have : (p.2 : ℕ) * m = (q.2 : ℕ) * m := by omega
      exact Nat.eq_of_mul_eq_mul_right hm this
    exact Prod.ext (Fin.val_injective hfst) (Fin.val_injective hsnd)
  · simp only [mem_filter] at hs
    obtain ⟨hsS, hs2⟩ := hs
    have hsub : s - 2 < m * m := by
      have := hS hsS
      simp only [mem_Icc] at this
      omega
    have hdiv : (s - 2) / m < m := Nat.div_lt_of_lt_mul (by omega)
    have hmod : (s - 2) % m < m := Nat.mod_lt _ hm
    have hdm : (s - 2) / m * m + (s - 2) % m = s - 2 := Nat.div_add_mod' _ _
    have hrepr : (s - 2) % m + (s - 2) / m * m + 2 = s := by omega
    refine ⟨(⟨(s - 2) % m, hmod⟩, ⟨(s - 2) / m, hdiv⟩), ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      rwa [hrepr]
    · simpa only using hrepr

/-- **Reduction of the sumset problem to the Zarankiewicz function.**  If `S` is a set of integers
in `[1, m² + 1]` with more than `zarankiewicz m m k k + 1` elements, then `S` contains a sumset
`A + B` with `#A = #B = k`. -/
theorem exists_add_subset_of_zarankiewicz_lt {m k : ℕ} (hm : 0 < m) {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 (m * m + 1)) (hz : zarankiewicz m m k k + 1 < #S) :
    ∃ A ⊆ Finset.Icc 1 m, ∃ B ⊆ Finset.Icc 1 (m * m), #A = k ∧ #B = k ∧ A + B ⊆ S := by
  classical
  have hone : #{s ∈ S | ¬ 2 ≤ s} ≤ 1 := by
    refine le_trans (Finset.card_le_card (fun s hs => ?_)) (Finset.card_singleton 1).le
    simp only [mem_filter, not_le, mem_singleton] at hs ⊢
    have := hS hs.1
    simp only [mem_Icc] at this
    omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (p := fun s => 2 ≤ s)
  have hcount : zarankiewicz m m k k < #{s ∈ S | 2 ≤ s} := by omega
  rw [← card_filter_univ_baseRepr_mem hm hS] at hcount
  obtain ⟨A₀, B₀, hA₀, hB₀, hrel⟩ :=
    exists_forall_rel_of_zarankiewicz_lt (fun i j : Fin m => (i : ℕ) + (j : ℕ) * m + 2 ∈ S)
      (by simpa using hcount)
  refine ⟨A₀.image (fun i : Fin m => (i : ℕ) + 1), fun a ha => ?_,
    B₀.image (fun j : Fin m => (j : ℕ) * m + 1), fun b hb => ?_, ?_, ?_, ?_⟩
  · simp only [mem_image] at ha
    obtain ⟨i, _, rfl⟩ := ha
    simp only [mem_Icc]
    have := i.isLt
    omega
  · simp only [mem_image] at hb
    obtain ⟨j, _, rfl⟩ := hb
    have hj : (j : ℕ) + 1 ≤ m := j.isLt
    have hjm : ((j : ℕ) + 1) * m ≤ m * m := Nat.mul_le_mul hj (le_refl m)
    have hexp : ((j : ℕ) + 1) * m = (j : ℕ) * m + m := by ring
    simp only [mem_Icc]
    omega
  · rw [Finset.card_image_of_injective _ (fun i j hij => Fin.val_injective (by omega)), hA₀]
  · rw [Finset.card_image_of_injective _ (fun i j hij => Fin.val_injective
      (Nat.eq_of_mul_eq_mul_right hm (by omega : (i : ℕ) * m = (j : ℕ) * m))), hB₀]
  · rw [Finset.add_subset_iff]
    rintro a ha b hb
    simp only [mem_image] at ha hb
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨j, hj, rfl⟩ := hb
    have := hrel i hi j hj
    convert this using 1
    omega

/-- **The lower bound for the main question.**  Every `S ⊆ [n]` with more than
`zarankiewicz (⌊√n⌋ + 1) (⌊√n⌋ + 1) k k + 1` elements contains a sumset `A + B` with
`A, B ⊆ [n]` and `min #A #B ≥ k`.

This is the converse direction to `dense_subset_without_large_sumsets`, whose conclusion is
exactly `¬ pairEvent n k S` for the set it constructs. -/
theorem exists_pairEvent_of_zarankiewicz_lt {n k : ℕ} {S : Finset ℕ} (hS : S ⊆ interval n)
    (hz : zarankiewicz (n.sqrt + 1) (n.sqrt + 1) k k + 1 < #S) :
    pairEvent n k S := by
  have hn : n < (n.sqrt + 1) * (n.sqrt + 1) := Nat.lt_succ_sqrt n
  have hS' : S ⊆ Finset.Icc 1 ((n.sqrt + 1) * (n.sqrt + 1) + 1) := by
    refine hS.trans (Finset.Icc_subset_Icc_right (by omega))
  obtain ⟨A, hA, B, hB, hAcard, hBcard, hAB⟩ :=
    exists_add_subset_of_zarankiewicz_lt (m := n.sqrt + 1) (Nat.succ_pos _) hS' hz
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Finset.card_eq_zero] at hAcard hBcard
    exact ⟨∅, ∅, by simp [interval], by simp [interval], by simp, by simp, by simp⟩
  obtain ⟨a₀, ha₀⟩ := Finset.card_pos.mp (hAcard ▸ hk)
  obtain ⟨b₀, hb₀⟩ := Finset.card_pos.mp (hBcard ▸ hk)
  have hmem : ∀ a ∈ A, ∀ b ∈ B, a + b ∈ Finset.Icc 1 n :=
    fun a ha b hb => hS (hAB (Finset.add_mem_add ha hb))
  refine ⟨A, B, fun a ha => ?_, fun b hb => ?_, hAcard.ge, hBcard.ge, hAB⟩
  · have h1 := (Finset.mem_Icc.mp (hA ha)).1
    have h2 := Finset.mem_Icc.mp (hmem a ha b₀ hb₀)
    exact Finset.mem_Icc.mpr ⟨h1, by omega⟩
  · have h1 := (Finset.mem_Icc.mp (hB hb)).1
    have h2 := Finset.mem_Icc.mp (hmem a₀ ha₀ b hb)
    exact Finset.mem_Icc.mpr ⟨h1, by omega⟩

/-- The density form of the lower bound: any subset of `[n]` of density `δ` contains a sumset
`A + B` with `min #A #B ≥ k`, as soon as `δ n` exceeds `zarankiewicz (⌊√n⌋ + 1) (⌊√n⌋ + 1) k k`
by more than one. -/
theorem pairEvent_of_zarankiewicz_lt_density {n k : ℕ} {δ : ℝ} {S : Finset ℕ}
    (hS : S ⊆ interval n) (hcard : δ * n ≤ #S)
    (hz : (zarankiewicz (n.sqrt + 1) (n.sqrt + 1) k k : ℝ) + 1 < δ * n) :
    pairEvent n k S := by
  refine exists_pairEvent_of_zarankiewicz_lt hS ?_
  have hlt : ((zarankiewicz (n.sqrt + 1) (n.sqrt + 1) k k : ℝ) + 1) < (#S : ℝ) :=
    lt_of_lt_of_le hz hcard
  exact_mod_cast hlt

end DenseSetsWithoutLargeSumsets
