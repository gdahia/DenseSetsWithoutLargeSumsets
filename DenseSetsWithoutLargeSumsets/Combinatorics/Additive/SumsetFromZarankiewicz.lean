/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.Combinatorics.SimpleGraph.BipartiteRel
import DenseSetsWithoutLargeSumsets.Common

/-!
# The lower bound for the main question, via the Zarankiewicz function

For any `m ≤ n`, the constant-preserving reduction represents every `s ∈ S \ {1}` in each
of the `m` ways `s = (i + s) - i`, for `0 ≤ i < m`.  It gives a relation on
`Fin (n + m) × Fin m` with exactly `m * #{s ∈ S | 2 ≤ s}` pairs.  A combinatorial
rectangle gives finite integer sets
whose difference set is contained in `S`; translating the sets in opposite directions preserves
their sumset and puts both inside `[n]`.

Consequently the Kővári–Sós–Turán exponent is `1 / k`, with no factor `1 / 2` lost to a
square-root/base representation.
-/

namespace DenseSetsWithoutLargeSumsets

open Finset SimpleGraph

open scoped Pointwise

/-- The difference relation has exactly `n` representatives for every member of `S` other than
`1`. -/
lemma card_filter_univ_sub_mem {n m : ℕ} {S : Finset ℕ}
    (hS : S ⊆ interval n) :
    #{p ∈ (univ : Finset (Fin (n + m) × Fin m)) |
        (p.2 : ℕ) + 2 ≤ (p.1 : ℕ) + 1 ∧ (p.1 : ℕ) + 1 - (p.2 : ℕ) ∈ S}
      = m * #{s ∈ S | 2 ≤ s} := by
  classical
  calc
    _ = #((univ : Finset (Fin m)) ×ˢ {s ∈ S | 2 ≤ s}) := by
      refine Finset.card_bij
        (fun p : Fin (n + m) × Fin m => fun _ =>
          (p.2, (p.1 : ℕ) + 1 - (p.2 : ℕ))) (fun p hp => ?_)
        (fun p hp q hq hpq => ?_) (fun q hq => ?_)
      · simp only [mem_filter, mem_univ, true_and] at hp
        simpa only [Finset.mem_product, Finset.mem_univ, Finset.mem_filter, true_and] using
          (⟨hp.2, by omega⟩ :
            (p.1 : ℕ) + 1 - (p.2 : ℕ) ∈ S ∧ 2 ≤ (p.1 : ℕ) + 1 - (p.2 : ℕ))
      · simp only [Prod.ext_iff] at hpq
        apply Prod.ext
        · apply Fin.val_injective
          simp only [mem_filter, mem_univ, true_and] at hp hq
          omega
        · exact hpq.1
      · have hq' : q.2 ∈ S ∧ 2 ≤ q.2 := by
          simpa only [Finset.mem_product, Finset.mem_univ, Finset.mem_filter, true_and] using hq
        obtain ⟨hsS, hs2⟩ := hq'
        have hsn := hS hsS
        simp only [interval, mem_Icc] at hsn
        have hj : (q.1 : ℕ) + q.2 - 1 < n + m := by omega
        let j : Fin (n + m) := ⟨(q.1 : ℕ) + q.2 - 1, hj⟩
        refine ⟨(j, q.1), ?_, ?_⟩
        · simp only [mem_filter, mem_univ, true_and, j]
          constructor
          · omega
          · have heq : (q.1 : ℕ) + q.2 - 1 + 1 - (q.1 : ℕ) = q.2 := by omega
            rwa [heq]
        · apply Prod.ext
          · rfl
          · change (q.1 : ℕ) + q.2 - 1 + 1 - (q.1 : ℕ) = q.2
            omega
    _ = _ := by simp

/-- **Constant-preserving reduction to the Zarankiewicz function.** If the difference relation
associated to `S ⊆ [n]` has more than `zarankiewicz (n + m) m k k` pairs, then `S` contains a
sumset `A + B` with `#A = #B = k` and `A, B ⊆ [n]`.

The hypothesis is written using `#{s ∈ S | 2 ≤ s}` because `1` cannot be a sum of two
positive integers. -/
theorem exists_pairEvent_of_zarankiewicz_lt {n m k : ℕ} (_hm : 0 < m) (hmn : m ≤ n)
    {S : Finset ℕ} (hS : S ⊆ interval n)
    (hz : zarankiewicz (n + m) m k k < m * #{s ∈ S | 2 ≤ s}) :
    pairEvent n k S := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨∅, ∅, by simp [interval], by simp [interval], by simp, by simp, by simp⟩
  rw [← card_filter_univ_sub_mem hS] at hz
  obtain ⟨J, I, hJ, hI, hrel⟩ :=
    exists_forall_rel_of_zarankiewicz_lt
      (fun j : Fin (n + m) => fun i : Fin m =>
        (i : ℕ) + 2 ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 - (i : ℕ) ∈ S)
      (by simpa using hz)
  obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (hI ▸ hk)
  let M : ℕ := ↑(I.max' ⟨i₀, hi₀⟩)
  have hleM : ∀ i ∈ I, (i : ℕ) ≤ M := by
    intro i hi
    exact_mod_cast Finset.le_max' I i hi
  let A := I.image (fun i : Fin m => M + 1 - (i : ℕ))
  let B := J.image (fun j : Fin (n + m) => (j : ℕ) - M)
  refine ⟨A, B, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    simp only [A, mem_image] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    simp only [interval, mem_Icc]
    have hiM := hleM i hi
    have hMm : M < m := (I.max' ⟨i₀, hi₀⟩).isLt
    omega
  · intro b hb
    simp only [B, mem_image] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    simp only [interval, mem_Icc]
    have hMmem : I.max' ⟨i₀, hi₀⟩ ∈ I := Finset.max'_mem I _
    have hr := hrel j hj (I.max' ⟨i₀, hi₀⟩) hMmem
    have hsIcc := hS hr.2
    simp only [interval, mem_Icc] at hsIcc
    dsimp [M] at hr hsIcc ⊢
    omega
  · change k ≤ #(I.image (fun i : Fin m => M + 1 - (i : ℕ)))
    rw [Finset.card_image_of_injOn]
    · exact hI.ge
    · intro i hi j hj hij
      apply Fin.val_injective
      have hiM : (i : ℕ) ≤ M := hleM i hi
      have hjM : (j : ℕ) ≤ M := hleM j hj
      dsimp only at hij
      omega
  · change k ≤ #(J.image (fun j : Fin (n + m) => (j : ℕ) - M))
    rw [Finset.card_image_of_injOn]
    · exact hJ.ge
    · intro j₁ hj₁ j₂ hj₂ hj
      apply Fin.val_injective
      have hMmem : I.max' ⟨i₀, hi₀⟩ ∈ I := Finset.max'_mem I _
      have h₁ := (hrel j₁ hj₁ (I.max' ⟨i₀, hi₀⟩) hMmem).1
      have h₂ := (hrel j₂ hj₂ (I.max' ⟨i₀, hi₀⟩) hMmem).1
      dsimp [M] at hj h₁ h₂
      omega
  · rw [Finset.add_subset_iff]
    rintro a ha b hb
    simp only [A, mem_image] at ha
    simp only [B, mem_image] at hb
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨j, hj, rfl⟩ := hb
    have hr := hrel j hj i hi
    have hiM := hleM i hi
    have hMmem : I.max' ⟨i₀, hi₀⟩ ∈ I := Finset.max'_mem I _
    have hMj := (hrel j hj (I.max' ⟨i₀, hi₀⟩) hMmem).1
    change M + 2 ≤ (j : ℕ) + 1 at hMj
    have heq : M + 1 - (i : ℕ) + ((j : ℕ) - M) = (j : ℕ) + 1 - (i : ℕ) := by
      omega
    rw [heq]
    exact hr.2

/-- A convenient unfiltered form of the reduction. The extra `n` accounts for the `n`
representations of the unusable element `1`. -/
theorem exists_pairEvent_of_zarankiewicz_add_lt {n m k : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {S : Finset ℕ} (hS : S ⊆ interval n)
    (hz : zarankiewicz (n + m) m k k + m < m * #S) :
    pairEvent n k S := by
  apply exists_pairEvent_of_zarankiewicz_lt hm hmn hS
  have hone : #{s ∈ S | ¬ 2 ≤ s} ≤ 1 := by
    refine le_trans (Finset.card_le_card (fun s hs => ?_)) (Finset.card_singleton 1).le
    simp only [mem_filter, not_le, mem_singleton] at hs ⊢
    have := hS hs.1
    simp only [interval, mem_Icc] at this
    omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (p := fun s => 2 ≤ s)
  nlinarith

/-- Density form of the constant-preserving reduction. -/
theorem pairEvent_of_zarankiewicz_lt_density {n m k : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {δ : ℝ} {S : Finset ℕ} (hS : S ⊆ interval n) (hcard : δ * n ≤ #S)
    (hz : (zarankiewicz (n + m) m k k : ℝ) + m < δ * m * n) :
    pairEvent n k S := by
  apply exists_pairEvent_of_zarankiewicz_add_lt hm hmn hS
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlt : (zarankiewicz (n + m) m k k : ℝ) + m < (m : ℝ) * #S := by
    calc
      (zarankiewicz (n + m) m k k : ℝ) + m < δ * m * n := hz
      _ ≤ (m : ℝ) * #S := by nlinarith
  exact_mod_cast hlt

end DenseSetsWithoutLargeSumsets
