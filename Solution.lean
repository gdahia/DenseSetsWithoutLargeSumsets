/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets

/-!
# Solution module for the Palomar submission

Proof of the statement recorded in `Challenge.lean`.  The witness for the exponent is
`DenseSetsWithoutLargeSumsets.denseSubsetDensityExponent`, and the work is done by
`DenseSetsWithoutLargeSumsets.dense_subset_without_large_sumsets`; all that remains here is to
package the density sequence as a sequence in the unit interval and to turn the negated
existential of the main theorem into the universally quantified form of the challenge.
-/

open Filter
open scoped Pointwise

theorem dense_sets_without_large_sumsets {γ c : ℝ}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hc_pos : 0 < c) (hc_lt : c < 1) :
    ∃ α : ℝ, 0 < α ∧
      ∀ δ : ℕ → ℝ, (∀ n, 0 ≤ δ n) → (∀ n, δ n ≤ 1) →
        (∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-α) < δ n) →
        (∀ᶠ n : ℕ in atTop, δ n ≤ 1 - c) →
        ∀ᶠ n : ℕ in atTop,
          ∃ S ⊆ Finset.Icc 1 n,
            δ n * (n : ℝ) ≤ (S.card : ℝ) ∧
              ∀ A B : Finset ℕ, A ⊆ Finset.Icc 1 n → B ⊆ Finset.Icc 1 n →
                ⌈(3 + γ) * Real.log (n : ℝ) / Real.log (1 / δ n)⌉₊ ≤ A.card →
                ⌈(3 + γ) * Real.log (n : ℝ) / Real.log (1 / δ n)⌉₊ ≤ B.card →
                ¬ A + B ⊆ S := by
  refine ⟨DenseSetsWithoutLargeSumsets.denseSubsetDensityExponent γ c,
    DenseSetsWithoutLargeSumsets.denseSubsetDensityExponent_pos hγ_pos hc_pos hc_lt, ?_⟩
  intro δ hδ_nonneg hδ_le_one hδ_lower hδ_upper
  have hmain := DenseSetsWithoutLargeSumsets.dense_subset_without_large_sumsets
    hγ_pos hγ_le hc_pos hc_lt (fun n ↦ ⟨δ n, hδ_nonneg n, hδ_le_one n⟩) hδ_lower hδ_upper
  filter_upwards [hmain] with n hn
  obtain ⟨S, hS_subset, hS_card, hS_free⟩ := hn
  refine ⟨S, hS_subset, hS_card, ?_⟩
  intro A B hA hB hA_card hB_card hsum
  exact hS_free ⟨A, B, hA, hB, hA_card, hB_card, hsum⟩
