/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DenseSetsWithoutLargeSumsets.Common

/-!
# The threshold function `φ(δ, N)`

Kra, Moreira, Richter and Robertson define `φ(δ, N)` as the largest integer `k` such that every
`A ⊆ [N]` with `|A| ≥ δ N` contains a sumset `B + C` with `B, C ⊆ [N]` and `min {|B|, |C|} ≥ k`
(*Problems on infinite sumset configurations in the integers and beyond*, Bull. Amer. Math. Soc.
62 (2025), 537–574, arXiv:2311.06197, Section 4.3). The set of such `k` contains `0`, is closed
downwards and is bounded by `N`, so it has a largest element.

## Main definitions

* `sumsetThresholdSet δ N`: the set of `k` with the property above.
* `phi δ N`: its supremum, the function `φ(δ, N)`.

## Main statements

* `phi_mem_sumsetThresholdSet`: the supremum is attained.
* `phi_lt_iff_existsDenseSetWithoutLargeSumsets`: `φ(δ, N) < k` if and only if some `S ⊆ [N]`
  with `|S| ≥ δ N` contains no sumset `A + B` with `A, B ⊆ [N]` and `|A|, |B| ≥ k`.
* `phi_mono`: `φ(δ, N)` is monotone in `δ`.
-/

@[expose] public section

namespace DenseSetsWithoutLargeSumsets

open scoped Pointwise

noncomputable section

/-- The set of `k` such that every `S ⊆ [N]` with `|S| ≥ δ N` contains a sumset `B + C` with
`B, C ⊆ [N]` and `min {|B|, |C|} ≥ k`. -/
def sumsetThresholdSet (δ : unitInterval) (N : ℕ) : Set ℕ :=
  {k | ∀ S : Finset ℕ, S ⊆ interval N → (δ : ℝ) * (N : ℝ) ≤ (S.card : ℝ) → pairEvent N k S}

/-- `φ(δ, N)`, the largest integer `k` such that every `A ⊆ [N]` with `|A| ≥ δ N` contains a sumset
`B + C` with `B, C ⊆ [N]` and `min {|B|, |C|} ≥ k`. -/
def phi (δ : unitInterval) (N : ℕ) : ℕ := sSup (sumsetThresholdSet δ N)

variable {δ δ' : unitInterval} {N k l : ℕ}

lemma sumsetThresholdSet_of_le (hkl : k ≤ l) (hl : l ∈ sumsetThresholdSet δ N) :
    k ∈ sumsetThresholdSet δ N := by
  intro S hS hcard
  obtain ⟨A, B, hA, hB, hAcard, hBcard, hAB⟩ := hl S hS hcard
  exact ⟨A, B, hA, hB, hkl.trans hAcard, hkl.trans hBcard, hAB⟩

lemma zero_mem_sumsetThresholdSet (δ : unitInterval) (N : ℕ) : 0 ∈ sumsetThresholdSet δ N :=
  fun _ _ _ ↦ ⟨∅, ∅, by simp, by simp, by simp, by simp, by simp⟩

lemma card_interval (N : ℕ) : (interval N).card = N := by
  simp [interval]

/-- Every element of `sumsetThresholdSet δ N` is at most `N`, as the set `S = [N]` shows. -/
lemma le_of_mem_sumsetThresholdSet (hk : k ∈ sumsetThresholdSet δ N) : k ≤ N := by
  obtain ⟨A, -, hA, -, hAcard, -⟩ := hk (interval N) subset_rfl
    (by simpa [card_interval] using mul_le_of_le_one_left N.cast_nonneg (unitInterval.le_one δ))
  exact hAcard.trans ((Finset.card_le_card hA).trans_eq (card_interval N))

lemma bddAbove_sumsetThresholdSet (δ : unitInterval) (N : ℕ) :
    BddAbove (sumsetThresholdSet δ N) :=
  ⟨N, fun _ hk ↦ le_of_mem_sumsetThresholdSet hk⟩

/-- The supremum that defines `phi δ N` is attained. -/
lemma phi_mem_sumsetThresholdSet (δ : unitInterval) (N : ℕ) : phi δ N ∈ sumsetThresholdSet δ N :=
  Nat.sSup_mem ⟨0, zero_mem_sumsetThresholdSet δ N⟩ (bddAbove_sumsetThresholdSet δ N)

lemma le_phi (hk : k ∈ sumsetThresholdSet δ N) : k ≤ phi δ N :=
  le_csSup (bddAbove_sumsetThresholdSet δ N) hk

lemma phi_le_self (δ : unitInterval) (N : ℕ) : phi δ N ≤ N :=
  le_of_mem_sumsetThresholdSet (phi_mem_sumsetThresholdSet δ N)

/-- If `k ≤ φ(δ, N)`, then every `S ⊆ [N]` with `|S| ≥ δ N` contains a sumset `A + B` with
`A, B ⊆ [N]` and `|A|, |B| ≥ k`. -/
lemma pairEvent_of_le_phi (hk : k ≤ phi δ N) {S : Finset ℕ} (hS : S ⊆ interval N)
    (hcard : (δ : ℝ) * (N : ℝ) ≤ (S.card : ℝ)) : pairEvent N k S :=
  sumsetThresholdSet_of_le hk (phi_mem_sumsetThresholdSet δ N) S hS hcard

/-- `φ(δ, N) < k` if and only if some `S ⊆ [N]` with `|S| ≥ δ N` contains no sumset `A + B` with
`A, B ⊆ [N]` and `|A|, |B| ≥ k`. -/
lemma phi_lt_iff_existsDenseSetWithoutLargeSumsets :
    phi δ N < k ↔ existsDenseSetWithoutLargeSumsets N k δ := by
  constructor
  · intro hlt
    by_contra hcon
    refine hlt.not_ge (le_phi ?_)
    intro S hS hcard
    by_contra hpair
    exact hcon ⟨S, hS, hcard, hpair⟩
  · rintro ⟨S, hS, hcard, hpair⟩
    by_contra hle
    exact hpair (pairEvent_of_le_phi (not_lt.mp hle) hS hcard)

alias ⟨_, phi_lt_of_existsDenseSetWithoutLargeSumsets⟩ :=
  phi_lt_iff_existsDenseSetWithoutLargeSumsets

lemma sumsetThresholdSet_mono (h : (δ : ℝ) ≤ (δ' : ℝ)) :
    sumsetThresholdSet δ N ⊆ sumsetThresholdSet δ' N := fun _ hk S hS hcard ↦
  hk S hS ((mul_le_mul_of_nonneg_right h N.cast_nonneg).trans hcard)

/-- `φ(δ, N)` is monotone in `δ`. -/
lemma phi_mono (h : (δ : ℝ) ≤ (δ' : ℝ)) : phi δ N ≤ phi δ' N :=
  le_phi (sumsetThresholdSet_mono h (phi_mem_sumsetThresholdSet δ N))

lemma phi_div_log_nonneg (δ : unitInterval) (N : ℕ) : 0 ≤ (phi δ N : ℝ) / Real.log N :=
  div_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg N)

lemma log_one_div_pos {x : ℝ} (hx : 0 < x) (hx' : x < 1) : 0 < Real.log (1 / x) :=
  Real.log_pos ((one_lt_div hx).mpr hx')

end

end DenseSetsWithoutLargeSumsets
