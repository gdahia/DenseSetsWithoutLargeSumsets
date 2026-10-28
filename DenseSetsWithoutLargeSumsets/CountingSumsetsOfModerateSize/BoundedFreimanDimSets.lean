/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import CountingSetsWithSmallSumset.SmallSumsetIsomorphismClasses.CoreParameters
public import SumOfSetsInSeveralDimensions.FreimanDimension
public import Mathlib.Analysis.SpecialFunctions.Exp
import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.MembersInInterval
import CountingSetsWithSmallSumset.FreimanIsomorphismClasses.RelationSpaces
import CountingSetsWithSmallSumset.SmallSumsetIsomorphismClasses.ClassCountBounds

/-!
# Sets of natural numbers of bounded Freiman dimension

This file counts the sets `X ⊆ [n] = {1, …, n}` of `t` elements with Freiman dimension at most
`r`, as in the proof of Proposition 23 of Green, *Counting sets with small sumset, and the clique
number of random Cayley graphs*. A Freiman isomorphism class of order `2` of such sets has at most
`n ^ (r + 1)` members in `[n]`. By Lemma 11 of Green, applied in `ℚ`, the sets of `t` natural
numbers lie in at most `t ^ (4 * t)` classes. By Proposition 18 of Green, those with
`|X + X| ≤ s ≤ t ^ (31 / 30) / 2` lie in at most `(2 * e * s / t) ^ t * exp (t ^ (31 / 32))`
classes, for `t ≥ 2 ^ 9000`. Green does not state these counts. They are used in Section 3 of
*Dense sets without large sumsets* (Dahia, Marciano, Souza).

## Main definitions

* `boundedFreimanDimSets n r t`: the sets `X ⊆ [n]` with `t` elements and Freiman dimension at
  most `r`.
* `smallSumsetFreimanDimSets n r s t`: the sets of `boundedFreimanDimSets n r t` with
  `|X + X| ≤ s`.

## Main statements

* `card_boundedFreimanDimSets`: there are at most `n ^ (r + 1) * t ^ (4 * t)` sets in
  `boundedFreimanDimSets n r t`.
* `smallSumsetFreimanDimSets_ncard_le`: if `t ≥ 2 ^ 9000` and `s ≤ t ^ (31 / 30) / 2`, there are
  at most `n ^ (r + 1) * (2 * e * s / t) ^ t * exp (t ^ (31 / 32))` sets in
  `smallSumsetFreimanDimSets n r s t`.
-/

@[expose] public section

namespace DenseSetsWithoutLargeSumsets

open Finset Real CountingSetsWithSmallSumset SumOfSetsInSeveralDimensions
open scoped Pointwise

/-- The sets `X ⊆ [n]` with `t` elements and Freiman dimension at most `r`. -/
def boundedFreimanDimSets (n r t : ℕ) : Set (Finset ℕ) :=
  {X : Finset ℕ | X ⊆ Icc 1 n ∧ #X = t ∧ freimanDim X ≤ r}

/-- The sets `X` of `boundedFreimanDimSets n r t` with `|X + X| ≤ s`. -/
def smallSumsetFreimanDimSets (n r s t : ℕ) : Set (Finset ℕ) :=
  {X : Finset ℕ | X ⊆ Icc 1 n ∧ #X = t ∧ freimanDim X ≤ r ∧ #(X + X) ≤ s}

/-- There are at most `n ^ (r + 1) * t ^ (4 * t)` sets `X ⊆ [n]` with `t` elements and Freiman
dimension at most `r`. -/
lemma card_boundedFreimanDimSets (n r : ℕ) {t : ℕ} (ht : 0 < t) :
    (boundedFreimanDimSets n r t).ncard ≤ (n : ℝ) ^ (r + 1) * t ^ (4 * t) := by
  obtain ⟨representatives, hrep, hcard⟩ := exists_representsFreimanIsoClasses_card_le_pow ℚ ℚ 2 t
  have hsub : image (Nat.castAddMonoidHom ℚ) '' boundedFreimanDimSets n r t ⊆ {A | #A = t} := by
    rintro _ ⟨X, ⟨-, hX, -⟩, rfl⟩
    simpa [card_image_of_injective _ Nat.cast_injective]
  obtain ⟨representatives', -, hrep', hcard'⟩ := exists_representsFreimanIsoClasses_card_le_of_image
    (isAddFreimanIso_image_of_injective 2 (φ := Nat.castAddMonoidHom ℚ) Nat.cast_injective)
    (hrep.subset hsub)
  rw [mul_comm]
  exact_mod_cast (ncard_le_card_mul_pow_of_representsFreimanIsoClasses hrep' fun X ⟨hXn, hX, hXr⟩ ↦
    ⟨card_pos.1 (hX ▸ ht), hXn, hXr⟩).trans (Nat.mul_le_mul_right _ (hcard'.trans hcard))

/-- Let `t ≥ 2 ^ 9000` and `s ≤ t ^ (31 / 30) / 2`. There are at most
`n ^ (r + 1) * (2 * e * s / t) ^ t * exp (t ^ (31 / 32))` sets `X ⊆ [n]` with `|X| = t`,
`freimanDim X ≤ r` and `|X + X| ≤ s`. -/
lemma smallSumsetFreimanDimSets_ncard_le (n r s t : ℕ)
    (ht : smallSumsetClassCountThreshold ≤ t)
    (hs : s ≤ (t : ℝ) ^ ((31 : ℝ) / 30) / 2) :
    (smallSumsetFreimanDimSets n r s t).ncard ≤
      n ^ (r + 1) * (2 * exp 1 * s / t) ^ t * exp (t ^ ((31 : ℝ) / 32)) := by
  have hm : ((2 * s : ℕ) : ℝ) ≤ (t : ℝ) ^ ((31 : ℝ) / 30) := by
    push_cast
    linarith
  obtain ⟨representatives, hrep, hcard⟩ :=
    exists_representsFreimanIsoClasses_card_restrictedSumset_le_of_injective ℚ
      (φ := Nat.castAddMonoidHom ℚ) Nat.cast_injective ht hm
  have hsub : smallSumsetFreimanDimSets n r s t ⊆
      {A : Finset ℕ | #A = t ∧ #(restrictedSumset A) ≤ 2 * s} := by
    rintro X ⟨-, hX, -, hXs⟩
    exact ⟨hX, (card_restrictedSumset_le_card_add X).trans (by grind)⟩
  refine (Nat.cast_le.2 (ncard_le_card_mul_pow_of_representsFreimanIsoClasses (hrep.subset hsub)
    fun X ⟨hXn, hX, hXr, _⟩ ↦ ⟨card_pos.1 (hX ▸ pos_of_smallSumsetClassCountThreshold_le ht),
      hXn, hXr⟩)).trans ?_
  rw [Nat.cast_mul, Nat.cast_pow, mul_comm, mul_assoc]
  refine (mul_le_mul_of_nonneg_left hcard (by positivity)).trans_eq ?_
  push_cast
  ring

end DenseSetsWithoutLargeSumsets
