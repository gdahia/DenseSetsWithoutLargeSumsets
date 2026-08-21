/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import Mathlib

/-!
# Dense sets without large sumsets

Formal statement of the main theorem of *Dense sets without large sumsets*, by Gabriel Dahia,
João Pedro Marciano, and Victor Souza ([arXiv:2607.15269](https://arxiv.org/abs/2607.15269)).

Write `[n] = {1, …, n}` for the interval `Finset.Icc 1 n`, and write `A + B` for the sumset
`{a + b | a ∈ A, b ∈ B}`.

**Theorem.** Fix `0 < γ ≤ 1` and `0 < c < 1`. Then there is an exponent `α > 0` with the
following property. Let `(δ n)` be any sequence of densities such that, for all large `n`,

* `n ^ (-α) < δ n`, and
* `δ n ≤ 1 - c`.

Then, for all large `n`, there is a set `S ⊆ [n]` of size at least `δ n * n` which contains no
sumset `A + B` with `A, B ⊆ [n]` and

  `#A, #B ≥ ⌈(3 + γ) * log n / log (1 / δ n)⌉`.

The size threshold is sharp up to the value of `γ`: a set of density `δ` in `[n]` does contain
sumsets `A + B` with both summands of size roughly `log n / log (1 / δ)`, so the theorem cannot
hold with `3 + γ` replaced by a constant smaller than `1`. Taking `δ n` constant recovers the
statement quoted in the abstract of the paper, and answers a question of Kra, Moreira, Richter
and Robertson.
-/

open Filter
open scoped Pointwise

/-- **Dense sets without large sumsets.**  For every `0 < γ ≤ 1` and `0 < c < 1` there is an
exponent `α > 0` such that, for every density sequence `δ` eventually trapped between `n ^ (-α)`
and `1 - c`, all large `n` admit a set `S ⊆ [n]` with at least `δ n * n` elements containing no
sumset `A + B` of sets `A, B ⊆ [n]` with at least `⌈(3 + γ) * log n / log (1 / δ n)⌉` elements
each. -/
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
                ¬ A + B ⊆ S :=
  sorry
