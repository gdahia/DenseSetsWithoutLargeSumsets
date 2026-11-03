/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal

/-!
# Dense sets without large sumsets

Theorem 1.1 and Corollary 1.2 of Dahia, Marciano and Souza, *Dense sets without large sumsets*,
arXiv:2607.15269. Corollary C of Hernández and Hetzel, *On growth rates of infinite and finite
sumsets*, arXiv:2606.07310. Conjecture 4.10 and Question 4.12 of Kra, Moreira, Richter and
Robertson, *Problems on infinite sumset configurations in the integers and beyond*, Bull. Amer.
Math. Soc. 62 (2025), 537–574, whose function `φ(δ, N)` is `φ δ N`. The explicit exponent and
threshold of Theorem 1.1 and Corollary 1.2 are `α γ c` and `n₀ γ c`, and
`SimpleGraph.triangleRemovalBound ε` is the constant of the triangle removal lemma in Mathlib. The
proofs are in `Solution.lean`.
-/

@[expose] public section

open Filter Real
open scoped Finset Pointwise

namespace DenseSetsWithoutLargeSumsets

/-- The function `φ(δ, N)` of Kra, Moreira, Richter and Robertson: the largest integer `k` such that
every `S ⊆ [N]` with `|S| ≥ δ N` contains a sumset `A + B` with `A, B ⊆ [N]` and
`min {|A|, |B|} ≥ k`. -/
noncomputable def φ (δ : unitInterval) (N : ℕ) : ℕ :=
  sSup {k | ∀ S ⊆ Finset.Icc 1 N, (δ : ℝ) * N ≤ #S → ∃ A B : Finset ℕ,
    A ⊆ Finset.Icc 1 N ∧ B ⊆ Finset.Icc 1 N ∧ k ≤ #A ∧ k ≤ #B ∧ A + B ⊆ S}

/-- The exponent `α = γ / exp (exp (10 ^ 4 / c))` of Theorem 1.1 and Corollary 1.2: they hold for
densities `δ` above `n ^ (-α)`. -/
noncomputable def α (γ c : ℝ) : ℝ := γ / exp (exp (10 ^ 4 / c))

/-- The threshold `n₀ = exp (exp (10 ^ 5 / c) / (γ * T) ^ 16)` of Theorem 1.1 and Corollary 1.2,
where `T` is the triangle removal constant `triangleRemovalBound (γ ^ 2 / exp (3 * 10 ^ 4 / c))`:
they hold for every `n ≥ n₀`. -/
noncomputable def n₀ (γ c : ℝ) : ℝ :=
  exp (exp (10 ^ 5 / c) /
    (γ * SimpleGraph.triangleRemovalBound (γ ^ 2 / exp (3 * 10 ^ 4 / c))) ^ 16)

/-! ### Dense sets without large sumsets -/

/-- **Theorem 1.1.** Let `0 < γ ≤ 1` and `0 < c < 1`. For every `n ≥ n₀ γ c` and every `δ` with
`n ^ (-α γ c) < δ ≤ 1 - c`, some `S ⊆ [n]` with `|S| ≥ δ n` contains no sumset `A + B` with
`A, B ⊆ [n]` and `|A|, |B| ≥ (3 + γ) * log n / log (1 / δ)`. -/
theorem exists_dense_subset_forall_add_not_subset' {γ c : ℝ} (hγ : γ ∈ Set.Ioc 0 1)
    (hc : c ∈ Set.Ioo 0 1) {n : ℕ} (hn : n₀ γ c ≤ n) {δ : ℝ}
    (hδ : δ ∈ Set.Ioc ((n : ℝ) ^ (-α γ c)) (1 - c)) :
    ∃ S ⊆ Finset.Icc 1 n, δ * n ≤ #S ∧ ∀ A ⊆ Finset.Icc 1 n, ∀ B ⊆ Finset.Icc 1 n,
      ⌈(3 + γ) * log n / log (1 / δ)⌉₊ ≤ #A → ⌈(3 + γ) * log n / log (1 / δ)⌉₊ ≤ #B →
        ¬ A + B ⊆ S :=
  sorry

/-- **Corollary 1.2.** Let `0 < γ ≤ 1` and `0 < c < 1`. For every `n ≥ n₀ γ c` and every `δ` with
`n ^ (-α γ c) ≤ δ ≤ 1 - c`,
`(1 - γ) / log (1 / δ) ≤ φ(δ, n) / log n ≤ (3 + γ) / log (1 / δ)`. -/
theorem phi_div_log_mem_Icc' {γ c : ℝ} (hγ : γ ∈ Set.Ioc 0 1) (hc : c ∈ Set.Ioo 0 1) {n : ℕ}
    (hn : n₀ γ c ≤ n) {δ : unitInterval}
    (hδ : (δ : ℝ) ∈ Set.Icc ((n : ℝ) ^ (-α γ c)) (1 - c)) :
    (φ δ n : ℝ) / log n ∈ Set.Icc ((1 - γ) / log (1 / δ)) ((3 + γ) / log (1 / δ)) :=
  sorry

/-! ### The lower bound of Hernández and Hetzel -/

/-- **Corollary C of Hernández and Hetzel.** For fixed `0 < δ < 1`,
`1 / log (1 / δ) ≤ liminf φ(δ, N) / log N`. -/
theorem one_div_log_one_div_le_liminf_phi_div_log' {δ : unitInterval} (hδ : δ ∈ Set.Ioo 0 1) :
    1 / log (1 / δ) ≤ liminf (fun N : ℕ ↦ (φ δ N : ℝ) / log N) atTop :=
  sorry

/-! ### Conjecture 4.10 and Question 4.12 of Kra, Moreira, Richter and Robertson -/

/-- **Conjecture 4.10 of Kra, Moreira, Richter and Robertson.** For fixed `0 < δ < 1`,
`limsup φ(δ, N) / log N < ∞` and `liminf φ(δ, N) / log N > 0`, with both limits taken in the
extended reals. The conjecture is stated for every `δ > 0`; it fails for `δ = 1`, where
`φ(1, N) = N / 2`. -/
theorem limsup_phi_div_log_lt_top_and_liminf_phi_div_log_pos' {δ : unitInterval}
    (hδ : δ ∈ Set.Ioo 0 1) :
    limsup (fun N : ℕ ↦ ((φ δ N / log N : ℝ) : EReal)) atTop < ⊤ ∧
      0 < liminf (fun N : ℕ ↦ ((φ δ N / log N : ℝ) : EReal)) atTop :=
  sorry

/-- **Question 4.12 of Kra, Moreira, Richter and Robertson** asks whether
`liminf φ(δ_N, N) / log N > 0` for some sequence `δ_N → 0`. It is not: the limit inferior is `0`
for every sequence `δ_N → 0`. -/
theorem liminf_phi_div_log_eq_zero' (δ : ℕ → unitInterval)
    (hδ : Tendsto (fun N : ℕ ↦ (δ N : ℝ)) atTop (nhds 0)) :
    liminf (fun N : ℕ ↦ (φ (δ N) N : ℝ) / log N) atTop = 0 :=
  sorry

end DenseSetsWithoutLargeSumsets
