/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DenseSetsWithoutLargeSumsets.Probability
public import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.CountingBaseBounds
public import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.WitnessPairs
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.EventSubset
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.ExponentBounds
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.LargeSubsetsGAP
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.ThresholdEstimates
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.WitnessPairProbability

/-!
# A random set contains no pair with a small sumset

Let `S` be a `δ`-random subset of `[n]` and let `k = pairCardThreshold (3 + γ) n δ`. This file
proves the result of Section 2 of *Dense sets without large sumsets* (Dahia, Marciano, Souza): the
probability that `S` contains `A + B` for some `A, B ⊆ [n]` of size `k` with `|A + B| ≤ C * k` is
at most `2 * k / n ^ (ε γ / 2)`.

The event is covered by the events `A' + B' ⊆ S`, where `(A', B')` ranges over the pairs of
`bltDimSmallWitnessPairs` for the proper progressions of `lowerModelGAPs`. The probability of each
is at most `δ ^ |A' + B'|`, and the sum of these bounds over the progressions of a given dimension
is at most `n ^ (-(ε γ / 2))`.

## Main definitions

* `smallSumsetMeasure n δ`: the distribution of a `δ`-random subset of `[n]`.

## Main statements

* `small_sumset_pair_probability_le_fingerprint_sum`: the union bound over progressions and
  pairs.
* `small_sumset_pair_probability_le`: the probability is at most `2 * k / n ^ (ε γ / 2)`.
* `exists_forall_setBernoulli_real_pairSumsetIsSubset_le`: Lemma 2.1 of the paper, with the
  exponent `α` quantified and the random set distributed as `setBernoulli (Set.Icc 1 n) δ`.
-/

@[expose] public section

namespace DenseSetsWithoutLargeSumsets

open Finset MeasureTheory
open scoped Pointwise

noncomputable section

/-- The distribution of a `δ`-random subset of `[n]`. -/
abbrev smallSumsetMeasure (n : ℕ) (δ : unitInterval) :
    MeasureTheory.Measure (Finset ℕ) :=
  binomialFinsetSubset (Set.Icc 1 n) δ

/-- The probability that a `δ`-random subset of `[n]` contains `A + B` for some `A, B ⊆ [n]` of
size `k = pairCardThreshold (3 + γ) n δ` with `|A + B| ≤ C * k` is at most the sum of
`δ ^ |A' + B'|` over the progressions `P` of `lowerModelGAPs` and the pairs `(A', B')` of
`bltDimSmallWitnessPairs` for `P`. -/
lemma small_sumset_pair_probability_le_fingerprint_sum {γ C c : ℝ} {n : ℕ}
    {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (C_pos : 0 < C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c) :
    (smallSumsetMeasure n δ).real
        (pairSumsetIsSubset n (pairCardThreshold (3 + γ) n δ) 0
          (C * pairCardThreshold (3 + γ) n δ)) ≤
      ∑ P ∈ lowerModelGAPs δ hγ_pos C_pos hn,
        ∑ p ∈ bltDimSmallWitnessPairs
            (zmodGAPPreimageContainer n (zmodModelEmbedding hγ_pos C_pos hn) P)
            P.dim (pairCardThreshold (3 + γ) n δ) C γ,
          (δ : ℝ) ^ #(p.1 + p.2) := by
  refine (measureReal_mono (pairSumsetIsSubset_event_subset_zmodGAPPreimageDimSmallWitnessPairs
    hγ_pos hγ_le C_pos hc_pos hc_lt hn hn_gap hδ_lower hδ_upper hδ_upper_c)
    (measure_ne_top _ _)).trans ?_
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  gcongr with P
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  gcongr with p
  exact bltWitnessPair_probability_le n p

private lemma sum_sum_pow_le_two_mul_div {γ C c : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (C_pos : 0 < C) (hC_one : 1 ≤ C)
    (hc_pos : 0 < c) (hc_lt : c < 1) (hn : lowerSizeThreshold C γ < n)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1)
    (hδ_upper_c : (δ : ℝ) ≤ 1 - c) :
    ∑ P ∈ lowerModelGAPs δ hγ_pos C_pos hn,
        ∑ p ∈ bltDimSmallWitnessPairs
            (zmodGAPPreimageContainer n (zmodModelEmbedding hγ_pos C_pos hn) P)
            P.dim (pairCardThreshold (3 + γ) n δ) C γ,
          (δ : ℝ) ^ #(p.1 + p.2) ≤
      2 * (pairCardThreshold (3 + γ) n δ : ℝ) / (n : ℝ) ^ (ε γ / 2) := by
  have hC_two : 0 < 2 * C := by positivity
  refine (dim_fingerprint_sum_le_gap_dim_sum (zmodModelEmbedding hγ_pos C_pos hn)
    (zmodModelQ_prime hγ_pos C_pos hn).pos (zmodModelEmbedding_iso hγ_pos C_pos hn).bijOn.injOn
    hC_two (ε_pos hγ_pos) (unitInterval_pos_of_density_lower hn hδ_lower) hδ_upper).trans ?_
  refine (sum_le_card_nsmul _ _ ((n : ℝ) ^ (-(ε γ / 2))) ?_).trans ?_
  · intro d hd
    exact mod_cast lower_gap_dim_summand_le hγ_pos hγ_le C_pos hC_one hc_pos hc_lt hn hn_gap
      hδ_lower hδ_upper hδ_upper_c hC_two (ε_pos hγ_pos) hd
  · rw [Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul,
      Real.rpow_neg (old_model_threshold_nat_pos hn).le, ← div_eq_mul_inv]
    gcongr
    linarith [Nat.cast_nonneg (α := ℝ) (pairCardThreshold (3 + γ) n δ)]

/-- Let `S` be a `δ`-random subset of `[n]` and let `k = pairCardThreshold (3 + γ) n δ`. If
`n > lowerGapThreshold C γ c` and `n ^ (-lowerDensityExponent C γ) < δ ≤ 1 - c`, then the
probability that `S` contains `A + B` for some `A, B ⊆ [n]` of size `k` with `|A + B| ≤ C * k` is
at most `2 * k / n ^ (ε γ / 2)`. -/
lemma small_sumset_pair_probability_le {γ C c : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (C_pos : 0 < C) (hc_pos : 0 < c)
    (hn_gap : lowerGapThreshold C γ c < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ))
    (hδ_upper : (δ : ℝ) ≤ 1 - c) :
    (smallSumsetMeasure n δ).real
        (pairSumsetIsSubset n (pairCardThreshold (3 + γ) n δ) 0
          (C * pairCardThreshold (3 + γ) n δ)) ≤
      2 * (pairCardThreshold (3 + γ) n δ : ℝ) / (n : ℝ) ^ (ε γ / 2) := by
  have hn := (lowerSizeThreshold_le_lowerGapThreshold C γ c).trans_lt hn_gap
  have hc_lt : c < 1 := by linarith [unitInterval_pos_of_density_lower hn hδ_lower]
  have hδ_lt : (δ : ℝ) < 1 := by linarith
  obtain hC | hC := le_or_gt 1 C
  · exact (small_sumset_pair_probability_le_fingerprint_sum hγ_pos hγ_le C_pos hc_pos hc_lt hn
      hn_gap hδ_lower hδ_lt hδ_upper).trans (sum_sum_pow_le_two_mul_div hγ_pos hγ_le C_pos hC
      hc_pos hc_lt hn hn_gap hδ_lower hδ_lt hδ_upper)
  · refine (measureReal_mono (s₂ := ∅) ?_ (measure_ne_top _ _)).trans ?_
    · rintro S ⟨A, B, -, -, hAcard, hBcard, -, hAB, -⟩
      exact hC.not_ge (one_le_sumset_card_coefficient_of_threshold_pair_sumset hγ_pos hn hδ_lower
        hδ_lt hAcard hBcard hAB)
    · rw [measureReal_empty]
      positivity

/-- **Lemma 2.1.** Let `0 < γ ≤ 1`, `C > 1` and `c > 0`. There is `α > 0` such that, for all large
`n`, every `n ^ (-α) < δ ≤ 1 - c` and `k = ⌈(3 + γ) * log n / log (1 / δ)⌉`, the `δ`-random subset
of `[n]` contains a sumset `A + B` with `A, B ⊆ [n]`, `|A| = |B| = k` and `|A + B| ≤ C * k` with
probability at most `2 * k / n ^ (γ / (8 * (γ + 2)))`. -/
theorem exists_forall_setBernoulli_real_pairSumsetIsSubset_le {γ C c : ℝ} (hγ : 0 < γ)
    (hγ' : γ ≤ 1) (hC : 1 < C) (hc : 0 < c) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ δ : unitInterval, (n : ℝ) ^ (-α) < δ →
      (δ : ℝ) ≤ 1 - c →
        (ProbabilityTheory.setBernoulli (Set.Icc 1 n) δ).real
            ((↑) '' {S : Finset ℕ | pairSumsetIsSubset n (pairCardThreshold (3 + γ) n δ) 0
              (C * pairCardThreshold (3 + γ) n δ) S}) ≤
          2 * pairCardThreshold (3 + γ) n δ / n ^ (γ / (8 * (γ + 2))) := by
  refine ⟨lowerDensityExponent C γ, lowerDensityExponent_pos_of_one_le hγ hC.le, ?_⟩
  filter_upwards [Filter.eventually_gt_atTop ⌈lowerGapThreshold C γ c⌉₊] with n hn δ hδ hδ'
  rw [← binomialFinsetSubset_real_eq_image (Set.finite_Icc 1 n), ← ε_div_two]
  exact small_sumset_pair_probability_le hγ hγ' (by linarith) hc (Nat.lt_of_ceil_lt hn) hδ hδ'

end

end DenseSetsWithoutLargeSumsets
