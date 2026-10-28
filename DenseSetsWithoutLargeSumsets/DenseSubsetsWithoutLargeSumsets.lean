/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DenseSetsWithoutLargeSumsets.SimpleBoundForVeryLargeSumsets
public import DenseSetsWithoutLargeSumsets.CountingSumsetsOfModerateSize.Probability
public import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.Constants
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.MainTheorem
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.ThresholdEstimates

/-!
# Dense subsets of `[n]` without large sumsets

This file proves Theorems 1.1 and 1.3 of *Dense sets without large sumsets* (Dahia, Marciano,
Souza). Let `k = ⌈(3 + γ) * log n / log (1 / δ)⌉` and let `S` be a random subset of `[n]` that
contains each element independently with probability `δ`.

The pairs `(A, B)` of `k`-subsets of `[n]` are split into three ranges according to the size of
`A + B`: at most `C * k`, between `C * k` and `k * (k + 1) / 2`, and at least `(k + 1) * k / 2`.
The files `RandomSetContainsNoSmallSumset`, `CountingSumsetsOfModerateSize` and
`SimpleBoundForVeryLargeSumsets` bound the probability that `S` contains a sumset `A + B` in each
range. The sum of the three bounds is at most `4 * k ^ 2 / n ^ (γ / (8 * (γ + 3)))`, which tends
to zero. Since `|S| ≥ δ n` with probability at least `1 / 4`, some `S ⊆ [n]` with `|S| ≥ δ n`
contains no sumset `A + B` with `|A|, |B| ≥ k`.

## Main definitions

* `denseSubsetDensityExponent γ c`: the exponent `α` of Theorems 1.1 and 1.3.

## Main statements

* `eventually_pairEvent_probability_le`: Theorem 1.3, with the bound above on the probability.
* `exists_forall_setBernoulli_real_pairEvent_le`: Theorem 1.3 with the exponent `α` quantified
  and the random set distributed as `setBernoulli (Set.Icc 1 n) δ`.
* `eventually_forall_exists_dense_subset_without_large_sumsets`: Theorem 1.1, for all large `n` and
  every `δ` with `n ^ (-α) < δ ≤ 1 - c`.
* `dense_subset_without_large_sumsets`: Theorem 1.1 along a sequence of densities.
* `exists_dense_subset_forall_add_not_subset`: Theorem 1.1 with the exponent `α` quantified, as
  stated in `Challenge.lean`.
-/

@[expose] public section

namespace DenseSetsWithoutLargeSumsets

open Filter Finset MeasureTheory Real
open scoped Pointwise

noncomputable section

/-- The sets that contain a sumset `A + B` with `A, B ⊆ [n]`, `|A| = |B| = k` and
`|A + B| ≤ C * k`. -/
def smallSumsetEvent (n k : ℕ) (C : ℝ) : Set (Finset ℕ) :=
  {S | pairSumsetIsSubset n k 0 (C * k) S}

/-- The sets that contain a sumset `A + B` with `A, B ⊆ [n]`, `|A| = |B| = k` and
`C * k < |A + B| < k * (k + 1) / 2`. -/
def mediumSumsetEvent (n k : ℕ) (C : ℝ) : Set (Finset ℕ) :=
  {S | moderateSumsetEvent n k C S}

/-- The sets that contain a sumset `A + B` with `A, B ⊆ [n]`, `|A| = |B| = k` and
`|A + B| ≥ (k + 1) * k / 2`. -/
def largeSumsetEvent (n k : ℕ) : Set (Finset ℕ) :=
  {S | veryLargeSumsetEvent n k S}

lemma pairEvent_subset_three_ranges {n k : ℕ} {C : ℝ} :
    {S : Finset ℕ | exactPairEvent n k S} ⊆
      smallSumsetEvent n k C ∪ mediumSumsetEvent n k C ∪ largeSumsetEvent n k := by
  rintro S ⟨A, B, hA, hB, hAk, hBk, hS⟩
  obtain h₁ | h₁ := le_or_gt (#(A + B) : ℝ) (C * k)
  · exact Or.inl (Or.inl ⟨A, B, hA, hB, hAk, hBk, by positivity, h₁, hS⟩)
  obtain h₂ | h₂ := lt_or_ge #(A + B) (k * (k + 1) / 2)
  · exact Or.inl (Or.inr ⟨A, B, hA, hB, hAk, hBk, h₁, h₂, hS⟩)
  · exact Or.inr ⟨A, B, hA, hB, hAk, hBk, by grind, hS⟩

lemma pairEvent_measure_le_three_ranges {n k : ℕ} {δ : unitInterval} {C L M G : ℝ}
    (hlower : (binomialFinsetSubset (Set.Icc 1 n) δ).real (smallSumsetEvent n k C) ≤ L)
    (hmid : (binomialFinsetSubset (Set.Icc 1 n) δ).real (mediumSumsetEvent n k C) ≤ M)
    (hlarge : (binomialFinsetSubset (Set.Icc 1 n) δ).real (largeSumsetEvent n k) ≤ G) :
    (binomialFinsetSubset (Set.Icc 1 n) δ).real {S | exactPairEvent n k S} ≤ L + M + G := by
  refine (measureReal_mono (pairEvent_subset_three_ranges (C := C))).trans
    ((measureReal_union_le _ _).trans ?_)
  exact add_le_add ((measureReal_union_le _ _).trans (add_le_add hlower hmid)) hlarge

private lemma pairEvent_subset_exactPairEvent {n k : ℕ} :
    {S : Finset ℕ | pairEvent n k S} ⊆ {S | exactPairEvent n k S} := by
  rintro S ⟨A, B, hA, hB, hAk, hBk, hS⟩
  obtain ⟨A', hA', hA'k⟩ := exists_subset_card_eq hAk
  obtain ⟨B', hB', hB'k⟩ := exists_subset_card_eq hBk
  exact ⟨A', B', hA'.trans hA, hB'.trans hB, hA'k, hB'k, (add_subset_add hA' hB').trans hS⟩

private lemma rpow_neg_lt_of_le {n : ℕ} {α β δ : ℝ} (hn : 1 ≤ n) (hαβ : α ≤ β)
    (hδ : Real.rpow n (-α) < δ) : (n : ℝ) ^ (-β) < δ :=
  (rpow_le_rpow_of_exponent_le (mod_cast hn) (neg_le_neg hαβ)).trans_lt hδ

private lemma pairEventDecayExponent_pos {γ : ℝ} (hγ : 0 < γ) : 0 < pairEventDecayExponent γ :=
  div_pos hγ (by positivity)

private lemma pairEventDecayExponent_le {γ : ℝ} (hγ : 0 < γ) : pairEventDecayExponent γ ≤ γ / 24 :=
  div_le_div_of_nonneg_left hγ.le (by norm_num) (by linarith)

/-- The sum of the bounds for the three ranges is at most `4 * k ^ 2 / n ^ (γ / (8 * (γ + 3)))`. -/
private lemma add_add_le_four_mul_sq_div_rpow {γ C k : ℝ} {n : ℕ} (hγ_pos : 0 < γ)
    (hγ_le : γ ≤ 1) (hC : 1 ≤ C) (hn : 1 ≤ n) (hk : 2 ≤ k) :
    2 * k / (n : ℝ) ^ (ε γ / 2) + 2 * k ^ 2 / (n : ℝ) ^ ((1 + γ) * C / 2) +
        k ^ 2 / (n : ℝ) ^ (γ * k / 3) ≤
      4 * k ^ 2 / (n : ℝ) ^ pairEventDecayExponent γ := by
  have hn₁ : (1 : ℝ) ≤ n := mod_cast hn
  have he := pairEventDecayExponent_le hγ_pos
  have h : 4 * k ^ 2 = k ^ 2 + 2 * k ^ 2 + k ^ 2 := by ring
  rw [h, add_div, add_div]
  gcongr
  · nlinarith
  · rw [pairEventDecayExponent, ε, div_div]
    exact div_le_div_of_nonneg_left hγ_pos.le (by positivity) (by linarith)
  · nlinarith [mul_nonneg hγ_pos.le (zero_le_one.trans hC)]
  · nlinarith

lemma pairEvent_measure_le_three_ranges_of_bounds {γ α c : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1)
    (hc_pos : 0 < c) {n : ℕ}
    (hn_low : lowerGapThreshold (moderateSumsetGapConstant (1 + γ) c) γ c < n)
    (hn_large : veryLargeSumsetStrictThreshold γ c < n)
    {δ : unitInterval} (hδ_lower : Real.rpow (n : ℝ) (-α) < (δ : ℝ))
    (hδ_upper : (δ : ℝ) ≤ 1 - c)
    (hα_lower : α ≤ lowerDensityExponent (moderateSumsetGapConstant (1 + γ) c) γ)
    (hα_mid : α ≤ moderateSumsetDensityExponent (1 + γ) c)
    (hα_half : α ≤ 1 / 2)
    (hn_two : 2 ≤ n)
    (hk_two : 2 ≤ pairCardThreshold (3 + γ) n δ) :
    (binomialFinsetSubset (Set.Icc 1 n) δ).real
        {S | pairEvent n (pairCardThreshold (3 + γ) n δ) S} ≤
      4 * (pairCardThreshold (3 + γ) n δ : ℝ) ^ 2 /
        Real.rpow (n : ℝ) (pairEventDecayExponent γ) := by
  have hδ₀ : (0 : ℝ) < δ := (rpow_pos_of_pos (by positivity) (-α)).trans hδ_lower
  have hn₁ : 1 ≤ n := one_le_two.trans hn_two
  have hC := one_le_moderateSumsetGapConstant (γ := 1 + γ) (by linarith) hc_pos (by linarith)
  have hM := moderate_sumset_probability_le (γ := 1 + γ) (by linarith) (by linarith) hc_pos hn_two
    (rpow_neg_lt_of_le hn₁ hα_mid hδ_lower) hδ_upper
  rw [← add_assoc, two_add_one_eq_three] at hM
  refine (measureReal_mono pairEvent_subset_exactPairEvent).trans ?_
  refine (pairEvent_measure_le_three_ranges
    (small_sumset_pair_probability_le hγ_pos hγ_le (zero_lt_one.trans_le hC) hc_pos hn_low
      (rpow_neg_lt_of_le hn₁ hα_lower hδ_lower) hδ_upper)
    hM
    (very_large_sumset_probability_le hγ_pos hγ_le hc_pos hn_large
      (rpow_neg_lt_of_le hn₁ hα_half hδ_lower) hδ_upper)).trans ?_
  exact add_add_le_four_mul_sq_div_rpow hγ_pos hγ_le hC hn₁ (mod_cast hk_two)

lemma eventually_pairEvent_bound_lt {γ α c ε : ℝ} (hγ_pos : 0 < γ) (hc_pos : 0 < c)
    (hc_lt : c < 1) (hε_pos : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ∀ δ : unitInterval,
        Real.rpow (n : ℝ) (-α) < (δ : ℝ) → (δ : ℝ) ≤ 1 - c →
          4 * (pairCardThreshold (3 + γ) n δ : ℝ) ^ 2 /
              Real.rpow (n : ℝ) (pairEventDecayExponent γ) < ε := by
  have hq := densityCoefficient_pos (τ := 3 + γ) (by linarith) hc_pos hc_lt
  have hlog :=
    (isLittleO_log_rpow_rpow_atTop 2 (pairEventDecayExponent_pos hγ_pos)).tendsto_div_nhds_zero
  filter_upwards [(hlog.comp tendsto_natCast_atTop_atTop).eventually_lt_const
      (div_pos hε_pos (mul_pos four_pos (pow_pos hq 2))), eventually_ge_atTop 2]
    with n hn hn₂ δ hδ_lower hδ_upper
  have hn₀ : (0 : ℝ) < n := by positivity
  have hk := pairCardThreshold_le_densityCoefficient_mul_log (τ := 3 + γ) (by linarith) hc_pos hn₂
    ((rpow_pos_of_pos hn₀ _).trans hδ_lower) hδ_upper
  rw [Function.comp_apply, rpow_two] at hn
  refine lt_of_le_of_lt ?_ ((lt_div_iff₀' (by positivity)).1 hn)
  rw [rpow_eq_pow, ← mul_div_assoc, mul_assoc, ← mul_pow]
  gcongr

lemma eventually_pairEvent_bound_lt_quarter {γ α c : ℝ} (hγ_pos : 0 < γ) (hc_pos : 0 < c)
    (hc_lt : c < 1) :
    ∀ᶠ n : ℕ in atTop,
      ∀ δ : unitInterval,
        Real.rpow (n : ℝ) (-α) < (δ : ℝ) → (δ : ℝ) ≤ 1 - c →
          4 * (pairCardThreshold (3 + γ) n δ : ℝ) ^ 2 /
              Real.rpow (n : ℝ) (pairEventDecayExponent γ) < 1 / 4 :=
  eventually_pairEvent_bound_lt hγ_pos hc_pos hc_lt (by norm_num)

lemma exists_dense_set_of_pair_probability_lt_quarter {n k : ℕ} {δ : unitInterval}
    (hmean : (3 : ℝ) ≤ (δ : ℝ) * (n : ℝ))
    (hprob : (binomialFinsetSubset (Set.Icc 1 n) δ).real {S | pairEvent n k S} < 1 / 4) :
    existsDenseSetWithoutLargeSumsets n k δ := by
  by_contra h
  refine hprob.not_ge ((binomialFinsetSubset_real_dense_event_ge_quarter n δ hmean).trans
    (measureReal_mono ?_))
  rintro S ⟨hSn, hScard⟩
  by_contra hpair
  exact h ⟨S, hSn, hScard, hpair⟩

/-- The exponent `α` of Theorems 1.1 and 1.3. The densities considered are those larger than
`n ^ (-α)`. -/
def denseSubsetDensityExponent (γ c : ℝ) : ℝ :=
  min (1 / 2)
    (min (lowerDensityExponent (moderateSumsetGapConstant (1 + γ) c) γ)
      (moderateSumsetDensityExponent (1 + γ) c))

lemma denseSubsetDensityExponent_pos {γ c : ℝ} (hγ_pos : 0 < γ) (hc_pos : 0 < c)
    (hc_lt : c < 1) :
    0 < denseSubsetDensityExponent γ c := by
  refine lt_min (by norm_num) (lt_min ?_ (moderateSumsetDensityExponent_pos (by linarith)))
  exact lowerDensityExponent_pos_of_one_le hγ_pos
    (one_le_moderateSumsetGapConstant (by linarith) hc_pos hc_lt)

/-- Theorem 1.3. Let `k = ⌈(3 + γ) * log n / log (1 / δ)⌉` and
`α = denseSubsetDensityExponent γ c`. For all large `n` and every `δ` with
`n ^ (-α) < δ ≤ 1 - c`, the random subset of `[n]` of density `δ` contains a sumset `A + B` with
`A, B ⊆ [n]` and `|A|, |B| ≥ k` with probability at most `4 * k ^ 2 / n ^ (γ / (8 * (γ + 3)))`. -/
theorem eventually_pairEvent_probability_le {γ c : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1)
    (hc_pos : 0 < c) (hc_lt : c < 1) :
    eventuallyForDensities (denseSubsetDensityExponent γ c) c fun n δ ↦
      let ℙ : Measure (Finset ℕ) := binomialFinsetSubset (Set.Icc 1 n) δ
      ℙ.real (pairEvent n (pairCardThreshold (3 + γ) n δ)) ≤
        4 * (pairCardThreshold (3 + γ) n δ : ℝ) ^ 2 /
          Real.rpow (n : ℝ) (pairEventDecayExponent γ) := by
  rw [eventuallyForDensities]
  filter_upwards [
    eventually_gt_atTop ⌈lowerGapThreshold (moderateSumsetGapConstant (1 + γ) c) γ c⌉₊,
    eventually_gt_atTop (veryLargeSumsetStrictThreshold γ c), eventually_ge_atTop 2]
    with n hn_low hn_large hn_two δ hδ_lower hδ_upper
  refine pairEvent_measure_le_three_ranges_of_bounds hγ_pos hγ_le hc_pos (Nat.lt_of_ceil_lt hn_low)
    hn_large hδ_lower hδ_upper ?_ ?_ (min_le_left _ _) hn_two ?_
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)
  · exact pairCardThreshold_ge_two_of_density_lower (by linarith)
      ((min_le_left _ _).trans (by linarith)) hn_two (by linarith) hδ_lower

/-- **Theorem 1.3.** For `0 < γ ≤ 1` and `0 < c < 1` there is `α > 0` such that, for all large
`n`, every `n ^ (-α) < δ ≤ 1 - c` and `k = ⌈(3 + γ) * log n / log (1 / δ)⌉`, the `δ`-random subset
of `[n]` contains a sumset `A + B` with `A, B ⊆ [n]` and `|A|, |B| ≥ k` with probability at most
`4 * k ^ 2 / n ^ (γ / (8 * (γ + 3)))`. -/
theorem exists_forall_setBernoulli_real_pairEvent_le {γ c : ℝ} (hγ : 0 < γ) (hγ' : γ ≤ 1)
    (hc : 0 < c) (hc' : c < 1) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop, ∀ δ : unitInterval, (n : ℝ) ^ (-α) < δ →
      (δ : ℝ) ≤ 1 - c →
        (ProbabilityTheory.setBernoulli (Set.Icc 1 n) δ).real
            ((↑) '' {S : Finset ℕ | pairEvent n (pairCardThreshold (3 + γ) n δ) S}) ≤
          4 * pairCardThreshold (3 + γ) n δ ^ 2 / n ^ (γ / (8 * (γ + 3))) := by
  refine ⟨denseSubsetDensityExponent γ c, denseSubsetDensityExponent_pos hγ hc hc', ?_⟩
  filter_upwards [eventually_pairEvent_probability_le hγ hγ' hc hc'] with n hn δ hδ hδ'
  rw [← binomialFinsetSubset_real_eq_image (Set.finite_Icc 1 n)]
  exact hn δ hδ hδ'

private lemma three_le_rpow_neg_mul {n : ℕ} {α : ℝ} (hn : 9 ≤ n) (hα : α ≤ 1 / 2) :
    3 ≤ (n : ℝ) ^ (-α) * n := by
  have hn₉ : (9 : ℝ) ≤ n := mod_cast hn
  rw [← rpow_add_one (by positivity)]
  refine le_trans ?_ (rpow_le_rpow_of_exponent_le (by linarith) (by linarith : 1 / 2 ≤ -α + 1))
  rw [← sqrt_eq_rpow]
  exact (le_sqrt' three_pos).2 (by linarith)

/-- Theorem 1.1, uniformly in the density. For all large `n` and every `δ` with
`n ^ (-α) < δ ≤ 1 - c`, where `α = denseSubsetDensityExponent γ c`, there is `S ⊆ [n]` with
`|S| ≥ δ n` that contains no sumset `A + B` with `A, B ⊆ [n]` and
`|A|, |B| ≥ ⌈(3 + γ) * log n / log (1 / δ)⌉`. -/
theorem eventually_forall_exists_dense_subset_without_large_sumsets {γ c : ℝ} (hγ_pos : 0 < γ)
    (hγ_le : γ ≤ 1) (hc_pos : 0 < c) (hc_lt : c < 1) :
    ∀ᶠ n : ℕ in atTop,
      ∀ δ : unitInterval,
        Real.rpow (n : ℝ) (-denseSubsetDensityExponent γ c) < (δ : ℝ) →
        (δ : ℝ) ≤ 1 - c →
        ∃ S : Finset ℕ,
          S ⊆ Finset.Icc 1 n ∧
          (δ : ℝ) * (n : ℝ) ≤ (#S : ℝ) ∧
          ¬ ∃ A B : Finset ℕ,
            A ⊆ Finset.Icc 1 n ∧
            B ⊆ Finset.Icc 1 n ∧
            ⌈(3 + γ) * log (n : ℝ) / log (1 / δ)⌉₊ ≤ #A ∧
            ⌈(3 + γ) * log (n : ℝ) / log (1 / δ)⌉₊ ≤ #B ∧
            A + B ⊆ S := by
  filter_upwards [eventually_pairEvent_probability_le hγ_pos hγ_le hc_pos hc_lt,
    eventually_pairEvent_bound_lt_quarter (α := denseSubsetDensityExponent γ c) hγ_pos hc_pos
      hc_lt,
    eventually_ge_atTop 9] with n hmain hquarter hn δ hδ_lower hδ_upper
  refine exists_dense_set_of_pair_probability_lt_quarter ?_
    ((hmain δ hδ_lower hδ_upper).trans_lt (hquarter δ hδ_lower hδ_upper))
  exact (three_le_rpow_neg_mul hn (min_le_left _ _)).trans
    (mul_le_mul_of_nonneg_right hδ_lower.le (Nat.cast_nonneg n))

/-- Theorem 1.1. Let `δ n` be densities with `n ^ (-α) < δ n ≤ 1 - c` for all large `n`, where
`α = denseSubsetDensityExponent γ c`. For all large `n` there is `S ⊆ [n]` with `|S| ≥ δ n * n`
that contains no sumset `A + B` with `A, B ⊆ [n]` and
`|A|, |B| ≥ ⌈(3 + γ) * log n / log (1 / δ n)⌉`. -/
theorem dense_subset_without_large_sumsets {γ c : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1)
    (hc_pos : 0 < c) (hc_lt : c < 1) (δ : ℕ → unitInterval)
    (hδ_lower : ∀ᶠ n : ℕ in atTop,
      Real.rpow (n : ℝ) (-denseSubsetDensityExponent γ c) < (δ n : ℝ))
    (hδ_upper : ∀ᶠ n : ℕ in atTop, (δ n : ℝ) ≤ 1 - c) :
    ∀ᶠ n : ℕ in atTop,
      ∃ S : Finset ℕ,
        S ⊆ Finset.Icc 1 n ∧
        (δ n : ℝ) * (n : ℝ) ≤ (#S : ℝ) ∧
        ¬ ∃ A B : Finset ℕ,
          A ⊆ Finset.Icc 1 n ∧
          B ⊆ Finset.Icc 1 n ∧
          ⌈(3 + γ) * log (n : ℝ) / log (1 / δ n)⌉₊ ≤ #A ∧
          ⌈(3 + γ) * log (n : ℝ) / log (1 / δ n)⌉₊ ≤ #B ∧
          A + B ⊆ S := by
  filter_upwards [eventually_forall_exists_dense_subset_without_large_sumsets hγ_pos hγ_le hc_pos
    hc_lt, hδ_lower, hδ_upper] with n hmain h₁ h₂ using hmain (δ n) h₁ h₂

/-- **Theorem 1.1.** For `0 < γ ≤ 1` and `0 < c < 1` there is `α > 0` such that, for all large `n`
and every `n ^ (-α) < δ ≤ 1 - c`, some `S ⊆ [n]` with `|S| ≥ δ n` contains no sumset `A + B` with
`A, B ⊆ [n]` and `|A|, |B| ≥ (3 + γ) * log n / log (1 / δ)`. -/
theorem exists_dense_subset_forall_add_not_subset {γ c : ℝ} (hγ : 0 < γ) (hγ' : γ ≤ 1)
    (hc : 0 < c) (hc' : c < 1) :
    ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop, ∀ δ : ℝ, (n : ℝ) ^ (-α) < δ → δ ≤ 1 - c →
      ∃ S ⊆ Finset.Icc 1 n, δ * n ≤ #S ∧ ∀ A ⊆ Finset.Icc 1 n, ∀ B ⊆ Finset.Icc 1 n,
        ⌈(3 + γ) * log n / log (1 / δ)⌉₊ ≤ #A → ⌈(3 + γ) * log n / log (1 / δ)⌉₊ ≤ #B →
          ¬ A + B ⊆ S := by
  refine ⟨denseSubsetDensityExponent γ c, denseSubsetDensityExponent_pos hγ hc hc', ?_⟩
  filter_upwards [eventually_forall_exists_dense_subset_without_large_sumsets hγ hγ' hc hc']
    with n hn δ hδ hδ'
  obtain ⟨S, hS, hcard, hfree⟩ :=
    hn ⟨δ, (rpow_nonneg n.cast_nonneg _).trans hδ.le, by linarith⟩ hδ hδ'
  exact ⟨S, hS, hcard, fun A hA B hB hA' hB' hAB ↦ hfree ⟨A, B, hA, hB, hA', hB', hAB⟩⟩

end

end DenseSetsWithoutLargeSumsets
