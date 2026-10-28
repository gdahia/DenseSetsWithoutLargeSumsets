/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Order.Interval.Set.Nat

public import DenseSetsWithoutLargeSumsets.Common
public import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Probability.Distributions.Binomial
import Mathlib.RingTheory.Polynomial.Bernstein

/-!
# The binomial random subset

For a set `Ω` and `p ∈ [0, 1]`, the `p`-random subset of `Ω` contains each element of `Ω`
independently with probability `p`. This file defines its distribution as a measure on finsets,
computes the probability that it contains, or is equal to, a given finite set, and proves that the
`δ`-random subset of `[n]` has at least `δ n` elements with probability at least `1 / 4` when
`δ n ≥ 3`.

The last statement is a bound for the binomial distribution: if `X` is binomial with parameters
`n` and `p`, and `p n ≥ 3`, then `X ≥ p n` with probability at least `1 / 4`. For `p ≤ 1 / 2` and
`r = ⌊p n⌋`, the mass of `X` at `r - 1 - j` is at most its mass at `r + j`, so `X ≥ r` with
probability at least `1 / 2`, and the mass at `r` is at most the sum of the masses at `r + 1` and
`r + 2`. For `p > 1 / 2` we pass to `n - X`, which is binomial with parameters `n` and `q = 1 - p`.
The probability that it is less than `s` is a polynomial in `q` that is decreasing on `[0, 1]`.
This reduces the bound to the parameter `s / n` when `2 s ≤ n`, and to the parameter `1 / 2`
otherwise. The bound at `s / n` follows from the one for `n = 2 s` by induction on `n`, and the
bounds at `1 / 2` follow from the case `p ≤ 1 / 2`.

## Main definitions

* `binomialFinsetSubset Ω p`: the distribution of the `p`-random subset of `Ω`.

## Main statements

* `binomialFinsetSubset_real_eq_image`: for finite `Ω`, the `p`-random subset of `Ω` lies in a
  family of finsets with the same probability as a random set with distribution
  `setBernoulli Ω p` lies in its image.
* `setBernoulli_real_superset`: a random set with distribution `setBernoulli Ω p` contains a given
  finite set `T ⊆ Ω` with probability `p ^ |T|`.
* `binomialFinsetSubset_real_superset_nat`: the `p`-random subset of a finite set `Ω ⊆ ℕ` contains
  a given finite set `T` with probability at most `p ^ |T|`.
* `binomialFinsetSubset_real_singleton_nat_of_subset`: the `p`-random subset of a finite set
  `Ω ⊆ ℕ` is equal to a given `T ⊆ Ω` with probability `p ^ |T| * (1 - p) ^ (|Ω| - |T|)`.
* `binomialFinsetSubset_real_dense_event_ge_quarter`: if `δ n ≥ 3`, then the `δ`-random subset of
  `[n]` has at least `δ n` elements with probability at least `1 / 4`.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace DenseSetsWithoutLargeSumsets

open MeasureTheory ProbabilityTheory Finset

noncomputable section

/-- The distribution of the `p`-random subset of `Ω`, as a measure on finsets. It is the image of
`ProbabilityTheory.setBernoulli Ω p` under the map that sends a finite set to itself and an
infinite set to `∅`. -/
noncomputable def binomialFinsetSubset {α : Type*} (Ω : Set α) (p : unitInterval) :
    Measure (Finset α) := by
  classical
  exact (ProbabilityTheory.setBernoulli Ω p).map fun S ↦
    if hS : S.Finite then hS.toFinset else ∅

instance instIsFiniteMeasureBinomialFinsetSubset {α : Type*} (Ω : Set α) (p : unitInterval) :
    IsFiniteMeasure (binomialFinsetSubset Ω p) := by
  classical
  rw [binomialFinsetSubset]
  infer_instance

/-- A random set with distribution `setBernoulli Ω p` contains a given finite set `T ⊆ Ω` with
probability `p ^ |T|`. -/
lemma setBernoulli_real_superset {α : Type*} [Countable α]
    {Ω T : Set α} (p : unitInterval) (hTΩ : T ⊆ Ω) (hT : T.Finite) :
    (ProbabilityTheory.setBernoulli Ω p).real {S : Set α | T ⊆ S} = (p : ℝ) ^ T.ncard := by
  lift T to Finset α using hT
  have hmem (i : T) : (i : α) ∈ Ω := hTΩ i.2
  have hcyl : (fun q : α → Prop ↦ {i | q i}) ⁻¹' {S | ↑T ⊆ S} =
      cylinder T ({fun _ ↦ True} : Set (T → Prop)) := by
    ext q
    simp [mem_cylinder, Set.subset_def, funext_iff]
  rw [measureReal_def, setBernoulli_apply', hcyl, Measure.infinitePi_cylinder _ (by simp),
    Measure.pi_singleton]
  simp [bernoulliMeasure_def, hmem]

open scoped Classical in
private lemma measurable_dite_toFinset {α : Type*} [Countable α] :
    Measurable fun S : Set α ↦ if hS : S.Finite then hS.toFinset else ∅ := by
  have h : (fun S : Set α ↦ ((if hS : S.Finite then hS.toFinset else ∅ : Finset α) : Set α)) =
      fun S ↦ if S.Finite then S else ∅ := by
    ext S : 1
    split <;> simp
  rw [measurable_finset_iff_measurable_set, h]
  exact .ite .setOfPred_finite measurable_id measurable_const

/-- For finite `Ω`, the `p`-random subset of `Ω` lies in a family `A` of finsets with the same
probability as a random set with distribution `setBernoulli Ω p` lies in `A`. -/
lemma binomialFinsetSubset_real_eq_image {Ω : Set ℕ} (hΩ : Ω.Finite) (p : unitInterval)
    (A : Set (Finset ℕ)) :
    (binomialFinsetSubset Ω p).real A = (setBernoulli Ω p).real ((↑) '' A) := by
  rw [binomialFinsetSubset, map_measureReal_apply measurable_dite_toFinset
    A.to_countable.measurableSet]
  apply measureReal_congr
  filter_upwards [setBernoulli_ae_subset] with S hS
  have hfin := hΩ.subset hS
  refine propext ⟨fun h ↦ ⟨hfin.toFinset, by simpa [hfin] using h, hfin.coe_toFinset⟩, ?_⟩
  rintro ⟨T, hT, rfl⟩
  simpa using hT

/-- The `p`-random subset of a finite set `Ω ⊆ ℕ` contains a given finite set `T` with probability
at most `p ^ |T|`. -/
lemma binomialFinsetSubset_real_superset_nat
    {Ω : Set ℕ} (p : unitInterval) (hΩ : Ω.Finite) {T : Finset ℕ} :
    (binomialFinsetSubset Ω p).real {S : Finset ℕ | T ⊆ S} ≤ (p : ℝ) ^ #T := by
  rw [binomialFinsetSubset_real_eq_image hΩ]
  by_cases hTΩ : (T : Set ℕ) ⊆ Ω
  · rw [← Set.ncard_coe_finset, ← setBernoulli_real_superset p hTΩ T.finite_toSet]
    refine measureReal_mono ?_
    rintro _ ⟨S, hS, rfl⟩
    simpa using hS
  · refine (le_of_eq ?_).trans (pow_nonneg (unitInterval.nonneg p) _)
    rw [measureReal_eq_zero_iff, measure_eq_zero_iff_ae_notMem]
    filter_upwards [setBernoulli_ae_subset] with S hSΩ
    rintro ⟨S', hS', rfl⟩
    exact hTΩ ((coe_subset.2 hS').trans hSΩ)

/-- The `p`-random subset of a finite set `Ω ⊆ ℕ` is equal to a given `T ⊆ Ω` with probability
`p ^ |T| * (1 - p) ^ (|Ω| - |T|)`. -/
lemma binomialFinsetSubset_real_singleton_nat_of_subset
    {Ω : Set ℕ} (p : unitInterval) (hΩ : Ω.Finite) {T : Finset ℕ}
    (hTΩ : (T : Set ℕ) ⊆ Ω) :
    (binomialFinsetSubset Ω p).real ({T} : Set (Finset ℕ)) =
      (p : ℝ) ^ #T * (1 - (p : ℝ)) ^ (Ω.ncard - #T) := by
  rw [binomialFinsetSubset_real_eq_image hΩ, Set.image_singleton,
    setBernoulli_real_singleton p hTΩ hΩ, Set.ncard_sdiff' hTΩ hΩ, Set.ncard_coe_finset]

open Polynomial

/-! ### The binomial masses and the lower tail polynomial -/

/-- The probability `C(n, k) * p ^ k * (1 - p) ^ (n - k)` that a binomial variable with parameters
`n` and `p` is equal to `k`. -/
private def binomialMass (n k : ℕ) (p : unitInterval) : ℝ :=
  (n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)

private lemma binomialMass_nonneg (n k : ℕ) (p : unitInterval) : 0 ≤ binomialMass n k p :=
  binomial_nonneg

/-- The probability that a binomial variable with parameters `n` and `p` is at least `m`. -/
private def binomialUpperTail (n m : ℕ) (p : unitInterval) : ℝ :=
  ∑ k ∈ Icc m n, binomialMass n k p

private lemma binomialUpperTail_anti (n : ℕ) (p : unitInterval) {m m' : ℕ} (h : m ≤ m') :
    binomialUpperTail n m' p ≤ binomialUpperTail n m p :=
  sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_left h) fun _ _ _ ↦ binomialMass_nonneg ..

private lemma binomialUpperTail_eq_add (n : ℕ) (p : unitInterval) {m : ℕ} (hm : m ≤ n) :
    binomialUpperTail n m p = binomialMass n m p + binomialUpperTail n (m + 1) p := by
  unfold binomialUpperTail
  rw [← insert_Icc_add_one_left_eq_Icc hm, sum_insert (by simp)]

private lemma sum_binomialMass (n : ℕ) (p : unitInterval) :
    ∑ k ∈ range (n + 1), binomialMass n k p = 1 := by
  simpa [binomialMass, mul_comm, mul_left_comm, mul_assoc] using
    (add_pow (p : ℝ) (1 - (p : ℝ)) n).symm

private lemma sum_range_add_binomialUpperTail (n : ℕ) (p : unitInterval) {m : ℕ}
    (hm : m ≤ n + 1) : ∑ k ∈ range m, binomialMass n k p + binomialUpperTail n m p = 1 := by
  rw [binomialUpperTail, ← Ico_add_one_right_eq_Icc, sum_range_add_sum_Ico _ hm, sum_binomialMass]

/-- The polynomial `∑ k < s, C(n, k) * X ^ k * (1 - X) ^ (n - k)`. Its value at `p` is the
probability that a binomial variable with parameters `n` and `p` is less than `s`. -/
private def binomialLowerPolynomial (n s : ℕ) : ℝ[X] :=
  ∑ k ∈ range s, bernsteinPolynomial ℝ n k

private lemma binomialLowerPolynomial_succ (n s : ℕ) :
    binomialLowerPolynomial n (s + 1) =
      binomialLowerPolynomial n s + bernsteinPolynomial ℝ n s :=
  sum_range_succ _ s

private lemma eval_binomialLowerPolynomial (n s : ℕ) (x : ℝ) :
    (binomialLowerPolynomial n s).eval x =
      ∑ k ∈ range s, (n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k) := by
  simp [binomialLowerPolynomial, eval_finsetSum, bernsteinPolynomial]

private lemma derivative_binomialLowerPolynomial (n s : ℕ) (hs : 0 < s) :
    (binomialLowerPolynomial n s).derivative =
      -(n : ℝ[X]) * bernsteinPolynomial ℝ (n - 1) (s - 1) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_one.2 hs
  clear hs
  rw [Nat.add_sub_cancel]
  induction s with
  | zero => simp [binomialLowerPolynomial, bernsteinPolynomial.derivative_zero]
  | succ s ih =>
    rw [binomialLowerPolynomial_succ, map_add, ih, bernsteinPolynomial.derivative_succ]
    ring

/-- The function `x ^ (s - 1) * (1 - x) ^ (n - s)`. Up to a constant factor it is the derivative
of `binomialLowerPolynomial n s`. -/
private def boundaryKernel (n s : ℕ) (x : ℝ) : ℝ :=
  x ^ (s - 1) * (1 - x) ^ (n - s)

private lemma deriv_eval_binomialLowerPolynomial (n s : ℕ) (hs : 0 < s) (x : ℝ) :
    deriv (fun y : ℝ ↦ (binomialLowerPolynomial n s).eval y) x =
      -(n : ℝ) * ((n - 1).choose (s - 1) : ℝ) * boundaryKernel n s x := by
  rw [Polynomial.deriv, derivative_binomialLowerPolynomial n s hs]
  simp only [bernsteinPolynomial, neg_mul, eval_neg, eval_mul, eval_natCast, eval_pow, eval_X,
    eval_sub, eval_one, boundaryKernel, neg_inj]
  rw [Nat.sub_sub_sub_cancel_right hs]
  ring

private lemma antitoneOn_eval_binomialLowerPolynomial (n s : ℕ) (hs : 0 < s) :
    AntitoneOn (fun x : ℝ ↦ (binomialLowerPolynomial n s).eval x) (Set.Icc 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (by fun_prop) (by fun_prop)
  intro x hx
  obtain ⟨hx0, hx1⟩ := interior_subset hx
  rw [deriv_eval_binomialLowerPolynomial n s hs, neg_mul, neg_mul, neg_nonpos, boundaryKernel]
  have := sub_nonneg.2 hx1
  positivity

/-! ### Increasing the number of trials at the parameter `s / n` -/

/-- An instance of the weighted inequality between the arithmetic and the geometric mean, with
weights `s / (s + d)` and `d / (s + d)`. -/
private lemma centered_step_factor_ge_one (s d : ℕ) (hs : 0 < s) (hd : 0 < d) :
    (1 : ℝ) ≤ (((s : ℝ) + d + 1) / (s + d)) ^ s *
      (d * (s + d + 1) / ((s + d) * (d + 1))) ^ d := by
  have hn : (0 : ℝ) < s + d := by positivity
  have hA : (0 : ℝ) < (s + d + 1) / (s + d) := by positivity
  have hB : (0 : ℝ) < d * (s + d + 1) / ((s + d) * (d + 1)) := by positivity
  have hamgm := Real.geom_mean_le_arith_mean2_weighted (w₁ := s / (s + d)) (w₂ := d / (s + d))
    (by positivity) (by positivity) (inv_nonneg.2 hA.le) (inv_nonneg.2 hB.le) (by field_simp)
  have harith : (s : ℝ) / (s + d) * (((s : ℝ) + d + 1) / (s + d))⁻¹ +
      (d : ℝ) / (s + d) * ((d : ℝ) * (s + d + 1) / ((s + d) * (d + 1)))⁻¹ = 1 := by
    field_simp
    ring
  rw [harith, Real.inv_rpow hA.le, Real.inv_rpow hB.le, ← mul_inv,
    inv_le_one₀ (by positivity)] at hamgm
  have hpow := Real.one_le_rpow hamgm hn.le
  rwa [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hA.le,
    ← Real.rpow_mul hB.le, div_mul_cancel₀ _ hn.ne', div_mul_cancel₀ _ hn.ne',
    Real.rpow_natCast, Real.rpow_natCast] at hpow

private lemma cast_choose_pred_mul (s d : ℕ) (hs : 0 < s) :
    ((s + d).choose (s - 1) : ℝ) * (d + 1) = (s + d - 1).choose (s - 1) * (s + d) := by
  have h := Nat.choose_mul_succ_eq (s + d - 1) (s - 1)
  rw [Nat.sub_add_cancel (by grind), (by grind : s + d - (s - 1) = d + 1)] at h
  exact_mod_cast h.symm

/-- With `n = s + d`, `a = s / (n + 1)` and `b = s / n`, the product
`C(n, s - 1) * a ^ s * (1 - a) ^ (d + 1)` is at most
`n * C(n - 1, s - 1) * b ^ (s - 1) * (1 - b) ^ d * (b - a)`. -/
private lemma centered_boundary_cost_le (s d : ℕ) (hs : 0 < s) (hd : 0 < d) :
    ((s + d).choose (s - 1) : ℝ) * ((s : ℝ) / (s + d + 1)) ^ s *
        (1 - (s : ℝ) / (s + d + 1)) ^ (d + 1) ≤
      (s + d : ℝ) * ((s + d - 1).choose (s - 1) : ℝ) * ((s : ℝ) / (s + d)) ^ (s - 1) *
        (1 - (s : ℝ) / (s + d)) ^ d * ((s : ℝ) / (s + d) - (s : ℝ) / (s + d + 1)) := by
  have hchoose := cast_choose_pred_mul s d hs
  have h₁ : 1 - (s : ℝ) / (s + d + 1) = (d + 1) / (s + d + 1) := by
    field_simp
    ring
  have h₂ : 1 - (s : ℝ) / (s + d) = d / (s + d) := by
    field_simp
    ring
  have h₃ : (s : ℝ) / (s + d) - s / (s + d + 1) = s / ((s + d) * (s + d + 1)) := by
    field_simp
    ring
  rw [← eq_div_iff (by positivity)] at hchoose
  rw [h₁, h₂, h₃, hchoose]
  refine (le_mul_of_one_le_right (by positivity) (centered_step_factor_ge_one s d hs hd)).trans_eq
    ?_
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_one.2 hs
  simp only [Nat.add_sub_cancel, div_pow, mul_pow]
  push_cast
  field_simp
  ring

private lemma bernsteinPolynomial_degree_succ (n k : ℕ) (hk : k ≤ n) :
    bernsteinPolynomial ℝ (n + 1) (k + 1) =
      (1 - X) * bernsteinPolynomial ℝ n (k + 1) + X * bernsteinPolynomial ℝ n k := by
  simp only [bernsteinPolynomial, Nat.choose_succ_succ', Nat.succ_sub_succ_eq_sub]
  obtain rfl | hkn := hk.eq_or_lt
  · simp [pow_succ, mul_comm]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hkn
    rw [(by grind : k + m + 1 - k = m + 1), (by grind : k + m + 1 - (k + 1) = m)]
    push_cast
    ring

private lemma binomialLowerPolynomial_degree_succ (n s : ℕ) (hs : 0 < s) (hsn : s ≤ n + 1) :
    binomialLowerPolynomial (n + 1) s =
      binomialLowerPolynomial n s - X * bernsteinPolynomial ℝ n (s - 1) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_one.2 hs
  clear hs
  rw [Nat.add_sub_cancel]
  induction s with
  | zero =>
    simp [binomialLowerPolynomial, bernsteinPolynomial, pow_succ]
    ring
  | succ s ih =>
    rw [binomialLowerPolynomial_succ (n + 1) (s + 1), ih (by grind),
      bernsteinPolynomial_degree_succ n s (by grind), binomialLowerPolynomial_succ n (s + 1)]
    ring

private lemma eval_binomialLowerPolynomial_degree_succ (n s : ℕ) (hs : 0 < s) (hsn : s ≤ n)
    (a : ℝ) :
    (binomialLowerPolynomial (n + 1) s).eval a =
      (binomialLowerPolynomial n s).eval a - n.choose (s - 1) * a ^ s * (1 - a) ^ (n - s + 1) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_one.2 hs
  rw [binomialLowerPolynomial_degree_succ n _ hs (by grind), Nat.add_sub_cancel,
    (by grind : n - (s + 1) + 1 = n - s)]
  simp only [bernsteinPolynomial, eval_sub, eval_mul, eval_X, eval_natCast, eval_pow, eval_one]
  ring

private lemma hasDerivAt_boundaryKernel (n s : ℕ) (x : ℝ) :
    HasDerivAt (boundaryKernel n s)
      ((s - 1 : ℕ) * x ^ (s - 1 - 1) * (1 - x) ^ (n - s) -
        x ^ (s - 1) * ((n - s : ℕ) * (1 - x) ^ (n - s - 1))) x := by
  unfold boundaryKernel
  refine (((hasDerivAt_id x).pow (s - 1)).mul
    (((hasDerivAt_id x).const_sub 1).pow (n - s))).congr_deriv ?_
  simp
  ring

private lemma antitoneOn_boundaryKernel (n s : ℕ) (hs : 0 < s) (hns : 2 * s ≤ n) :
    AntitoneOn (boundaryKernel n s) (Set.Icc ((s : ℝ) / (n + 1)) ((s : ℝ) / n)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · unfold boundaryKernel
    fun_prop
  · unfold boundaryKernel
    fun_prop
  · intro x hx
    obtain ⟨hxa, hxb⟩ := interior_subset hx
    have hn : (0 : ℝ) < n := mod_cast (by grind : 0 < n)
    have h2s : (2 : ℝ) * s ≤ n := mod_cast hns
    have hx0 : 0 ≤ x := le_trans (by positivity) hxa
    have hxhalf : x ≤ 1 / 2 := hxb.trans ((div_le_iff₀ hn).2 (by linarith))
    have hx1 : 0 ≤ 1 - x := by linarith
    have hxn := (div_le_iff₀ (by positivity)).1 hxa
    rw [(hasDerivAt_boundaryKernel n s x).deriv]
    obtain rfl | hs2 : s = 1 ∨ 2 ≤ s := by grind
    · rw [Nat.sub_self, Nat.cast_zero, zero_mul, zero_mul, zero_sub, neg_nonpos]
      positivity
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le' hs2
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt (by grind : t + 2 < n)
      rw [(by grind : t + 2 + m + 1 - (t + 2) = m + 1), (by grind : t + 2 - 1 = t + 1)]
      simp only [Nat.add_sub_cancel]
      push_cast at hxn ⊢
      linear_combination x ^ t * (1 - x) ^ m *
        (by linarith : ((t : ℝ) + 1) * (1 - x) - (m + 1) * x ≤ 0)

private lemma deriv_eval_binomialLowerPolynomial_le (n s : ℕ) (hs : 0 < s) (hns : 2 * s ≤ n)
    {x : ℝ} (hx : x ∈ Set.Icc ((s : ℝ) / (n + 1)) ((s : ℝ) / n)) :
    deriv (fun y : ℝ ↦ (binomialLowerPolynomial n s).eval y) x ≤
      -(n : ℝ) * ((n - 1).choose (s - 1) : ℝ) * boundaryKernel n s (s / n) := by
  obtain ⟨hxa, hxb⟩ := hx
  rw [deriv_eval_binomialLowerPolynomial n s hs]
  linarith [mul_le_mul_of_nonneg_left
    (antitoneOn_boundaryKernel n s hs hns ⟨hxa, hxb⟩ ⟨hxa.trans hxb, le_rfl⟩ hxb)
    (by positivity : (0 : ℝ) ≤ n * (n - 1).choose (s - 1))]

/-- For `0 < s ≤ d`, the probability that a binomial variable with parameters `n` and `s / n` is
less than `s` does not decrease from `n = s + d` to `n = s + d + 1`. -/
private lemma centered_binomialLowerPolynomial_step (s d : ℕ) (hs : 0 < s) (hsd : s ≤ d) :
    (binomialLowerPolynomial (s + d) s).eval ((s : ℝ) / (s + d : ℕ)) ≤
      (binomialLowerPolynomial (s + d + 1) s).eval ((s : ℝ) / (s + d + 1 : ℕ)) := by
  have hab : (s : ℝ) / ((s + d : ℕ) + 1) ≤ s / (s + d : ℕ) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hsec := (convex_Icc _ _).image_sub_le_mul_sub_of_deriv_le
    (f := fun x ↦ (binomialLowerPolynomial (s + d) s).eval x) (by fun_prop) (by fun_prop)
    (fun x hx ↦ deriv_eval_binomialLowerPolynomial_le (s + d) s hs (by grind)
      (interior_subset hx)) _ ⟨le_rfl, hab⟩ _ ⟨hab, le_rfl⟩ hab
  rw [boundaryKernel, Nat.add_sub_cancel_left] at hsec
  rw [eval_binomialLowerPolynomial_degree_succ (s + d) s hs (by grind), Nat.add_sub_cancel_left]
  push_cast at hsec ⊢
  linarith [centered_boundary_cost_le s d hs (hs.trans_le hsd)]

/-! ### The upper tail for `p ≤ 1 / 2` -/

/-- The recurrence between consecutive binomial masses. -/
private lemma binomialMass_mul_succ (n k : ℕ) (p : unitInterval) (hk : k < n) :
    binomialMass n k p * (n - k : ℕ) * (p : ℝ) =
      binomialMass n (k + 1) p * (k + 1 : ℕ) * (1 - (p : ℝ)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hk
  have hchoose : ((k + m + 1).choose (k + 1) : ℝ) * (k + 1 : ℕ) =
      (k + m + 1).choose k * (k + m + 1 - k : ℕ) :=
    mod_cast Nat.choose_succ_right_eq (k + m + 1) k
  rw [(by grind : k + m + 1 - k = m + 1)] at hchoose
  rw [binomialMass, binomialMass, (by grind : k + m + 1 - k = m + 1),
    (by grind : k + m + 1 - (k + 1) = m)]
  linear_combination -((p : ℝ) ^ (k + 1) * (1 - (p : ℝ)) ^ (m + 1)) * hchoose

private lemma mul_binomialMass_le_succ (n k : ℕ) (p : unitInterval) (hk : k < n)
    (hp : (p : ℝ) < 1) {c : ℝ} (hc : c * (1 - (p : ℝ)) ≤ (n - k : ℕ) * (p : ℝ)) :
    c * binomialMass n k p ≤ (k + 1) * binomialMass n (k + 1) p := by
  have h := binomialMass_mul_succ n k p hk
  push_cast at h
  refine le_of_mul_le_mul_right ?_ (sub_pos.2 hp)
  linear_combination h + mul_le_mul_of_nonneg_left hc (binomialMass_nonneg n k p)

private lemma le_of_paired_recurrences {x y z w a b c d P Q : ℝ}
    (hx : x * a * P = y * b * Q) (hz : z * c * P = w * d * Q) (hyz : y ≤ z) (hz0 : 0 ≤ z)
    (hb : 0 ≤ b * Q) (ha : 0 < a * P) (hd : 0 < d * Q)
    (hcross : b * Q * (d * Q) ≤ a * P * (c * P)) : x ≤ w := by
  refine le_of_mul_le_mul_right ?_ (mul_pos ha hd)
  linear_combination d * Q * hx + a * P * hz +
    mul_le_mul_of_nonneg_right hyz (mul_nonneg hb hd.le) + mul_le_mul_of_nonneg_left hcross hz0

private lemma paired_binomial_factor_inequality {N R J x : ℝ} (hR : 0 < R) (hJ0 : 0 ≤ J)
    (hJ : J < R) (hNR : R ≤ N) (hx1 : x ≤ 1) (hratio : R * (1 - x) ≤ N * x) :
    (R - J) * (1 - x) * ((R + J) * (1 - x)) ≤ (N + J + 1) * x * ((N - J + 1) * x) := by
  have hcoef : N ^ 2 * ((R - J) * (R + J)) ≤ R ^ 2 * ((N + J + 1) * (N - J + 1)) := by
    linarith [mul_nonneg (sq_nonneg R) (by linarith : 0 ≤ 2 * N + 1),
      mul_nonneg (sq_nonneg J) (sub_nonneg.2 (pow_le_pow_left₀ hR.le hNR 2))]
  refine le_of_mul_le_mul_left ?_ (pow_pos hR 2)
  linear_combination
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hR.le (sub_nonneg.2 hx1)) hratio 2)
      (mul_nonneg (sub_nonneg.2 hJ.le) (add_nonneg hR.le hJ0)) +
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg x)

/-- Reflection of the binomial masses about `r`: if `2 * r ≤ n`, `r ≤ p * n` and `p ≤ 1 / 2`, then
the mass at `r - 1 - j` is at most the mass at `r + j`. -/
private lemma binomialMass_reflection (n r : ℕ) (p : unitInterval) (h2r : 2 * r ≤ n)
    (hmean : (r : ℝ) ≤ (p : ℝ) * (n : ℝ)) (hp_half : (p : ℝ) ≤ 1 / 2) (j : ℕ) (hjr : j < r) :
    binomialMass n (r - 1 - j) p ≤ binomialMass n (r + j) p := by
  have hr0 : (0 : ℝ) < r := mod_cast (by grind : 0 < r)
  have hp0 : 0 < (p : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hq0 : 0 < 1 - (p : ℝ) := by linarith
  have hratio : (r : ℝ) * (1 - (p : ℝ)) ≤ ((n - r : ℕ) : ℝ) * (p : ℝ) := by
    rw [Nat.cast_sub (by grind)]
    linarith
  induction j with
  | zero =>
    have hc : (r : ℝ) * (1 - (p : ℝ)) ≤ ((n - (r - 1) : ℕ) : ℝ) * (p : ℝ) := by
      rw [Nat.cast_sub (by grind), Nat.cast_pred hjr]
      linarith
    have h := mul_binomialMass_le_succ n (r - 1) p (by grind) (by linarith) hc
    rw [Nat.sub_add_cancel (by grind : 1 ≤ r), Nat.cast_pred hjr, sub_add_cancel] at h
    exact le_of_mul_le_mul_left h hr0
  | succ j ih =>
    have hl := binomialMass_mul_succ n (r - 1 - (j + 1)) p (by grind)
    rw [(by grind : r - 1 - (j + 1) + 1 = r - 1 - j)] at hl
    refine le_of_paired_recurrences hl (binomialMass_mul_succ n (r + j) p (by grind))
      (ih (by grind)) (binomialMass_nonneg ..) (by positivity) ?_ (by positivity) ?_
    · exact mul_pos (Nat.cast_pos.2 (by grind)) hp0
    · rw [(by grind : n - (r - 1 - (j + 1)) = n - r + (j + 1) + 1),
        (by grind : n - (r + j) = n - r - (j + 1) + 1), (by grind : r - 1 - j = r - (j + 1))]
      push_cast [Nat.cast_sub (by grind : j + 1 ≤ n - r), Nat.cast_sub (by grind : j + 1 ≤ r)]
      linear_combination paired_binomial_factor_inequality (N := (n - r : ℕ)) (R := r)
        (J := j + 1) (x := p) hr0 (by positivity) (mod_cast hjr)
        (mod_cast (by grind : r ≤ n - r)) (unitInterval.le_one p) hratio

/-- If `2 * r ≤ n`, `r ≤ p * n` and `p ≤ 1 / 2`, then a binomial variable with parameters `n` and
`p` is at least `r` with probability at least `1 / 2`. -/
private lemma one_half_le_binomialUpperTail_of_le_half (n r : ℕ) (p : unitInterval)
    (h2r : 2 * r ≤ n) (hmean : (r : ℝ) ≤ (p : ℝ) * (n : ℝ)) (hp_half : (p : ℝ) ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ binomialUpperTail n r p := by
  have hlower : ∑ k ∈ range r, binomialMass n k p ≤ binomialUpperTail n r p := by
    rw [← sum_range_reflect, binomialUpperTail]
    refine (sum_le_sum fun j hj ↦
      binomialMass_reflection n r p h2r hmean hp_half j (mem_range.1 hj)).trans ?_
    rw [range_eq_Ico, sum_Ico_add (fun k ↦ binomialMass n k p) 0 r r]
    gcongr
    · intros
      apply binomialMass_nonneg
    · grind
  linarith [sum_range_add_binomialUpperTail n p (by grind : r ≤ n + 1)]

private lemma binomialMass_le_next_add_next (n r : ℕ) (p : unitInterval) (hr : 3 ≤ r)
    (h2r : 2 * r ≤ n) (hmean : (r : ℝ) ≤ (p : ℝ) * (n : ℝ)) (hp_half : (p : ℝ) ≤ 1 / 2) :
    binomialMass n r p ≤ binomialMass n (r + 1) p + binomialMass n (r + 2) p := by
  have hr3 : (3 : ℝ) ≤ r := mod_cast hr
  have h₁ : (r : ℝ) * binomialMass n r p ≤ (r + 1) * binomialMass n (r + 1) p := by
    apply mul_binomialMass_le_succ n r p (by grind) (by linarith)
    rw [Nat.cast_sub (by grind)]
    linarith
  have h₂ : ((r : ℝ) - 1) * binomialMass n (r + 1) p ≤ (r + 2) * binomialMass n (r + 2) p := by
    refine (mul_binomialMass_le_succ n (r + 1) p (by grind) (by linarith) ?_).trans_eq ?_
    · rw [Nat.cast_sub (by grind)]
      push_cast
      linarith
    · push_cast
      ring
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < (r + 1) * (r + 2))
  linear_combination (2 * (r : ℝ) + 1) * h₁ + ((r : ℝ) + 1) * h₂ +
    mul_nonneg (binomialMass_nonneg n r p) (by nlinarith : (0 : ℝ) ≤ r ^ 2 - 2 * r - 2)

/-- If `3 ≤ r`, `2 * r ≤ n`, `r ≤ p * n` and `p ≤ 1 / 2`, then a binomial variable with parameters
`n` and `p` is greater than `r` with probability at least `1 / 4`. -/
private lemma one_fourth_le_binomialUpperTail_succ_of_le_half (n r : ℕ) (p : unitInterval)
    (hr : 3 ≤ r) (h2r : 2 * r ≤ n) (hmean : (r : ℝ) ≤ (p : ℝ) * (n : ℝ))
    (hp_half : (p : ℝ) ≤ 1 / 2) :
    (1 / 4 : ℝ) ≤ binomialUpperTail n (r + 1) p := by
  have hhalf := one_half_le_binomialUpperTail_of_le_half n r p h2r hmean hp_half
  have hnext : binomialMass n r p ≤ binomialUpperTail n (r + 1) p := by
    refine (binomialMass_le_next_add_next n r p hr h2r hmean hp_half).trans ?_
    rw [← sum_pair (f := fun k ↦ binomialMass n k p) (by grind : r + 1 ≠ r + 2),
      binomialUpperTail]
    gcongr
    · intros
      apply binomialMass_nonneg
    · grind
  rw [binomialUpperTail_eq_add n p (by grind : r ≤ n)] at hhalf
  linarith

/-- If `3 ≤ p * n` and `p ≤ 1 / 2`, then a binomial variable with parameters `n` and `p` is at
least `p * n` with probability at least `1 / 4`. -/
private lemma one_fourth_le_binomialUpperTail_of_three_le_mean_of_le_half (n : ℕ)
    (p : unitInterval) (hmean : (3 : ℝ) ≤ (p : ℝ) * (n : ℝ)) (hp_half : (p : ℝ) ≤ 1 / 2) :
    (1 / 4 : ℝ) ≤ binomialUpperTail n ⌈(p : ℝ) * (n : ℝ)⌉₊ p := by
  have hr := Nat.floor_le (mul_nonneg (unitInterval.nonneg p) n.cast_nonneg)
  have hpn := mul_le_mul_of_nonneg_right hp_half (Nat.cast_nonneg (α := ℝ) n)
  have h2r : 2 * ⌊(p : ℝ) * n⌋₊ ≤ n := mod_cast (by linarith : (2 : ℝ) * ⌊(p : ℝ) * n⌋₊ ≤ n)
  exact (one_fourth_le_binomialUpperTail_succ_of_le_half n _ p (Nat.le_floor (mod_cast hmean)) h2r
    hr hp_half).trans (binomialUpperTail_anti n p (Nat.ceil_le_floor_add_one _))

/-! ### The upper tail for `p > 1 / 2` -/

/-- The parameter `1 / 2`. -/
private def halfParameter : unitInterval :=
  ⟨1 / 2, by constructor <;> norm_num⟩

@[simp] private lemma halfParameter_coe : (halfParameter : ℝ) = 1 / 2 := rfl

/-- A binomial variable with parameters `n` and `1 - p` is less than `s` with the probability that
a binomial variable with parameters `n` and `p` is at least `n + 1 - s`. -/
private lemma eval_one_sub_binomialLowerPolynomial (n s : ℕ) (p : unitInterval)
    (hsn : s ≤ n + 1) :
    (binomialLowerPolynomial n s).eval (1 - (p : ℝ)) = binomialUpperTail n (n + 1 - s) p := by
  rw [eval_binomialLowerPolynomial, binomialUpperTail]
  refine sum_nbij' (n - ·) (n - ·) (by grind) (by grind) (by grind) (by grind) ?_
  intro k hk
  have hkn : k ≤ n := by grind
  simp only [binomialMass]
  rw [Nat.choose_symm hkn, Nat.sub_sub_self hkn, sub_sub_cancel]
  ring

private lemma eval_half_binomialLowerPolynomial (n s : ℕ) (hsn : s ≤ n + 1) :
    (binomialLowerPolynomial n s).eval (1 / 2) =
      binomialUpperTail n (n + 1 - s) halfParameter := by
  rw [← eval_one_sub_binomialLowerPolynomial n s halfParameter hsn, halfParameter_coe]
  norm_num

private lemma ceil_mul_add_floor_one_sub_mul (n : ℕ) (p : unitInterval) :
    ⌈(p : ℝ) * n⌉₊ + ⌊(1 - (p : ℝ)) * n⌋₊ = n := by
  have hceil : ⌈(p : ℝ) * n⌉₊ ≤ n :=
    Nat.ceil_le.2 (mul_le_of_le_one_left n.cast_nonneg (unitInterval.le_one p))
  have hfloor : ⌊(1 - (p : ℝ)) * n⌋₊ = n - ⌈(p : ℝ) * n⌉₊ := by
    rw [Nat.floor_eq_iff (mul_nonneg (unitInterval.one_sub_nonneg p) n.cast_nonneg),
      Nat.cast_sub hceil]
    constructor <;> linarith [Nat.le_ceil ((p : ℝ) * n),
      Nat.ceil_lt_add_one (mul_nonneg (unitInterval.nonneg p) n.cast_nonneg)]
  grind

private lemma one_fourth_le_eval_half_binomialLowerPolynomial_midpoint (n : ℕ) :
    (1 / 4 : ℝ) ≤ (binomialLowerPolynomial n (n / 2 + 1)).eval (1 / 2) := by
  have hmean : ((n / 2 : ℕ) : ℝ) ≤ (halfParameter : ℝ) * n := by
    rw [halfParameter_coe]
    linarith [(mod_cast Nat.mul_div_le n 2 : (2 : ℝ) * (n / 2 : ℕ) ≤ n)]
  rw [eval_half_binomialLowerPolynomial n (n / 2 + 1) (by grind)]
  obtain h | h : n + 1 - (n / 2 + 1) = n / 2 ∨ n + 1 - (n / 2 + 1) = n / 2 + 1 := by grind
  · rw [h]
    linarith [one_half_le_binomialUpperTail_of_le_half n (n / 2) halfParameter (by grind) hmean
      (by simp)]
  · by_cases hr : 3 ≤ n / 2
    · rw [h]
      exact one_fourth_le_binomialUpperTail_succ_of_le_half n (n / 2) halfParameter hr (by grind)
        hmean (by simp)
    · obtain ⟨r, rfl⟩ : ∃ r, n = 2 * r + 1 := ⟨n / 2, by grind⟩
      have hr2 : r ≤ 2 := by grind
      interval_cases r <;>
        norm_num [binomialUpperTail, binomialMass, halfParameter, sum_Icc_succ_top, Nat.choose]

private lemma one_fourth_le_centered_binomialLowerPolynomial_base (s : ℕ) (hs : 0 < s) :
    (1 / 4 : ℝ) ≤ (binomialLowerPolynomial (2 * s) s).eval (1 / 2) := by
  rw [eval_half_binomialLowerPolynomial (2 * s) s (by grind),
    (by grind : 2 * s + 1 - s = s + 1)]
  by_cases hs3 : 3 ≤ s
  · exact one_fourth_le_binomialUpperTail_succ_of_le_half (2 * s) s halfParameter hs3 le_rfl
      (by simp) (by simp)
  · interval_cases s <;>
      norm_num [binomialUpperTail, binomialMass, halfParameter, sum_Icc_succ_top]

/-- If `0 < s` and `2 * s ≤ n`, then a binomial variable with parameters `n` and `s / n` is less
than `s` with probability at least `1 / 4`. -/
private lemma one_fourth_le_centered_binomialLowerPolynomial (n s : ℕ) (hs : 0 < s)
    (h2s : 2 * s ≤ n) :
    (1 / 4 : ℝ) ≤ (binomialLowerPolynomial n s).eval ((s : ℝ) / n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (by grind : s ≤ n)
  have hsd : s ≤ d := by grind
  clear h2s
  induction d, hsd using Nat.le_induction with
  | base =>
    rw [← two_mul, Nat.cast_mul, Nat.cast_ofNat, (by field_simp : (s : ℝ) / (2 * s) = 1 / 2)]
    exact one_fourth_le_centered_binomialLowerPolynomial_base s hs
  | succ d hsd ih => exact ih.trans (centered_binomialLowerPolynomial_step s d hs hsd)

/-- If `q ≤ 1 / 2`, then a binomial variable with parameters `n` and `q` is at most `q * n` with
probability at least `1 / 4`. -/
private lemma one_fourth_le_binomialLowerPolynomial_of_le_half (n : ℕ) (q : unitInterval)
    (hn : 0 < n) (hq_half : (q : ℝ) ≤ 1 / 2) :
    (1 / 4 : ℝ) ≤ (binomialLowerPolynomial n (⌊(q : ℝ) * n⌋₊ + 1)).eval (q : ℝ) := by
  have hn0 : (0 : ℝ) < n := mod_cast hn
  have hr₁ := Nat.floor_le (mul_nonneg (unitInterval.nonneg q) hn0.le)
  have hr₂ := Nat.lt_floor_add_one ((q : ℝ) * n)
  generalize ⌊(q : ℝ) * n⌋₊ = r at hr₁ hr₂ ⊢
  have hanti := antitoneOn_eval_binomialLowerPolynomial n (r + 1) r.succ_pos q.2
  by_cases hcenter : 2 * (r + 1) ≤ n
  · refine (one_fourth_le_centered_binomialLowerPolynomial n _ r.succ_pos hcenter).trans
      (hanti ⟨by positivity, ?_⟩ ?_)
    · exact div_le_one_of_le₀ (mod_cast (by grind : r + 1 ≤ n)) hn0.le
    · rw [le_div_iff₀ hn0]
      exact_mod_cast hr₂.le
  · have hqn := mul_le_mul_of_nonneg_right hq_half hn0.le
    have h2r : 2 * r ≤ n := mod_cast (by linarith : (2 : ℝ) * r ≤ n)
    rw [(by grind : r = n / 2)] at hanti ⊢
    exact (one_fourth_le_eval_half_binomialLowerPolynomial_midpoint n).trans
      (hanti ⟨by norm_num, by norm_num⟩ hq_half)

/-- If `3 ≤ p * n`, then a binomial variable with parameters `n` and `p` is at least `p * n` with
probability at least `1 / 4`. -/
private lemma one_fourth_le_binomialUpperTail_of_three_le_mean (n : ℕ) (p : unitInterval)
    (hmean : (3 : ℝ) ≤ (p : ℝ) * (n : ℝ)) :
    (1 / 4 : ℝ) ≤ binomialUpperTail n ⌈(p : ℝ) * (n : ℝ)⌉₊ p := by
  by_cases hp_half : (p : ℝ) ≤ 1 / 2
  · exact one_fourth_le_binomialUpperTail_of_three_le_mean_of_le_half n p hmean hp_half
  · obtain rfl | hn := n.eq_zero_or_pos
    · norm_num at hmean
    have hcut := ceil_mul_add_floor_one_sub_mul n p
    have hlower := one_fourth_le_binomialLowerPolynomial_of_le_half n (unitInterval.symm p) hn
      (by linarith [unitInterval.coe_symm_eq p])
    rw [unitInterval.coe_symm_eq, eval_one_sub_binomialLowerPolynomial n _ p (by grind)] at hlower
    rwa [(by grind : n + 1 - (⌊(1 - (p : ℝ)) * n⌋₊ + 1) = ⌈(p : ℝ) * n⌉₊)] at hlower

/-! ### The number of elements of the random subset -/

/-- The number of elements of the `p`-random subset of a finite set `Ω ⊆ ℕ` is binomial with
parameters `|Ω|` and `p`. -/
private lemma binomialFinsetSubset_real_card_ge_eq_upperTail {Ω : Set ℕ} (hΩ : Ω.Finite)
    (p : unitInterval) (m : ℕ) :
    (binomialFinsetSubset Ω p).real {S : Finset ℕ | (S : Set ℕ) ⊆ Ω ∧ m ≤ #S} =
      binomialUpperTail Ω.ncard m p := by
  have hA : {S : Finset ℕ | (S : Set ℕ) ⊆ Ω ∧ m ≤ #S} =
      ↑((Icc m #hΩ.toFinset).biUnion hΩ.toFinset.powersetCard) := by
    ext S
    simpa using fun hS _ ↦ card_le_card (hΩ.subset_toFinset.2 hS)
  rw [hA, ← sum_measureReal_singleton,
    sum_biUnion (hΩ.toFinset.pairwise_disjoint_powersetCard.set_pairwise _), binomialUpperTail,
    Set.ncard_eq_toFinset_card Ω hΩ]
  congr with k
  rw [binomialMass, ← card_powersetCard, mul_assoc, ← nsmul_eq_mul]
  apply sum_eq_card_nsmul
  intro S hS
  obtain ⟨hSΩ, rfl⟩ := mem_powersetCard.1 hS
  rw [binomialFinsetSubset_real_singleton_nat_of_subset p hΩ (by simpa using hSΩ),
    Set.ncard_eq_toFinset_card Ω hΩ]

private lemma binomialFinsetSubset_real_dense_event_eq_upperTail (n : ℕ) (δ : unitInterval) :
    (binomialFinsetSubset (Set.Icc 1 n) δ).real
        {S : Finset ℕ | S ⊆ interval n ∧ (δ : ℝ) * (n : ℝ) ≤ (#S : ℝ)} =
      binomialUpperTail n ⌈(δ : ℝ) * (n : ℝ)⌉₊ δ := by
  have hevent : {S : Finset ℕ | S ⊆ interval n ∧ (δ : ℝ) * (n : ℝ) ≤ (#S : ℝ)} =
      {S : Finset ℕ | (S : Set ℕ) ⊆ Set.Icc 1 n ∧ ⌈(δ : ℝ) * (n : ℝ)⌉₊ ≤ #S} := by
    ext S
    simp [interval, ← coe_subset, Nat.ceil_le]
  rw [hevent, binomialFinsetSubset_real_card_ge_eq_upperTail (Set.finite_Icc 1 n)]
  simp

/-- If `δ n ≥ 3`, then the `δ`-random subset of `[n]` has at least `δ n` elements with probability
at least `1 / 4`. -/
lemma binomialFinsetSubset_real_dense_event_ge_quarter (n : ℕ) (δ : unitInterval)
    (hmean : (3 : ℝ) ≤ (δ : ℝ) * (n : ℝ)) :
    (1 / 4 : ℝ) ≤
      (binomialFinsetSubset (Set.Icc 1 n) δ).real
        {S : Finset ℕ | S ⊆ interval n ∧
          (δ : ℝ) * (n : ℝ) ≤ (#S : ℝ)} := by
  rw [binomialFinsetSubset_real_dense_event_eq_upperTail]
  exact one_fourth_le_binomialUpperTail_of_three_le_mean n δ hmean

end

end DenseSetsWithoutLargeSumsets
