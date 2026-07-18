/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.Probability
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.MeanInequalities
import Mathlib.RingTheory.Polynomial.Bernstein

/-!
Elementary facts about the binomial random variable used by the dense-set argument.

The mean-at-least-three binomial lower-tail estimate used by the dense-set argument is proved in
this file. Keeping the finite calculation here separates it from the construction of the Bernoulli
random finset.
-/

open scoped BigOperators ENNReal

namespace DenseSetsWithoutLargeSumsets

open MeasureTheory

noncomputable section

open Polynomial

/-- The upper tail of the elementary binomial mass function, written as a finite sum. -/
private def binomialUpperTail (n m : ℕ) (p : unitInterval) : ℝ :=
  ∑ k ∈ Finset.Icc m n,
    (n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)

/-- One term of the elementary binomial mass function. -/
private def binomialMass (n k : ℕ) (p : unitInterval) : ℝ :=
  (n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)

private def binomialLowerPolynomial (n s : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range s, bernsteinPolynomial ℝ n k

private lemma eval_binomialLowerPolynomial (n s : ℕ) (x : ℝ) :
    (binomialLowerPolynomial n s).eval x =
      ∑ k ∈ Finset.range s,
        (n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k) := by
  rw [binomialLowerPolynomial, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [bernsteinPolynomial]

private lemma derivative_binomialLowerPolynomial (n s : ℕ) (hs : 0 < s) :
    (binomialLowerPolynomial n s).derivative =
      -(n : ℝ[X]) * bernsteinPolynomial ℝ (n - 1) (s - 1) := by
  induction s with
  | zero => omega
  | succ s ih =>
      by_cases hs0 : s = 0
      · subst s
        simp [binomialLowerPolynomial, bernsteinPolynomial.derivative_zero]
      · rw [binomialLowerPolynomial, Finset.sum_range_succ, map_add]
        change (binomialLowerPolynomial n s).derivative +
          (bernsteinPolynomial ℝ n s).derivative = _
        rw [ih (Nat.pos_of_ne_zero hs0)]
        conv_lhs =>
          rhs
          rw [← Nat.sub_add_cancel (Nat.pos_of_ne_zero hs0)]
        rw [bernsteinPolynomial.derivative_succ (R := ℝ) n (s - 1)]
        simp only [Nat.sub_add_cancel (Nat.pos_of_ne_zero hs0)]
        push_cast
        ring

private lemma antitoneOn_eval_binomialLowerPolynomial (n s : ℕ) (hs : 0 < s) :
    AntitoneOn (fun x : ℝ => (binomialLowerPolynomial n s).eval x) (Set.Icc 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · fun_prop
  · fun_prop
  · intro x hx
    rw [(binomialLowerPolynomial n s).hasDerivAt x |>.deriv,
      derivative_binomialLowerPolynomial n s hs]
    have hxmem : x ∈ Set.Icc (0 : ℝ) 1 := interior_subset hx
    have hx0 : 0 ≤ x := hxmem.1
    have hx1 : 0 ≤ 1 - x := sub_nonneg.mpr hxmem.2
    simp only [bernsteinPolynomial, neg_mul, eval_neg, eval_mul, eval_natCast, eval_pow, eval_X,
      eval_sub, eval_one, Left.neg_nonpos_iff, ge_iff_le]
    exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx0 _))
        (pow_nonneg hx1 _))

private lemma centered_step_factor_ge_one (s d : ℕ) (hs : 0 < s) (hd : 0 < d) :
    (1 : ℝ) ≤ (((s + d + 1 : ℕ) : ℝ) / (s + d)) ^ s *
      (((d : ℝ) * (s + d + 1)) / ((s + d) * (d + 1))) ^ d := by
  let n : ℝ := s + d
  let A : ℝ := (s + d + 1) / n
  let B : ℝ := (d * (s + d + 1)) / (n * (d + 1))
  have hn : 0 < n := by dsimp [n]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B, n]; positivity
  have hw1 : 0 ≤ (s : ℝ) / n := by positivity
  have hw2 : 0 ≤ (d : ℝ) / n := by positivity
  have hw : (s : ℝ) / n + (d : ℝ) / n = 1 := by
    dsimp [n]
    field_simp
  have hamgm := Real.geom_mean_le_arith_mean2_weighted hw1 hw2
    (inv_nonneg.mpr hA.le) (inv_nonneg.mpr hB.le) hw
  have harith : (s : ℝ) / n * A⁻¹ + (d : ℝ) / n * B⁻¹ = 1 := by
    dsimp [A, B, n]
    field_simp
    ring
  rw [harith] at hamgm
  have hpow := Real.rpow_le_rpow
    (mul_nonneg (Real.rpow_nonneg (inv_nonneg.mpr hA.le) _)
      (Real.rpow_nonneg (inv_nonneg.mpr hB.le) _))
    hamgm (by positivity : 0 ≤ n)
  have hinv : (A ^ s * B ^ d)⁻¹ ≤ 1 := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (inv_nonneg.mpr hA.le),
      ← Real.rpow_mul (inv_nonneg.mpr hB.le)] at hpow
    norm_num at hpow
    have hsprod : (s : ℝ) / n * n = s := by field_simp
    have hdprod : (d : ℝ) / n * n = d := by field_simp
    rw [hsprod, hdprod, Real.rpow_natCast, Real.rpow_natCast] at hpow
    rw [mul_inv, ← inv_pow, ← inv_pow]
    simpa [mul_comm] using hpow
  have hprod : 0 < A ^ s * B ^ d := mul_pos (pow_pos hA _) (pow_pos hB _)
  rw [inv_le_one₀ hprod] at hinv
  simpa [A, B, n] using hinv

private lemma centered_boundary_cost_le (s d : ℕ) (hs : 0 < s) (hd : 0 < d) :
    (((s + d).choose (s - 1) : ℝ) *
        ((s : ℝ) / (s + d + 1)) ^ s *
        (1 - (s : ℝ) / (s + d + 1)) ^ (d + 1)) ≤
      ((s + d : ℝ) * ((s + d - 1).choose (s - 1) : ℝ) *
        ((s : ℝ) / (s + d)) ^ (s - 1) *
        (1 - (s : ℝ) / (s + d)) ^ d *
        ((s : ℝ) / (s + d) - (s : ℝ) / (s + d + 1))) := by
  let R : ℝ := ((s + d).choose (s - 1) : ℝ) *
    ((s : ℝ) / (s + d + 1)) ^ s *
    (1 - (s : ℝ) / (s + d + 1)) ^ (d + 1)
  let Q : ℝ := (((s + d + 1 : ℕ) : ℝ) / (s + d)) ^ s *
    (((d : ℝ) * (s + d + 1)) / ((s + d) * (d + 1))) ^ d
  have hR : 0 ≤ R := by
    dsimp [R]
    have ha : 0 ≤ (1 : ℝ) - (s : ℝ) / (s + d + 1) := by
      rw [sub_nonneg, div_le_one (by positivity)]
      exact_mod_cast (by omega : s ≤ s + d + 1)
    positivity
  have hRQ : R ≤ R * Q := by
    nlinarith [centered_step_factor_ge_one s d hs hd]
  have hchoose' : ((s + d).choose (s - 1) : ℝ) =
      ((s + d - 1).choose (s - 1) : ℝ) * (s + d) / (d + 1) := by
    rw [eq_div_iff (by positivity : (d + 1 : ℝ) ≠ 0)]
    symm
    exact_mod_cast (by simpa [(by omega : s + d - 1 + 1 = s + d),
      (by omega : s + d - (s - 1) = d + 1)] using
        Nat.choose_mul_succ_eq (s + d - 1) (s - 1))
  change R ≤ _
  refine hRQ.trans_eq ?_
  dsimp [R, Q]
  rw [one_sub_div (by positivity : (s + d + 1 : ℝ) ≠ 0),
    one_sub_div (by positivity : (s + d : ℝ) ≠ 0)]
  rw [div_sub_div (s : ℝ) (s : ℝ) (by positivity) (by positivity),
    mul_comm ((s : ℝ) + d) s, ← mul_sub, add_sub_cancel_left,
    add_sub_cancel_left, mul_one]
  simp only [add_assoc, add_sub_cancel_left]
  rw [hchoose']
  norm_num only [Nat.cast_add, Nat.cast_one]
  simp only [mul_pow, div_pow, pow_succ]
  field_simp
  have hspow : (s : ℝ) ^ s = (s : ℝ) ^ (s - 1) * s := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ s), pow_succ]
    simp [Nat.sub_add_cancel (by omega : 1 ≤ s)]
  have hnpow : ((s : ℝ) + d) ^ s =
      ((s : ℝ) + d) ^ (s - 1) * (s + d) := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ s), pow_succ]
    simp [Nat.sub_add_cancel (by omega : 1 ≤ s)]
  rw [hspow, hnpow]
  ring

private lemma bernsteinPolynomial_degree_succ (n k : ℕ) (hk : k ≤ n) :
    bernsteinPolynomial ℝ (n + 1) (k + 1) =
      (1 - X) * bernsteinPolynomial ℝ n (k + 1) +
        X * bernsteinPolynomial ℝ n k := by
  rw [bernsteinPolynomial, bernsteinPolynomial, bernsteinPolynomial]
  rw [Nat.choose_succ_succ']
  rw [Nat.succ_sub_succ_eq_sub]
  by_cases hkn : k = n
  · subst k
    simp
    simp [pow_succ, mul_comm]
  · rw [← Nat.sub_add_cancel (Nat.sub_pos_of_lt (lt_of_le_of_ne hk hkn)), pow_succ]
    rw [Nat.sub_succ']
    norm_num only [Nat.sub_zero]
    push_cast
    ring_nf
    rw [add_comm 1 k, Nat.sub_succ']

private lemma binomialLowerPolynomial_degree_succ
    (n s : ℕ) (hs : 0 < s) (hsn : s ≤ n + 1) :
    binomialLowerPolynomial (n + 1) s =
      binomialLowerPolynomial n s - X * bernsteinPolynomial ℝ n (s - 1) := by
  induction s with
  | zero => omega
  | succ s ih =>
      by_cases hs0 : s = 0
      · subst s
        simp [binomialLowerPolynomial, bernsteinPolynomial, pow_succ]
        ring
      · rw [binomialLowerPolynomial, Finset.sum_range_succ]
        change binomialLowerPolynomial (n + 1) s + bernsteinPolynomial ℝ (n + 1) s = _
        rw [ih (Nat.pos_of_ne_zero hs0) (by omega)]
        conv_rhs =>
          lhs
          rw [binomialLowerPolynomial, Finset.sum_range_succ]
        simp only [Nat.add_sub_cancel]
        change binomialLowerPolynomial n s - X * bernsteinPolynomial ℝ n (s - 1) +
            bernsteinPolynomial ℝ (n + 1) s =
          (binomialLowerPolynomial n s + bernsteinPolynomial ℝ n s) -
            X * bernsteinPolynomial ℝ n s
        conv_lhs =>
          rhs
          rw [← Nat.sub_add_cancel (Nat.pos_of_ne_zero hs0)]
        rw [bernsteinPolynomial_degree_succ n (s - 1) (by omega)]
        simp only [Nat.sub_add_cancel (Nat.pos_of_ne_zero hs0)]
        ring

private def boundaryKernel (n s : ℕ) (x : ℝ) : ℝ :=
  x ^ (s - 1) * (1 - x) ^ (n - s)

private lemma hasDerivAt_boundaryKernel_of_two_le
    (n s : ℕ) (hs : 2 ≤ s) (hsn : s < n) (x : ℝ) :
    HasDerivAt (boundaryKernel n s)
      (x ^ (s - 2) * (1 - x) ^ (n - s - 1) *
        (((s - 1 : ℕ) : ℝ) * (1 - x) - ((n - s : ℕ) : ℝ) * x)) x := by
  unfold boundaryKernel
  apply ((hasDerivAt_id x).pow (s - 1) |>.mul
    ((HasDerivAt.const_sub (1 : ℝ) (hasDerivAt_id x)).pow (n - s))).congr_deriv
  dsimp only [id_eq, Pi.pow_apply, Pi.mul_apply]
  rw [Nat.sub_sub]
  norm_num only [Nat.reduceAdd]
  rw [← Nat.sub_add_cancel (by omega : 1 ≤ s - 1), pow_succ]
  rw [← Nat.sub_add_cancel (by omega : 1 ≤ n - s), pow_succ]
  simp only [Nat.sub_add_cancel (by omega : 1 ≤ s - 1),
    Nat.sub_add_cancel (by omega : 1 ≤ n - s)]
  simp only [Nat.sub_sub]
  norm_num only [Nat.reduceAdd]
  ring_nf

private lemma antitoneOn_boundaryKernel
    (n s : ℕ) (hs : 0 < s) (hns : 2 * s ≤ n) :
    AntitoneOn (boundaryKernel n s)
      (Set.Icc ((s : ℝ) / (n + 1)) ((s : ℝ) / n)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
  · unfold boundaryKernel
    fun_prop
  · unfold boundaryKernel
    fun_prop
  · intro x hx
    obtain ⟨hxa, hxb⟩ := interior_subset hx
    have hx1 : 0 ≤ 1 - x := sub_nonneg.mpr (hxb.trans
      ((div_le_one (Nat.cast_pos.mpr (by omega))).mpr
        (by exact_mod_cast (by omega : s ≤ n))))
    by_cases hs1 : s = 1
    · subst s
      have hderiv : HasDerivAt (boundaryKernel n 1)
          (-((n - 1 : ℕ) : ℝ) * (1 - x) ^ (n - 2)) x := by
        refine ((HasDerivAt.const_sub (1 : ℝ) (hasDerivAt_id x)).pow (n - 1)
          |>.congr_of_eventuallyEq ?_).congr_deriv ?_
        · filter_upwards [] with y
          simp [boundaryKernel]
        · dsimp
          rw [Nat.sub_sub]
          norm_num only [Nat.reduceAdd]
          ring_nf
      rw [hderiv.deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _))
        (pow_nonneg hx1 _)
    · rw [(hasDerivAt_boundaryKernel_of_two_le n s (by omega) (by omega) x).deriv]
      refine mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (pow_nonneg (le_trans (by positivity) hxa) _)
          (pow_nonneg hx1 _)) ?_
      rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_sub (by omega : s ≤ n)]
      norm_num only [Nat.cast_one]
      have hnsub : (0 : ℝ) < (n : ℝ) - 1 :=
        sub_pos.mpr (Nat.one_lt_cast.mpr (by omega))
      have hnsr : (2 : ℝ) * (s : ℝ) ≤ (n : ℝ) := by exact_mod_cast hns
      suffices hmode : ((s : ℝ) - 1) / ((n : ℝ) - 1) ≤ x by
        rw [div_le_iff₀ hnsub] at hmode
        nlinarith
      refine le_trans ?_ hxa
      rw [div_le_div_iff₀ hnsub (by positivity)]
      nlinarith

private lemma deriv_eval_binomialLowerPolynomial
    (n s : ℕ) (hs : 0 < s) (_hsn : s ≤ n) (x : ℝ) :
    deriv (fun y : ℝ => (binomialLowerPolynomial n s).eval y) x =
      -(n : ℝ) * ((n - 1).choose (s - 1) : ℝ) * boundaryKernel n s x := by
  rw [(binomialLowerPolynomial n s).hasDerivAt x |>.deriv,
    derivative_binomialLowerPolynomial n s hs]
  simp only [bernsteinPolynomial, neg_mul, eval_neg, eval_mul, eval_natCast, eval_pow, eval_X,
    eval_sub, eval_one, boundaryKernel, neg_inj]
  rw [Nat.sub_sub_sub_cancel_right (by omega : 1 ≤ s)]
  ring

private lemma centered_binomialLowerPolynomial_step
    (s d : ℕ) (hs : 0 < s) (hsd : s ≤ d) :
    (binomialLowerPolynomial (s + d) s).eval ((s : ℝ) / (s + d)) ≤
      (binomialLowerPolynomial (s + d + 1) s).eval ((s : ℝ) / (s + d + 1)) := by
  let n : ℕ := s + d
  let a : ℝ := (s : ℝ) / (n + 1)
  let b : ℝ := (s : ℝ) / n
  have hd : 0 < d := hs.trans_le hsd
  have hn : 0 < n := by dsimp [n]; omega
  have hsn : s ≤ n := by dsimp [n]; omega
  have h2sn : 2 * s ≤ n := by dsimp [n]; omega
  have hab : a ≤ b := by
    dsimp [a, b]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    norm_num
  have hkb : b ∈ Set.Icc ((s : ℝ) / (n + 1)) ((s : ℝ) / n) :=
    ⟨hab, le_rfl⟩
  let f : ℝ → ℝ := fun x => (binomialLowerPolynomial n s).eval x
  have hderiv_le : ∀ x ∈ interior (Set.Icc a b), deriv f x ≤ deriv f b := by
    intro x hx
    have hk := antitoneOn_boundaryKernel n s hs h2sn
      (by simpa [a, b] using interior_subset hx) hkb
      (by simpa [a, b] using (interior_subset hx).2)
    dsimp [f]
    rw [deriv_eval_binomialLowerPolynomial n s hs hsn x,
      deriv_eval_binomialLowerPolynomial n s hs hsn b]
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      (Nat.cast_nonneg ((n - 1).choose (s - 1)) :
        (0 : ℝ) ≤ (n - 1).choose (s - 1))]
  have hsec : f b - f a ≤ deriv f b * (b - a) :=
    (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
      (by dsimp [f]; fun_prop) (by dsimp [f]; fun_prop) hderiv_le a
      ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
  have hcost := centered_boundary_cost_le s d hs hd
  have hcost' :
      ((n.choose (s - 1) : ℝ) * a ^ s * (1 - a) ^ (d + 1)) ≤
        -(deriv f b) * (b - a) := by
    dsimp [n, a, b, f] at hcost ⊢
    norm_num only [Nat.cast_add, Nat.cast_one] at hcost ⊢
    rw [deriv_eval_binomialLowerPolynomial (s + d) s hs (by omega)]
    simp only [boundaryKernel]
    rw [Nat.add_sub_cancel_left]
    push_cast
    convert hcost using 1 ; ring
  have hgap :
      (n.choose (s - 1) : ℝ) * a ^ s * (1 - a) ^ (d + 1) ≤ f a - f b := by
    linarith
  have hrec := congrArg (fun P : ℝ[X] => P.eval a)
    (binomialLowerPolynomial_degree_succ n s hs (by omega : s ≤ n + 1))
  have hrec' :
      (binomialLowerPolynomial (n + 1) s).eval a =
        f a - (n.choose (s - 1) : ℝ) * a ^ s * (1 - a) ^ (d + 1) := by
    dsimp [f]
    rw [hrec]
    simp only [bernsteinPolynomial, eval_sub, eval_mul, eval_X, eval_natCast, eval_pow, eval_one,
      sub_right_inj]
    dsimp [n]
    rw [Nat.sub_add_comm (Nat.sub_le s 1), Nat.sub_sub_self hs, add_comm]
    have hspow : a ^ s = a ^ (s - 1) * a := by
      conv_lhs => rw [← Nat.sub_add_cancel hs, pow_succ]
    rw [hspow]
    ring
  dsimp [f, n, a, b] at hrec' hgap ⊢
  norm_num only [Nat.cast_add, Nat.cast_one] at hrec' hgap ⊢
  rw [hrec']
  linarith

/-- The adjacent-term recurrence for the binomial mass function. -/
private lemma binomialMass_mul_succ (n k : ℕ) (p : unitInterval) (hk : k < n) :
    binomialMass n k p * (n - k : ℕ) * (p : ℝ) =
      binomialMass n (k + 1) p * (k + 1 : ℕ) * (1 - (p : ℝ)) := by
  unfold binomialMass
  have hchoose' :
      (n.choose (k + 1) : ℝ) * (k + 1 : ℕ) =
        (n.choose k : ℝ) * (n - k : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq n k
  have hnk : n - k = n - (k + 1) + 1 := by omega
  calc
    (n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) *
          (n - k : ℕ) * (p : ℝ) =
        ((n.choose k : ℝ) * (n - k : ℕ)) * (p : ℝ) ^ (k + 1) *
          (1 - (p : ℝ)) ^ (n - (k + 1)) * (1 - (p : ℝ)) := by
      rw [hnk, pow_succ, pow_succ]
      ring
    _ = ((n.choose (k + 1) : ℝ) * (k + 1 : ℕ)) * (p : ℝ) ^ (k + 1) *
          (1 - (p : ℝ)) ^ (n - (k + 1)) * (1 - (p : ℝ)) := by
      rw [hchoose']
    _ = (n.choose (k + 1) : ℝ) * (p : ℝ) ^ (k + 1) *
          (1 - (p : ℝ)) ^ (n - (k + 1)) * (k + 1 : ℕ) *
          (1 - (p : ℝ)) := by ring

private lemma le_of_paired_recurrences
    {x y z w A B C D : ℝ}
    (hx : x * A = y * B) (hz : z * C = w * D)
    (hyz : y ≤ z) (hz0 : 0 ≤ z)
    (hB0 : 0 ≤ B) (hA : 0 < A) (hD : 0 < D)
    (hcross : B * D ≤ A * C) : x ≤ w := by
  have hmul : x * (A * D) ≤ w * (A * D) := calc
    x * (A * D) = y * (B * D) := by rw [← mul_assoc, hx]; ring
    _ ≤ z * (B * D) := by
      exact mul_le_mul_of_nonneg_right hyz (mul_nonneg hB0 hD.le)
    _ ≤ z * (A * C) := mul_le_mul_of_nonneg_left hcross hz0
    _ = A * (z * C) := by ring
    _ = A * (w * D) := by rw [hz]
    _ = w * (A * D) := by ring
  nlinarith [mul_pos hA hD]

private lemma paired_binomial_factor_inequality
    {N R J x : ℝ} (hR : 0 < R) (hJ0 : 0 ≤ J) (hJ : J < R)
    (hNR : R ≤ N) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hratio : R * (1 - x) ≤ N * x) :
    ((R - J) * (1 - x)) * ((R + J) * (1 - x)) ≤
      ((N + J + 1) * x) * ((N - J + 1) * x) := by
  have hN0 : 0 ≤ N := hR.le.trans hNR
  have hB : 0 ≤ (R - J) * (R + J) := by positivity
  have hsq : (R * (1 - x)) ^ 2 ≤ (N * x) ^ 2 := by
    exact (sq_le_sq₀ (mul_nonneg hR.le (sub_nonneg.mpr hx1))
      (mul_nonneg hN0 hx)).mpr hratio
  have hcoef :
      N ^ 2 * ((R - J) * (R + J)) ≤
        R ^ 2 * ((N + J + 1) * (N - J + 1)) := by
    have hNN : 0 ≤ N ^ 2 - R ^ 2 :=
      sub_nonneg.mpr ((sq_le_sq₀ hR.le hN0).mpr hNR)
    have hid :
        R ^ 2 * ((N + J + 1) * (N - J + 1)) -
            N ^ 2 * ((R - J) * (R + J)) =
          R ^ 2 * (2 * N + 1) + J ^ 2 * (N ^ 2 - R ^ 2) := by
      ring
    rw [← sub_nonneg, hid]
    positivity
  have h1 := mul_le_mul_of_nonneg_left hsq hB
  have h2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg x)
  ring_nf at h1 h2 ⊢
  nlinarith [sq_pos_of_pos hR]

/-- Reflection of binomial masses about the integral part of the mean when `p ≤ 1/2`. -/
private lemma binomialMass_reflection
    (n r : ℕ) (p : unitInterval) (hr : 1 ≤ r) (h2r : 2 * r ≤ n)
    (hmean : (r : ℝ) ≤ (p : ℝ) * (n : ℝ)) (hp_half : (p : ℝ) ≤ 1 / 2)
    (j : ℕ) (hj : 1 ≤ j) (hjr : j ≤ r) :
    binomialMass n (r - j) p ≤ binomialMass n (r + j - 1) p := by
  have hp_pos : 0 < (p : ℝ) := by
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    have hrpos : 0 < (r : ℝ) := by positivity
    nlinarith
  have hq_pos : 0 < 1 - (p : ℝ) := by nlinarith
  have hrn : r ≤ n := by omega
  have hNR : r ≤ n - r := by omega
  have hratio :
      (r : ℝ) * (1 - (p : ℝ)) ≤ ((n - r : ℕ) : ℝ) * (p : ℝ) := by
    rw [Nat.cast_sub hrn]
    nlinarith
  induction j with
  | zero => omega
  | succ j ih =>
      by_cases hj0 : j = 0
      · subst j
        have hrpred : r - 1 + 1 = r := by omega
        have hright : r + (0 + 1) - 1 = r := by omega
        rw [hright]
        have hfactor :
            (r : ℝ) * (1 - (p : ℝ)) ≤
              ((n - (r - 1) : ℕ) : ℝ) * (p : ℝ) := by
          rw [Nat.cast_sub (by omega : r - 1 ≤ n)]
          have hrpredcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ r)]
            norm_num
          rw [hrpredcast]
          nlinarith
        have hfactor_pos :
            0 < ((n - (r - 1) : ℕ) : ℝ) * (p : ℝ) := by
          exact mul_pos (by exact_mod_cast (by omega : 0 < n - (r - 1))) hp_pos
        apply (mul_le_mul_iff_of_pos_right hfactor_pos).mp
        rw [← mul_assoc, binomialMass_mul_succ n (r - 1) p (by omega), hrpred]
        simpa [mul_assoc] using
          mul_le_mul_of_nonneg_left hfactor (by
            simpa only [binomialMass] using
              (ProbabilityTheory.binomial_nonneg (n := n) (k := r) (p := p)))
      · have hjpos : 1 ≤ j := by omega
        have hjlt : j < r := by omega
        have hinner := ih hjpos hjlt.le
        let l : ℕ := r - j - 1
        let u : ℕ := r + j - 1
        have hl_succ : l + 1 = r - j := by dsimp [l]; omega
        have hu_succ : u + 1 = r + j := by dsimp [u]; omega
        have hnl : n - l = (n - r) + j + 1 := by dsimp [l]; omega
        have hnu : n - u = (n - r) - j + 1 := by dsimp [u]; omega
        have hl_lt : l < n := by dsimp [l]; omega
        have hu_lt : u < n := by dsimp [u]; omega
        refine le_of_paired_recurrences
          (x := binomialMass n l p) (y := binomialMass n (r - j) p)
          (z := binomialMass n u p) (w := binomialMass n (r + j) p)
          (A := ((n - l : ℕ) : ℝ) * (p : ℝ))
          (B := ((l + 1 : ℕ) : ℝ) * (1 - (p : ℝ)))
          (C := ((n - u : ℕ) : ℝ) * (p : ℝ))
          (D := ((u + 1 : ℕ) : ℝ) * (1 - (p : ℝ)))
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · rw [hl_succ]
          simpa only [hl_succ, Nat.cast_add, Nat.cast_one, mul_assoc] using
            binomialMass_mul_succ n l p hl_lt
        · rw [hu_succ]
          simpa only [hu_succ, Nat.cast_add, Nat.cast_one, mul_assoc] using
            binomialMass_mul_succ n u p hu_lt
        · simpa [u] using hinner
        · simpa only [binomialMass] using
            (ProbabilityTheory.binomial_nonneg (n := n) (k := u) (p := p))
        · positivity
        · exact mul_pos (by exact_mod_cast (by omega : 0 < n - l)) hp_pos
        · exact mul_pos (by exact_mod_cast (by omega : 0 < u + 1)) hq_pos
        · rw [hl_succ, hu_succ, hnl, hnu, Nat.cast_sub (by omega : j ≤ r)]
          push_cast
          rw [Nat.cast_sub (by omega : j ≤ n - r)]
          exact paired_binomial_factor_inequality
            (N := (n - r : ℕ)) (R := r) (J := j) (x := (p : ℝ))
            (by positivity) (by positivity) (by exact_mod_cast hjlt)
            (by exact_mod_cast hNR) p.2.1 p.2.2 hratio

private lemma sum_binomialMass (n : ℕ) (p : unitInterval) :
    ∑ k ∈ Finset.range (n + 1), binomialMass n k p = 1 := by
  simpa [binomialMass, mul_comm, mul_left_comm, mul_assoc] using
    (add_pow (p : ℝ) (1 - (p : ℝ)) n).symm

/-- For `p ≤ 1/2`, at least half of the binomial mass is at or above an integral lower bound
for the mean. -/
private lemma one_half_le_binomialUpperTail_of_le_half
    (n r : ℕ) (p : unitInterval) (hr : 1 ≤ r) (h2r : 2 * r ≤ n)
    (hmean : (r : ℝ) ≤ (p : ℝ) * (n : ℝ)) (hp_half : (p : ℝ) ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ binomialUpperTail n r p := by
  have hreflectSum :
      (∑ k ∈ Finset.range r, binomialMass n k p) ≤
        ∑ k ∈ Finset.range r, binomialMass n (2 * r - 1 - k) p := by
    apply Finset.sum_le_sum
    intro k hk
    have hkr : k < r := Finset.mem_range.mp hk
    have hreflect := binomialMass_reflection n r p hr h2r hmean hp_half
      (r - k) (by omega) (by omega)
    have hleftIndex : r - (r - k) = k := by omega
    have hrightIndex : r + (r - k) - 1 = 2 * r - 1 - k := by omega
    simpa only [hleftIndex, hrightIndex] using hreflect
  have hreindex :
      (∑ k ∈ Finset.range r, binomialMass n (2 * r - 1 - k) p) =
        ∑ k ∈ Finset.Icc r (2 * r - 1), binomialMass n k p := by
    apply Finset.sum_bij (fun k _ => 2 * r - 1 - k)
    · intro k hk
      simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
      omega
    · intro a₁ ha₁ a₂ ha₂ heq
      simp only [Finset.mem_range] at ha₁ ha₂
      omega
    · intro b hb
      simp only [Finset.mem_Icc] at hb
      refine ⟨2 * r - 1 - b, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
    · intro k hk
      rfl
  have hselected :
      (∑ k ∈ Finset.range r, binomialMass n k p) ≤
        ∑ k ∈ Finset.Icc r (2 * r - 1), binomialMass n k p := by
    rw [← hreindex]
    exact hreflectSum
  have hselectedTail :
      (∑ k ∈ Finset.Icc r (2 * r - 1), binomialMass n k p) ≤
        binomialUpperTail n r p := by
    unfold binomialUpperTail
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.Icc_subset_Icc le_rfl (by omega)
    · intro k hk hnot
      simpa only [binomialMass] using
        (ProbabilityTheory.binomial_nonneg (n := n) (k := k) (p := p))
  have hlowerTail :
      (∑ k ∈ Finset.range r, binomialMass n k p) ≤ binomialUpperTail n r p :=
    hselected.trans hselectedTail
  have hpartition :
      (∑ k ∈ Finset.range r, binomialMass n k p) + binomialUpperTail n r p = 1 := by
    have hsplit := Finset.sum_range_add_sum_Ico (fun k => binomialMass n k p)
      (by omega : r ≤ n + 1)
    have hIco : Finset.Ico r (n + 1) = Finset.Icc r n := by
      ext k
      simp
    rw [hIco] at hsplit
    change (∑ k ∈ Finset.range r, binomialMass n k p) +
      (∑ k ∈ Finset.Icc r n, binomialMass n k p) = 1
    rw [hsplit, sum_binomialMass]
  linarith

private lemma binomialMass_le_next_add_next
    (n r : ℕ) (p : unitInterval) (hr : 3 ≤ r) (h2r : 2 * r ≤ n)
    (hmean : (r : ℝ) ≤ (p : ℝ) * (n : ℝ)) (hp_half : (p : ℝ) ≤ 1 / 2) :
    binomialMass n r p ≤ binomialMass n (r + 1) p + binomialMass n (r + 2) p := by
  have hp_pos : 0 < (p : ℝ) := by
    have hrpos : 0 < (r : ℝ) := by positivity
    nlinarith [p.2.1]
  have hq_pos : 0 < 1 - (p : ℝ) := by nlinarith
  have hrec₁ := binomialMass_mul_succ n r p (by omega)
  have hfactor₁ :
      (r : ℝ) * (1 - (p : ℝ)) ≤ ((n - r : ℕ) : ℝ) * (p : ℝ) := by
    rw [Nat.cast_sub (by omega : r ≤ n)]
    nlinarith
  have hmul₁ :
      binomialMass n r p * ((r : ℝ) * (1 - (p : ℝ))) ≤
        binomialMass n (r + 1) p * (((r + 1 : ℕ) : ℝ) * (1 - (p : ℝ))) := by
    refine (mul_le_mul_of_nonneg_left hfactor₁ ?_).trans_eq ?_
    · simpa only [binomialMass] using
        (ProbabilityTheory.binomial_nonneg (n := n) (k := r) (p := p))
    · simpa [mul_assoc] using hrec₁
  have hnext₁ :
      (r : ℝ) * binomialMass n r p ≤
        (r + 1 : ℕ) * binomialMass n (r + 1) p := by
    nlinarith
  have hrec₂ := binomialMass_mul_succ n (r + 1) p (by omega)
  have hfactor₂ :
      ((r - 1 : ℕ) : ℝ) * (1 - (p : ℝ)) ≤
        ((n - (r + 1) : ℕ) : ℝ) * (p : ℝ) := by
    rw [Nat.cast_sub (by omega : r + 1 ≤ n),
      Nat.cast_sub (by omega : 1 ≤ r)]
    push_cast
    nlinarith
  have hmul₂ :
      binomialMass n (r + 1) p *
          (((r - 1 : ℕ) : ℝ) * (1 - (p : ℝ))) ≤
        binomialMass n (r + 2) p *
          (((r + 2 : ℕ) : ℝ) * (1 - (p : ℝ))) := by
    refine (mul_le_mul_of_nonneg_left hfactor₂ ?_).trans_eq ?_
    · simpa only [binomialMass] using
        (ProbabilityTheory.binomial_nonneg (n := n) (k := r + 1) (p := p))
    · simpa [Nat.add_assoc, mul_assoc] using hrec₂
  have hnext₂ :
      ((r - 1 : ℕ) : ℝ) * binomialMass n (r + 1) p ≤
        (r + 2 : ℕ) * binomialMass n (r + 2) p := by
    nlinarith
  let a := binomialMass n r p
  let b := binomialMass n (r + 1) p
  let c := binomialMass n (r + 2) p
  have ha0 : 0 ≤ a := by
    simpa only [a, binomialMass] using
      (ProbabilityTheory.binomial_nonneg (n := n) (k := r) (p := p))
  have hb0 : 0 ≤ b := by
    simpa only [b, binomialMass] using
      (ProbabilityTheory.binomial_nonneg (n := n) (k := r + 1) (p := p))
  have hb : ((r : ℝ) / (r + 1)) * a ≤ b := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    simpa [a, b, mul_comm] using hnext₁
  have hc : (((r - 1 : ℕ) : ℝ) / (r + 2)) * b ≤ c := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    simpa [b, c, mul_comm] using hnext₂
  have hcoeff :
      (1 : ℝ) ≤ (r : ℝ) / (r + 1) *
        (1 + ((r - 1 : ℕ) : ℝ) / (r + 2)) := by
    rw [Nat.cast_sub (by omega : 1 ≤ r)]
    field_simp
    norm_num
    have hrr : (3 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith [sq_nonneg ((r : ℝ) - 3)]
  refine (le_mul_of_one_le_left ha0 hcoeff).trans ?_
  nlinarith [hb, hc, mul_le_mul_of_nonneg_left hb
    (by positivity : (0 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) / (r + 2))]

/-- For `p ≤ 1/2` and integral part of the mean at least three, the strict upper tail is at
least one quarter. -/
private lemma one_fourth_le_binomialUpperTail_succ_of_le_half
    (n r : ℕ) (p : unitInterval) (hr : 3 ≤ r) (h2r : 2 * r ≤ n)
    (hmean : (r : ℝ) ≤ (p : ℝ) * (n : ℝ)) (hp_half : (p : ℝ) ≤ 1 / 2) :
    (1 / 4 : ℝ) ≤ binomialUpperTail n (r + 1) p := by
  have hhalf := one_half_le_binomialUpperTail_of_le_half n r p (by omega) h2r hmean hp_half
  have hnextTail : binomialMass n r p ≤ binomialUpperTail n (r + 1) p := by
    refine (binomialMass_le_next_add_next n r p hr h2r hmean hp_half).trans ?_
    suffices ∑ k ∈ ({r + 1, r + 2} : Finset ℕ), binomialMass n k p ≤
        binomialUpperTail n (r + 1) p by
      simpa using this
    unfold binomialUpperTail
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      simp only [Finset.mem_Icc]
      rcases hk with rfl | rfl <;> omega
    · intro k hk hnot
      simpa only [binomialMass] using
        (ProbabilityTheory.binomial_nonneg (n := n) (k := k) (p := p))
  have hsplit :
      binomialUpperTail n r p =
        binomialMass n r p + binomialUpperTail n (r + 1) p := by
    unfold binomialUpperTail
    have hset : Finset.Icc r n = insert r (Finset.Icc (r + 1) n) := by
      ext k
      simp
      omega
    rw [hset, Finset.sum_insert (by simp)]
    rfl
  rw [hsplit] at hhalf
  linarith

private def halfParameter : unitInterval :=
  ⟨1 / 2, by constructor <;> norm_num⟩

@[simp] private lemma halfParameter_coe : (halfParameter : ℝ) = 1 / 2 := rfl

private def complementParameter (p : unitInterval) : unitInterval :=
  ⟨1 - (p : ℝ), by constructor <;> nlinarith [p.2.1, p.2.2]⟩

@[simp] private lemma complementParameter_coe (p : unitInterval) :
    (complementParameter p : ℝ) = 1 - (p : ℝ) := rfl

private lemma binomialUpperTail_eq_complement_lower
    (n m : ℕ) (p : unitInterval) (hmn : m ≤ n) :
    binomialUpperTail n m p =
      (binomialLowerPolynomial n (n - m + 1)).eval (complementParameter p : ℝ) := by
  rw [eval_binomialLowerPolynomial]
  unfold binomialUpperTail
  apply Finset.sum_bij (fun k _ => n - k)
  · intro k hk
    simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
    omega
  · intro a₁ ha₁ a₂ ha₂ heq
    simp only [Finset.mem_Icc] at ha₁ ha₂
    omega
  · intro b hb
    simp only [Finset.mem_range] at hb
    refine ⟨n - b, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    rw [Nat.choose_symm hk.2]
    simp only [complementParameter_coe]
    rw [tsub_tsub_cancel_of_le hk.2]
    ring

private lemma ceil_mul_add_floor_complement
    (n : ℕ) (p : unitInterval) (hn : 0 < n) (hp_half : 1 / 2 < (p : ℝ)) :
    ⌈(p : ℝ) * n⌉₊ + ⌊(1 - (p : ℝ)) * n⌋₊ = n := by
  let r : ℕ := ⌊(1 - (p : ℝ)) * n⌋₊
  have hq0 : 0 ≤ (1 - (p : ℝ)) * n :=
    mul_nonneg (sub_nonneg.mpr p.2.2) (by positivity)
  have hrn : r < n := by
    apply (Nat.floor_lt hq0).mpr
    nlinarith [(by positivity : (0 : ℝ) < n)]
  have hrfloor : (r : ℝ) ≤ (1 - (p : ℝ)) * n := Nat.floor_le hq0
  have hrfloor' : (1 - (p : ℝ)) * n < (r : ℝ) + 1 := by
    simpa [r] using Nat.lt_floor_add_one ((1 - (p : ℝ)) * n)
  have hmcast : (((n - r : ℕ) : ℝ)) = (n : ℝ) - r := by
    rw [Nat.cast_sub hrn.le]
  have hmpredcast : (((n - r - 1 : ℕ) : ℝ)) = (n : ℝ) - r - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n - r), hmcast]
    norm_num
  have hceil : ⌈(p : ℝ) * n⌉₊ = n - r := by
    rw [Nat.ceil_eq_iff (by omega : n - r ≠ 0)]
    constructor
    · rw [hmpredcast]
      nlinarith
    · rw [hmcast]
      nlinarith
  dsimp [r] at hceil ⊢
  omega

private lemma binomialLower_eq_upper_half
    (n s : ℕ) (hsn : s ≤ n + 1) :
    (binomialLowerPolynomial n s).eval (1 / 2) =
      binomialUpperTail n (n + 1 - s) halfParameter := by
  rw [eval_binomialLowerPolynomial]
  unfold binomialUpperTail
  apply Finset.sum_bij (fun k _ => n - k)
  · intro k hk
    simp only [Finset.mem_range, Finset.mem_Icc] at hk ⊢
    omega
  · intro a₁ ha₁ a₂ ha₂ heq
    simp only [Finset.mem_range] at ha₁ ha₂
    omega
  · intro b hb
    simp only [Finset.mem_Icc] at hb
    refine ⟨n - b, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    have hkn : k ≤ n := by omega
    rw [Nat.choose_symm hkn]
    simp only [halfParameter_coe]
    rw [tsub_tsub_cancel_of_le hkn]
    ring

private lemma centered_lower_eq_strict_upper_half (s : ℕ) (hs : 0 < s) :
    (binomialLowerPolynomial (2 * s) s).eval (1 / 2) =
      binomialUpperTail (2 * s) (s + 1) halfParameter := by
  rw [eval_binomialLowerPolynomial]
  unfold binomialUpperTail
  apply Finset.sum_bij (fun k _ => 2 * s - k)
  · intro k hk
    simp only [Finset.mem_range, Finset.mem_Icc] at hk ⊢
    omega
  · intro a₁ ha₁ a₂ ha₂ heq
    simp only [Finset.mem_range] at ha₁ ha₂
    omega
  · intro b hb
    simp only [Finset.mem_Icc] at hb
    refine ⟨2 * s - b, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    have hk2 : k ≤ 2 * s := by omega
    rw [Nat.choose_symm hk2]
    simp only [halfParameter_coe]
    rw [tsub_tsub_cancel_of_le hk2]
    ring

private lemma one_fourth_le_binomialLower_half_at_midpoint
    (n : ℕ) (hn : 0 < n) :
    (1 / 4 : ℝ) ≤
      (binomialLowerPolynomial n (n / 2 + 1)).eval (1 / 2) := by
  rw [binomialLower_eq_upper_half n (n / 2 + 1) (by omega)]
  by_cases heven : 2 * (n / 2) = n
  · by_cases hn1 : n / 2 = 0
    · have : n = 1 := by omega
      subst n
      norm_num [binomialUpperTail, halfParameter]
    · have hr : 1 ≤ n / 2 := by omega
      have hmean : ((n / 2 : ℕ) : ℝ) ≤ (halfParameter : ℝ) * n := by
        have hevenR : (2 : ℝ) * (n / 2 : ℕ) = n := by exact_mod_cast heven
        simp only [halfParameter_coe]
        nlinarith
      have hhalf := one_half_le_binomialUpperTail_of_le_half
        n (n / 2) halfParameter hr (by omega) hmean (by simp)
      refine (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2).trans ?_
      convert hhalf using 1
      all_goals try rfl
      congr 1
      omega
  · have hodd : 2 * (n / 2) + 1 = n := by omega
    by_cases hr3 : 3 ≤ n / 2
    · have hmean : ((n / 2 : ℕ) : ℝ) ≤ (halfParameter : ℝ) * n := by
        have hoddR : (2 : ℝ) * (n / 2 : ℕ) + 1 = n := by exact_mod_cast hodd
        simp only [halfParameter_coe]
        nlinarith
      convert one_fourth_le_binomialUpperTail_succ_of_le_half
        n (n / 2) halfParameter hr3 (by omega) hmean (by simp) using 1
      congr 1
      omega
    · have hn5 : n ≤ 5 := by omega
      interval_cases n <;>
        norm_num [binomialUpperTail, halfParameter, Finset.sum_Icc_succ_top, Nat.choose] at hn ⊢

private lemma one_fourth_le_centered_binomialLowerPolynomial_base
    (s : ℕ) (hs : 0 < s) :
    (1 / 4 : ℝ) ≤ (binomialLowerPolynomial (2 * s) s).eval (1 / 2) := by
  rw [centered_lower_eq_strict_upper_half s hs]
  by_cases hs3 : 3 ≤ s
  · exact one_fourth_le_binomialUpperTail_succ_of_le_half
      (2 * s) s halfParameter hs3 (by omega) (by simp) (by simp)
  · interval_cases s <;>
      norm_num [binomialUpperTail, halfParameter, Finset.sum_Icc_succ_top]

private lemma one_fourth_le_centered_binomialLowerPolynomial
    (n s : ℕ) (hs : 0 < s) (h2s : 2 * s ≤ n) :
    (1 / 4 : ℝ) ≤
      (binomialLowerPolynomial n s).eval ((s : ℝ) / n) := by
  let d := n - s
  have hsd : s ≤ d := by dsimp [d]; omega
  have hbase : (1 / 4 : ℝ) ≤
      (binomialLowerPolynomial (s + s) s).eval ((s : ℝ) / (s + s)) := by
    rw [← two_mul]
    convert one_fourth_le_centered_binomialLowerPolynomial_base s hs using 1
    field_simp
    simp only [two_mul]
  have hd : (1 / 4 : ℝ) ≤
      (binomialLowerPolynomial (s + d) s).eval ((s : ℝ) / (s + d)) := by
    exact Nat.le_induction hbase (fun d hsd ih =>
      ih.trans (by simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
        centered_binomialLowerPolynomial_step s d hs hsd)) d hsd
  have hsum : s + d = n := by dsimp [d]; omega
  rw [hsum] at hd
  have hsumR : (s : ℝ) + d = n := by exact_mod_cast hsum
  rw [hsumR] at hd
  exact hd

private lemma one_fourth_le_binomialLowerPolynomial_of_le_half
    (n : ℕ) (q : unitInterval) (hn : 0 < n)
    (hq_half : (q : ℝ) ≤ 1 / 2) :
    (1 / 4 : ℝ) ≤
      (binomialLowerPolynomial n (⌊(q : ℝ) * n⌋₊ + 1)).eval (q : ℝ) := by
  let r : ℕ := ⌊(q : ℝ) * n⌋₊
  let s : ℕ := r + 1
  change (1 / 4 : ℝ) ≤ (binomialLowerPolynomial n s).eval (q : ℝ)
  have hs : 0 < s := by dsimp [s]; omega
  have hnreal : (0 : ℝ) < n := by positivity
  have hqy : (q : ℝ) < (s : ℝ) / n := by
    rw [lt_div_iff₀ hnreal]
    simpa [r, s, mul_comm] using Nat.lt_floor_add_one ((q : ℝ) * n)
  by_cases hcenter : 2 * s ≤ n
  · have hy : (s : ℝ) / n ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · exact (div_le_one hnreal).mpr (by exact_mod_cast (by omega : s ≤ n))
    have hqmem : (q : ℝ) ∈ Set.Icc (0 : ℝ) 1 := q.2
    exact (one_fourth_le_centered_binomialLowerPolynomial n s hs hcenter).trans
      (antitoneOn_eval_binomialLowerPolynomial n s hs hqmem hy hqy.le)
  · have hmul : (q : ℝ) * n ≤ (1 / 2 : ℝ) * n :=
      mul_le_mul_of_nonneg_right hq_half (by positivity)
    have hrle : r ≤ n / 2 := by
      have hf := Nat.floor_mono hmul
      have hhalfFloor : ⌊(1 / 2 : ℝ) * (n : ℝ)⌋₊ = n / 2 := by
        by_cases heven : 2 * (n / 2) = n
        · rw [← heven]
          push_cast
          simp
        · have hodd : 2 * (n / 2) + 1 = n := by omega
          rw [← hodd]
          push_cast
          ring_nf
          rw [Nat.floor_add_natCast (by norm_num)]
          have hh : ⌊(1 / 2 : ℝ)⌋₊ = 0 := by norm_num
          rw [hh]
          omega
      change r ≤ ⌊(1 / 2 : ℝ) * (n : ℝ)⌋₊ at hf
      rw [hhalfFloor] at hf
      exact hf
    have hrs : s = n / 2 + 1 := by dsimp [s]; omega
    have hbase := one_fourth_le_binomialLower_half_at_midpoint n hn
    have hhalfmem : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    have hqmem : (q : ℝ) ∈ Set.Icc (0 : ℝ) 1 := q.2
    have hanti := antitoneOn_eval_binomialLowerPolynomial n s hs hqmem hhalfmem hq_half
    rw [hrs] at hanti
    rw [hrs]
    exact hbase.trans hanti

/-- The quarter bound for all means at least three when `p ≤ 1/2`. -/
private lemma one_fourth_le_binomialUpperTail_of_three_le_mean_of_le_half
    (n : ℕ) (p : unitInterval)
    (hmean_three : (3 : ℝ) ≤ (p : ℝ) * (n : ℝ))
    (hp_half : (p : ℝ) ≤ 1 / 2) :
    (1 / 4 : ℝ) ≤ binomialUpperTail n ⌈(p : ℝ) * (n : ℝ)⌉₊ p := by
  let r : ℕ := ⌊(p : ℝ) * (n : ℝ)⌋₊
  have hmean_nonneg : 0 ≤ (p : ℝ) * (n : ℝ) := by positivity
  have hrmean : (r : ℝ) ≤ (p : ℝ) * (n : ℝ) := Nat.floor_le hmean_nonneg
  have hr : 3 ≤ r := by
    apply Nat.le_floor
    exact hmean_three
  have h2r : 2 * r ≤ n := by
    have hmean_half : (p : ℝ) * (n : ℝ) ≤ (n : ℝ) / 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hp_half) (by positivity : 0 ≤ (n : ℝ))]
    exact_mod_cast (by nlinarith : (2 : ℝ) * r ≤ n)
  apply (one_fourth_le_binomialUpperTail_succ_of_le_half
    n r p hr h2r hrmean hp_half).trans
  unfold binomialUpperTail
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc (Nat.ceil_le_floor_add_one ((p : ℝ) * (n : ℝ))) le_rfl
  · intro k hk hnot
    simpa only [binomialMass] using
      (ProbabilityTheory.binomial_nonneg (n := n) (k := k) (p := p))

/-- A binomial variable is at least its mean with probability at least one quarter. -/
private lemma one_fourth_le_binomialUpperTail_of_three_le_mean
    (n : ℕ) (p : unitInterval)
    (hmean : (3 : ℝ) ≤ (p : ℝ) * (n : ℝ)) :
    (1 / 4 : ℝ) ≤ binomialUpperTail n ⌈(p : ℝ) * (n : ℝ)⌉₊ p := by
  by_cases hp_half : (p : ℝ) ≤ 1 / 2
  · exact one_fourth_le_binomialUpperTail_of_three_le_mean_of_le_half
      n p hmean hp_half
  · have hn : 0 < n := by
      by_contra hn0
      have : n = 0 := by omega
      subst n
      norm_num at hmean
    let q : unitInterval := complementParameter p
    have hq_half : (q : ℝ) ≤ 1 / 2 := by
      dsimp [q]
      linarith
    have hlower := one_fourth_le_binomialLowerPolynomial_of_le_half n q hn hq_half
    let m : ℕ := ⌈(p : ℝ) * n⌉₊
    let r : ℕ := ⌊(1 - (p : ℝ)) * n⌋₊
    have hcut := ceil_mul_add_floor_complement n p hn (lt_of_not_ge hp_half)
    have hmr : m + r = n := by simpa [m, r] using hcut
    have hmle : m ≤ n := by omega
    have hs : n - m + 1 = r + 1 := by omega
    have href := binomialUpperTail_eq_complement_lower n m p hmle
    rw [hs] at href
    dsimp [q, r] at hlower
    rw [href]
    exact hlower

/-- The cardinality tail of a finite Bernoulli random finset is the elementary binomial tail. -/
private lemma binomialFinsetSubset_real_card_ge_eq_upperTail
    {Ω : Set ℕ} (hΩ : Ω.Finite) (p : unitInterval) (m : ℕ) :
    (binomialFinsetSubset Ω p).real
        {S : Finset ℕ | ((S : Finset ℕ) : Set ℕ) ⊆ Ω ∧ m ≤ S.card} =
      binomialUpperTail Ω.ncard m p := by
  classical
  let U : Finset ℕ := hΩ.toFinset
  let A : Finset (Finset ℕ) := U.powerset.filter fun S => m ≤ S.card
  have hA :
      (A : Set (Finset ℕ)) =
        {S : Finset ℕ | ((S : Finset ℕ) : Set ℕ) ⊆ Ω ∧ m ≤ S.card} := by
    ext S
    simp [A, U]
  rw [← hA, ← MeasureTheory.sum_measureReal_singleton]
  rw [Finset.sum_congr rfl fun S hS =>
    binomialFinsetSubset_real_singleton_nat_of_subset p hΩ (by
      have hSU : S ⊆ U := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
      simpa [U] using hSU)]
  have hcardU : U.card = Ω.ncard := by
    exact (Set.ncard_eq_toFinset_card Ω hΩ).symm
  have hmaps : ∀ S ∈ A, S.card ∈ Finset.Icc m U.card := by
    intro S hS
    simp only [A, Finset.mem_filter, Finset.mem_powerset] at hS
    exact Finset.mem_Icc.mpr ⟨hS.2, Finset.card_le_card hS.1⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun S : Finset ℕ =>
    (p : ℝ) ^ S.card * (1 - (p : ℝ)) ^ (Ω.ncard - S.card))]
  unfold binomialUpperTail
  apply Finset.sum_congr
  · simp [hcardU]
  · intro k hk
    have hfiber : (A.filter fun S => S.card = k) = U.powersetCard k := by
      ext S
      have hmk : m ≤ k := (Finset.mem_Icc.mp hk).1
      simp only [A, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hSU, hmS⟩, hSk⟩
        exact ⟨hSU, hSk⟩
      · rintro ⟨hSU, hSk⟩
        exact ⟨⟨hSU, hSk ▸ hmk⟩, hSk⟩
    rw [hfiber]
    rw [Finset.sum_congr rfl fun S hS => by
      rw [(Finset.mem_powersetCard.mp hS).2]]
    simp [Finset.card_powersetCard, hcardU, nsmul_eq_mul]
    ring

/-- The dense-set event in the main argument is exactly a binomial upper tail. -/
private lemma binomialFinsetSubset_real_dense_event_eq_upperTail
    (n : ℕ) (δ : unitInterval) :
    (binomialFinsetSubset (Set.Icc 1 n) δ).real
        {S : Finset ℕ | S ⊆ interval n ∧
          (δ : ℝ) * (n : ℝ) ≤ (S.card : ℝ)} =
      binomialUpperTail n ⌈(δ : ℝ) * (n : ℝ)⌉₊ δ := by
  have hevent :
      {S : Finset ℕ | S ⊆ interval n ∧
          (δ : ℝ) * (n : ℝ) ≤ (S.card : ℝ)} =
        {S : Finset ℕ | ((S : Finset ℕ) : Set ℕ) ⊆ Set.Icc 1 n ∧
          ⌈(δ : ℝ) * (n : ℝ)⌉₊ ≤ S.card} := by
    ext S
    simp only [Set.mem_setOf_eq]
    have hsubset :
        S ⊆ interval n ↔ ((S : Finset ℕ) : Set ℕ) ⊆ Set.Icc 1 n := by
      unfold interval
      constructor
      · intro hS x hx
        simpa only [Finset.mem_Icc, Set.mem_Icc] using hS hx
      · intro hS x hx
        simpa only [Finset.mem_Icc, Set.mem_Icc] using hS hx
    constructor
    · rintro ⟨hS, hcard⟩
      exact ⟨hsubset.mp hS, Nat.ceil_le.mpr hcard⟩
    · rintro ⟨hS, hcard⟩
      exact ⟨hsubset.mpr hS, Nat.ceil_le.mp hcard⟩
  rw [hevent]
  simpa using binomialFinsetSubset_real_card_ge_eq_upperTail
    (Set.finite_Icc 1 n) δ ⌈(δ : ℝ) * (n : ℝ)⌉₊

/-- The random Bernoulli subset has cardinality at least its mean, when the mean is at least three,
with probability at least one quarter. -/
theorem binomialFinsetSubset_real_dense_event_ge_quarter (n : ℕ) (δ : unitInterval)
    (hmean : (3 : ℝ) ≤ (δ : ℝ) * (n : ℝ)) :
    (1 / 4 : ℝ) ≤
      (binomialFinsetSubset (Set.Icc 1 n) δ).real
        {S : Finset ℕ | S ⊆ interval n ∧
          (δ : ℝ) * (n : ℝ) ≤ (S.card : ℝ)} := by
  rw [binomialFinsetSubset_real_dense_event_eq_upperTail]
  exact one_fourth_le_binomialUpperTail_of_three_le_mean n δ hmean

end

end DenseSetsWithoutLargeSumsets
