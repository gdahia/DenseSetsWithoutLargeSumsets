/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DenseSetsWithoutLargeSumsets.CountingSumsetsOfModerateSize.Enumeration
public import DenseSetsWithoutLargeSumsets.Probability
import DenseSetsWithoutLargeSumsets.SimpleBoundForVeryLargeSumsets
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# The probability that a random set contains a sumset of moderate size

Let `S` be the random subset of `[n]` that contains each element independently with probability
`δ`, and let `k = ⌈(2 + γ) * log n / log (1 / δ)⌉`. We bound the probability that `S` contains a
sumset `A + B` with `A, B ⊆ [n]`, `|A| = |B| = k` and `C * k < |A + B| < k * (k + 1) / 2`. The proof
is a union bound over the sets `Y = A + B`, which are counted in `Enumeration`. For
`|Y| ≤ k ^ (1 + ξ)` with `ξ = 2⁻⁸` we use the count for sets of small doubling, and for larger `Y`
the general count. This is Section 3 of *Dense sets without large sumsets* (Dahia, Marciano,
Souza).

## Main definitions

* `moderateSumsetEvent n k C S`: the set `S` contains a sumset `A + B` as above.
* `moderateSumsetGapConstant γ c`: the constant `C`.
* `moderateSumsetDensityExponent γ c`: the exponent `α` for which the bound holds when
  `δ > n ^ (-α)`.

## Main statements

* `moderate_sumset_probability_le`: if `0 < γ ≤ 2`, `n ≥ 2` and `n ^ (-α) < δ ≤ 1 - c`, then the
  probability of `moderateSumsetEvent n k C` is at most `2 * k ^ 2 / n ^ (γ * C / 2)`.
-/

@[expose] public section

namespace DenseSetsWithoutLargeSumsets

open Finset MeasureTheory CountingSetsWithSmallSumset
open scoped Pointwise

noncomputable section

/-- The set `S` contains a sumset `A + B` of two `k`-subsets `A`, `B` of `[n]` with
`C * k < |A + B| < k * (k + 1) / 2`. -/
def moderateSumsetEvent (n k : ℕ) (C : ℝ) (S : Finset ℕ) : Prop :=
  ∃ A B : Finset ℕ,
    A ⊆ interval n ∧ B ⊆ interval n ∧ #A = k ∧ #B = k ∧
      C * (k : ℝ) < (#(A + B) : ℝ) ∧
        #(A + B) < k * (k + 1) / 2 ∧ A + B ⊆ S

/-- The sizes `m` with `C * k < m < k * (k + 1) / 2`. -/
private def moderateSumsetCardRange (k : ℕ) (C : ℝ) : Finset ℕ :=
  (range (k * (k + 1) / 2)).filter fun m ↦ C * k < m

private lemma mem_moderateSumsetCardRange {k m : ℕ} {C : ℝ} :
    m ∈ moderateSumsetCardRange k C ↔ m < k * (k + 1) / 2 ∧ C * k < m := by
  simp [moderateSumsetCardRange]

private lemma card_moderateSumsetCardRange_le (k : ℕ) (C : ℝ) :
    (#(moderateSumsetCardRange k C) : ℝ) ≤ 2 * (k : ℝ) ^ 2 := by
  have h := (card_filter_le (range (k * (k + 1) / 2)) fun m : ℕ ↦ C * k < m).trans_eq
    (card_range _)
  exact mod_cast h.trans (Nat.div_le_of_le_mul (by nlinarith [Nat.le_mul_self k]))

private lemma finite_pairSumsetsFamily (n k m : ℕ) : (pairSumsetsFamily n k m).Finite :=
  (interval (2 * n)).powerset.finite_toSet.subset fun _ hY ↦ mem_powerset.2 hY.1

private lemma add_subset_interval {n : ℕ} {A B : Finset ℕ} (hA : A ⊆ interval n)
    (hB : B ⊆ interval n) : A + B ⊆ interval (2 * n) := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hx
  grind [interval]

/-- The union bound over the sets `Y = A + B` of each size `m`. A fixed `Y` is contained in the
random set with probability at most `δ ^ |Y|`. -/
private lemma measureReal_moderateSumsetEvent_le_sum (n k : ℕ) (C : ℝ) (δ : unitInterval) :
    (binomialFinsetSubset (Set.Icc 1 n) δ).real {S | moderateSumsetEvent n k C S} ≤
      ∑ m ∈ moderateSumsetCardRange k C, ((pairSumsetsFamily n k m).ncard : ℝ) * (δ : ℝ) ^ m := by
  have hsub : {S | moderateSumsetEvent n k C S} ⊆ ⋃ m ∈ moderateSumsetCardRange k C,
      ⋃ Y ∈ (finite_pairSumsetsFamily n k m).toFinset.filter (#· = m),
        {S : Finset ℕ | Y ⊆ S} := by
    rintro S ⟨A, B, hA, hB, hAk, hBk, hlo, hhi, hS⟩
    refine Set.mem_iUnion₂.2 ⟨#(A + B), mem_moderateSumsetCardRange.2 ⟨hhi, hlo⟩,
      Set.mem_iUnion₂.2 ⟨A + B, ?_, hS⟩⟩
    rw [mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨add_subset_interval hA hB, A, B, hA, hB, hAk, hBk, rfl, le_rfl⟩, rfl⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le _ _).trans ?_)
  gcongr with m
  refine (measureReal_biUnion_finset_le _ _).trans
    ((sum_le_card_nsmul _ _ ((δ : ℝ) ^ m) ?_).trans ?_)
  · intro Y hY
    obtain ⟨-, hYm⟩ := mem_filter.1 hY
    rw [← hYm]
    exact binomialFinsetSubset_real_superset_nat δ (Set.finite_Icc 1 n)
  rw [nsmul_eq_mul, Set.ncard_eq_toFinset_card _ (finite_pairSumsetsFamily n k m)]
  gcongr
  · exact pow_nonneg (unitInterval.nonneg δ) m
  · exact filter_subset _ _

private lemma measureReal_moderateSumsetEvent_le {n k : ℕ} {C B : ℝ} {δ : unitInterval}
    (hB : 0 ≤ B) (h : ∀ m ∈ moderateSumsetCardRange k C,
      ((pairSumsetsFamily n k m).ncard : ℝ) * (δ : ℝ) ^ m ≤ B) :
    (binomialFinsetSubset (Set.Icc 1 n) δ).real {S | moderateSumsetEvent n k C S} ≤
      2 * (k : ℝ) ^ 2 * B := by
  refine (measureReal_moderateSumsetEvent_le_sum n k C δ).trans
    ((sum_le_card_nsmul _ _ _ h).trans ?_)
  rw [nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (card_moderateSumsetCardRange_le k C) hB

private lemma log_six_mul_exp_one_le : Real.log (6 * Real.exp 1) ≤ 3 := by
  have h := Real.log_le_log (by norm_num)
    (by nlinarith [Real.exp_one_gt_d9] : (6 : ℝ) ≤ Real.exp 1 ^ 2)
  rw [Real.log_pow, Real.log_exp] at h
  rw [Real.log_mul (by norm_num) (Real.exp_pos 1).ne', Real.log_exp]
  push_cast at h
  linarith

private lemma pow_mul_exp_le_exp {k : ℕ} {q c : ℝ} (hk : 1 ≤ k) (hq₀ : 0 < q)
    (hq : 4 ≤ Real.log q) (hc : 0 ≤ c) :
    (6 * Real.exp 1 * q) ^ (6 * k) * Real.exp ((k : ℝ) ^ (1 - 2 * c)) ≤
      Real.exp (12 * k * Real.log q) := by
  have hk₁ : (1 : ℝ) ≤ k := mod_cast hk
  have hlog : Real.log (6 * Real.exp 1 * q) ≤ 3 + Real.log q := by
    rw [Real.log_mul (by positivity) hq₀.ne']
    linarith [log_six_mul_exp_one_le]
  have hkc : (k : ℝ) ^ (1 - 2 * c) ≤ k :=
    (Real.rpow_le_rpow_of_exponent_le hk₁ (by linarith)).trans_eq (Real.rpow_one _)
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity), ← Real.exp_add, Real.exp_le_exp]
  push_cast
  linarith [mul_le_mul_of_nonneg_right hlog (by positivity : 0 ≤ 6 * (k : ℝ)),
    mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ (k : ℝ))]

/-- If `N ≤ n ^ (2 * q + 1) * F` with `F ≤ exp E` and `x ≤ n ^ (-(2 + γ) * q)`, where `q ≥ C` and
`E + log n ≤ γ * q / 2 * log n`, then `N * x ≤ n ^ (-(γ * C / 2))`. -/
private lemma mul_le_rpow_neg {γ C q E F N x : ℝ} {n : ℕ} (hγ : 0 < γ) (hn : 1 < n) (hC : C ≤ q)
    (hE : E + Real.log n ≤ γ * q / 2 * Real.log n) (hF₀ : 0 ≤ F) (hF : F ≤ Real.exp E)
    (hN : N ≤ (n : ℝ) ^ (2 * q + 1) * F) (hx₀ : 0 ≤ x) (hx : x ≤ (n : ℝ) ^ (-(2 + γ) * q)) :
    N * x ≤ (n : ℝ) ^ (-(γ * C / 2)) := by
  have hn₀ : (0 : ℝ) < n := by positivity
  have hL : 0 < Real.log n := Real.log_pos (mod_cast hn)
  refine (mul_le_mul hN hx hx₀ (by positivity)).trans ?_
  refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF (by positivity))
    (by positivity)).trans ?_
  rw [Real.rpow_def_of_pos hn₀, Real.rpow_def_of_pos hn₀, Real.rpow_def_of_pos hn₀,
    ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  linarith [mul_le_mul_of_nonneg_right hC (mul_nonneg hγ.le hL.le)]

/-- The constant `C = exp (96 * q / γ)`, where `q = densityCoefficient (2 + γ) c`. The sumsets of
moderate size are those with more than `C * k` elements. -/
def moderateSumsetGapConstant (γ c : ℝ) : ℝ :=
  Real.exp (96 * densityCoefficient (2 + γ) c / γ)

lemma one_le_moderateSumsetGapConstant {γ c : ℝ} (hγ_pos : 0 < γ)
    (hc_pos : 0 < c) (hc_lt : c < 1) :
    1 ≤ moderateSumsetGapConstant γ c := by
  have hQ := densityCoefficient_gt_one (τ := 2 + γ) (by linarith) hc_pos hc_lt
  exact Real.one_le_exp (by positivity)

private lemma mul_log_add_one_le {γ Q q : ℝ} (hγ : 0 < γ) (hγ_le : γ ≤ 2) (hQ : 1 < Q)
    (hq : Real.exp (96 * Q / γ) ≤ q) : 12 * Q * Real.log q + 1 ≤ γ * q / 2 := by
  obtain ⟨a, rfl⟩ : ∃ a, Q = a * γ / 96 := ⟨96 * Q / γ, by field_simp⟩
  rw [(by field_simp : 96 * (a * γ / 96) / γ = a)] at hq
  have ha : 48 ≤ a := by nlinarith
  have hq' : a + 1 ≤ q := (Real.add_one_le_exp a).trans hq
  have hℓ : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  have hratio : Real.log q / q ≤ Real.log (Real.exp a) / Real.exp a :=
    Real.log_div_self_antitoneOn (Real.exp_le_exp.2 (by linarith))
      ((Real.exp_le_exp.2 (by linarith)).trans hq) hq
  rw [Real.log_exp, div_le_div_iff₀ (by linarith) (Real.exp_pos a)] at hratio
  have h : Real.log q * a ≤ 2 * q := by
    nlinarith [mul_nonneg hℓ (sub_nonneg.2 (Real.quadratic_le_exp_of_nonneg
      (by linarith : 0 ≤ a))), mul_nonneg hℓ (by linarith : 0 ≤ a)]
  linarith [mul_le_mul_of_nonneg_left h hγ.le, mul_le_mul_of_nonneg_left hq' hγ.le]

/-- The bound for the sumsets with at most `k ^ (1 + ξ)` elements. -/
private lemma ncard_mul_pow_le_of_le_rpow {γ c : ℝ} {n k m : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hγ_le : γ ≤ 2) (hc_pos : 0 < c) (hc_lt : c < 1) (hn : 1 < n) (hk : 1 ≤ k)
    (hδ : (δ : ℝ) ^ m ≤ (n : ℝ) ^ (-(2 + γ) * m / k))
    (hkL : (k : ℝ) ≤ densityCoefficient (2 + γ) c * Real.log n)
    (hk_large : smallSumsetClassCountThreshold ≤ k)
    (hm : m ∈ moderateSumsetCardRange k (moderateSumsetGapConstant γ c))
    (hm_small : (m : ℝ) ≤ (k : ℝ) ^ (1 + moderateSumsetAuxExponent)) :
    ((pairSumsetsFamily n k m).ncard : ℝ) * (δ : ℝ) ^ m ≤
      (n : ℝ) ^ (-(γ * moderateSumsetGapConstant γ c / 2)) := by
  obtain ⟨hm_lt, hCm⟩ := mem_moderateSumsetCardRange.1 hm
  have hk₀ : (0 : ℝ) < k := mod_cast hk
  have hL : 0 < Real.log n := Real.log_pos (mod_cast hn)
  have hQ := densityCoefficient_gt_one (τ := 2 + γ) (by linarith) hc_pos hc_lt
  have hC : moderateSumsetGapConstant γ c ≤ m / k := ((lt_div_iff₀ hk₀).2 hCm).le
  have hq₀ : (0 : ℝ) < m / k := (Real.exp_pos _).trans_le hC
  have hlogq : 48 ≤ Real.log (m / k) := by
    rw [Real.le_log_iff_exp_le hq₀]
    refine le_trans (Real.exp_le_exp.2 ?_) hC
    rw [le_div_iff₀ hγ_pos]
    linarith
  have hratio := mul_log_add_one_le hγ_pos hγ_le hQ hC
  have hcount := pairSumsetsFamily_ncard_le_of_small_sumset n k m _ hm_lt le_rfl hk_large hm_small
  rw [mul_assoc] at hcount
  simp only [mul_div_assoc] at hcount hδ
  refine mul_le_rpow_neg hγ_pos hn hC ?_ (by positivity) (pow_mul_exp_le_exp hk hq₀
    (by linarith) (by norm_num [moderateSumsetAuxExponent])) hcount (pow_nonneg δ.2.1 m) hδ
  linarith [mul_le_mul_of_nonneg_right hkL (by linarith : 0 ≤ Real.log (m / k)),
    mul_le_mul_of_nonneg_right hratio hL.le]

/-- The bound for the sumsets with more than `k ^ (1 + ξ)` elements. -/
private lemma ncard_mul_pow_le_of_rpow_lt {γ c : ℝ} {n k m : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hn : 1 < n) (hk : 1 ≤ k)
    (hδ : (δ : ℝ) ^ m ≤ (n : ℝ) ^ (-(2 + γ) * m / k))
    (hm : m ∈ moderateSumsetCardRange k (moderateSumsetGapConstant γ c))
    (hm_large : (k : ℝ) ^ (1 + moderateSumsetAuxExponent) < m)
    (hC : moderateSumsetGapConstant γ c ≤ (k : ℝ) ^ moderateSumsetAuxExponent)
    (hlog : 24 * k * Real.log k + Real.log n ≤
      γ / 2 * (k : ℝ) ^ moderateSumsetAuxExponent * Real.log n) :
    ((pairSumsetsFamily n k m).ncard : ℝ) * (δ : ℝ) ^ m ≤
      (n : ℝ) ^ (-(γ * moderateSumsetGapConstant γ c / 2)) := by
  have hk₀ : (0 : ℝ) < k := mod_cast hk
  have hL : 0 < Real.log n := Real.log_pos (mod_cast hn)
  have hq : (k : ℝ) ^ moderateSumsetAuxExponent ≤ m / k := by
    rw [le_div_iff₀ hk₀, ← Real.rpow_add_one hk₀.ne', add_comm]
    exact hm_large.le
  have hcount := pairSumsetsFamily_ncard_le n k m (mem_moderateSumsetCardRange.1 hm).1
  simp only [mul_div_assoc] at hcount hδ
  refine mul_le_rpow_neg (E := 24 * k * Real.log k) hγ_pos hn (hC.trans hq) ?_ (by positivity)
    (le_of_eq ?_) hcount (pow_nonneg δ.2.1 m) hδ
  · linarith [mul_le_mul_of_nonneg_right hq (mul_nonneg hγ_pos.le hL.le)]
  · rw [← Real.rpow_natCast, Real.rpow_def_of_pos hk₀]
    push_cast
    ring_nf

/-- A lower bound for `k = pairCardThreshold (2 + γ) n δ` under which the estimates of this file
hold. -/
def moderateSumsetCardScale (γ c : ℝ) : ℝ :=
  max (smallSumsetClassCountThreshold : ℝ)
    (max
      ((max (2 * moderateSumsetGapConstant γ c) ((4 : ℝ) / γ)) ^ ((2 : ℝ) ^ (8 : ℕ)))
      (((49152 * densityCoefficient (2 + γ) c) / γ) ^ ((2 : ℝ) ^ (9 : ℕ))))

/-- The exponent `α = (2 + γ) / (2 * R)`, where `R = moderateSumsetCardScale γ c`. If
`δ > n ^ (-α)`, then `pairCardThreshold (2 + γ) n δ ≥ R`. -/
def moderateSumsetDensityExponent (γ c : ℝ) : ℝ :=
  (2 + γ) / (2 * moderateSumsetCardScale γ c)

private lemma moderateSumsetCardScale_pos (γ c : ℝ) : 0 < moderateSumsetCardScale γ c :=
  lt_max_of_lt_left (mod_cast smallSumsetClassCountThreshold_pos)

lemma moderateSumsetDensityExponent_pos {γ c : ℝ} (hγ_pos : 0 < γ) :
    0 < moderateSumsetDensityExponent γ c :=
  div_pos (by linarith) (mul_pos two_pos (moderateSumsetCardScale_pos γ c))

private lemma moderateSumsetCardScale_bounds {γ c : ℝ} (hγ_pos : 0 < γ) (hc_pos : 0 < c)
    (hc_lt : c < 1) {k : ℕ} (hscale : moderateSumsetCardScale γ c ≤ (k : ℝ)) :
    smallSumsetClassCountThreshold ≤ k ∧
      2 * moderateSumsetGapConstant γ c ≤ (k : ℝ) ^ moderateSumsetAuxExponent ∧
        (4 : ℝ) / γ ≤ (k : ℝ) ^ moderateSumsetAuxExponent ∧
          (49152 * densityCoefficient (2 + γ) c) / γ ≤
            (k : ℝ) ^ (moderateSumsetAuxExponent / 2) := by
  have hQ := densityCoefficient_gt_one (τ := 2 + γ) (by linarith) hc_pos hc_lt
  rw [moderateSumsetCardScale, max_le_iff, max_le_iff,
    ← Real.le_rpow_inv_iff_of_pos (le_max_of_le_right (by positivity)) (by positivity)
      (by positivity),
    ← Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by positivity)] at hscale
  obtain ⟨hT, hA, hB⟩ := hscale
  rw [moderateSumsetAuxExponent, one_div,
    (by norm_num : ((2 : ℝ) ^ (8 : ℕ))⁻¹ / 2 = ((2 : ℝ) ^ (9 : ℕ))⁻¹)]
  exact ⟨mod_cast hT, (le_max_left _ _).trans hA, (le_max_right _ _).trans hA, hB⟩

private lemma le_pairCardThreshold {τ R α : ℝ} {n : ℕ} {δ : unitInterval} (hτ : 0 < τ)
    (hR : 0 < R) (hα : α = τ / (2 * R)) (hn : 1 < n) (hδ_lt : (δ : ℝ) < 1)
    (hδ : (n : ℝ) ^ (-α) < (δ : ℝ)) : R ≤ (pairCardThreshold τ n δ : ℝ) := by
  have hn₀ : (0 : ℝ) < n := by positivity
  have hL : 0 < Real.log n := Real.log_pos (mod_cast hn)
  have hδ₀ : (0 : ℝ) < δ := (Real.rpow_pos_of_pos hn₀ _).trans hδ
  have h := Real.log_lt_log (Real.rpow_pos_of_pos hn₀ _) hδ
  rw [Real.log_rpow hn₀, hα, neg_mul, neg_lt, div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    at h
  refine le_trans ?_ (Nat.le_ceil _)
  rw [le_div_iff₀ (Real.log_pos ((one_lt_div hδ₀).2 hδ_lt)), one_div, Real.log_inv]
  linarith [mul_pos hτ hL]

private lemma mul_log_add_log_le {γ Q : ℝ} {n k : ℕ} (hγ : 0 < γ) (hQ : 0 < Q) (hn : 1 < n)
    (hk : 1 ≤ k) (hkL : (k : ℝ) ≤ Q * Real.log n)
    (h4 : 4 / γ ≤ (k : ℝ) ^ moderateSumsetAuxExponent)
    (hB : 49152 * Q / γ ≤ (k : ℝ) ^ (moderateSumsetAuxExponent / 2)) :
    24 * k * Real.log k + Real.log n ≤
      γ / 2 * (k : ℝ) ^ moderateSumsetAuxExponent * Real.log n := by
  have hk₁ : (1 : ℝ) ≤ k := mod_cast hk
  have hL : 0 < Real.log n := Real.log_pos (mod_cast hn)
  have hlog : Real.log k ≤ 512 * (k : ℝ) ^ (moderateSumsetAuxExponent / 2) := by
    refine (Real.log_le_rpow_div (ε := moderateSumsetAuxExponent / 2) (by positivity)
      (by norm_num [moderateSumsetAuxExponent])).trans_eq ?_
    norm_num [moderateSumsetAuxExponent]
    ring
  have hsq : (k : ℝ) ^ (moderateSumsetAuxExponent / 2) *
      (k : ℝ) ^ (moderateSumsetAuxExponent / 2) = (k : ℝ) ^ moderateSumsetAuxExponent := by
    rw [← Real.rpow_add (by positivity), add_halves]
  rw [div_le_iff₀ hγ] at h4 hB
  rw [← hsq] at h4 ⊢
  have ha : 0 ≤ (k : ℝ) ^ (moderateSumsetAuxExponent / 2) := by positivity
  linarith [mul_le_mul_of_nonneg_right hkL (Real.log_nonneg hk₁),
    mul_le_mul_of_nonneg_left hlog (mul_nonneg hQ.le hL.le),
    mul_le_mul_of_nonneg_right hB (mul_nonneg ha hL.le), mul_le_mul_of_nonneg_right h4 hL.le]

lemma pairCardThreshold_ge_two_of_density_lower {τ α : ℝ} {n : ℕ}
    {δ : unitInterval} (hτ_pos : 0 < τ) (hα_le : α ≤ τ / 4)
    (hn : 1 < n) (hδ_lt : (δ : ℝ) < 1)
    (hδ_lower : Real.rpow (n : ℝ) (-α) < (δ : ℝ)) :
    2 ≤ pairCardThreshold τ n δ := by
  refine Nat.ofNat_le_cast.1 (le_pairCardThreshold hτ_pos two_pos
    (by ring : τ / 4 = τ / (2 * 2)) hn hδ_lt (lt_of_le_of_lt ?_ hδ_lower))
  exact Real.rpow_le_rpow_of_exponent_le (mod_cast hn.le) (neg_le_neg hα_le)

/-- Let `0 < γ ≤ 2`, `n ≥ 2` and `n ^ (-α) < δ ≤ 1 - c`, where
`α = moderateSumsetDensityExponent γ c`. Let `k = pairCardThreshold (2 + γ) n δ` and
`C = moderateSumsetGapConstant γ c`. The random subset of `[n]` of density `δ` contains a sumset
`A + B` with `A, B ⊆ [n]`, `|A| = |B| = k` and `C * k < |A + B| < k * (k + 1) / 2` with
probability at most `2 * k ^ 2 / n ^ (γ * C / 2)`. -/
lemma moderate_sumset_probability_le
    {γ c : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 2) (hc_pos : 0 < c)
    {n : ℕ} (hn_two : 2 ≤ n)
    {δ : unitInterval}
    (hδ_lower : (n : ℝ) ^ (-moderateSumsetDensityExponent γ c) < (δ : ℝ))
    (hδ_upper : (δ : ℝ) ≤ 1 - c) :
    let k := pairCardThreshold (2 + γ) n δ
    let C := moderateSumsetGapConstant γ c
    let ℙ : MeasureTheory.Measure (Finset ℕ) := binomialFinsetSubset (Set.Icc 1 n) δ
    ℙ.real {S : Finset ℕ | moderateSumsetEvent n k C S} ≤
      2 * (k : ℝ) ^ 2 / (n : ℝ) ^ (γ * C / 2) := by
  intro k C ℙ
  have hn₀ : (0 : ℝ) < n := by positivity
  have hδ_pos : 0 < (δ : ℝ) := (Real.rpow_pos_of_pos hn₀ _).trans hδ_lower
  have hc_lt : c < 1 := by linarith
  have hδ_lt : (δ : ℝ) < 1 := by linarith
  have hscale : moderateSumsetCardScale γ c ≤ k := le_pairCardThreshold (by linarith)
    (moderateSumsetCardScale_pos γ c) rfl hn_two hδ_lt hδ_lower
  have hk : 1 ≤ k := Nat.cast_pos.1 ((moderateSumsetCardScale_pos γ c).trans_le hscale)
  obtain ⟨hk_large, hC, h4, hB⟩ := moderateSumsetCardScale_bounds hγ_pos hc_pos hc_lt hscale
  have hkL := pairCardThreshold_le_densityCoefficient_mul_log (τ := 2 + γ) (by linarith) hc_pos
    hn_two hδ_pos hδ_upper
  have hQ := densityCoefficient_gt_one (τ := 2 + γ) (by linarith) hc_pos hc_lt
  rw [div_eq_mul_inv, ← Real.rpow_neg hn₀.le]
  refine measureReal_moderateSumsetEvent_le (by positivity) ?_
  intro m hm
  have hδ := unitInterval_pow_le_exp_div_mul_log n m (2 + γ) δ hδ_pos hδ_lt hn_two hk
  obtain hm_small | hm_large := le_or_gt (m : ℝ) ((k : ℝ) ^ (1 + moderateSumsetAuxExponent))
  · exact ncard_mul_pow_le_of_le_rpow hγ_pos hγ_le hc_pos hc_lt hn_two hk hδ hkL hk_large hm
      hm_small
  · exact ncard_mul_pow_le_of_rpow_lt hγ_pos hn_two hk hδ hm hm_large
      (by linarith [one_le_moderateSumsetGapConstant hγ_pos hc_pos hc_lt])
      (mul_log_add_log_le hγ_pos (by linarith) hn_two hk hkL h4 hB)

end

end DenseSetsWithoutLargeSumsets
