/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.SumsetFromZarankiewicz
import DenseSetsWithoutLargeSumsets.DenseSubsetsWithoutLargeSumsets

/-!
# The threshold function `φ (δ, N)`

Following the introduction of *Dense sets without large sumsets*, we let `φ δ N` be the largest
integer `k` such that **every** `A ⊆ [N]` with `#A ≥ δ N` contains a sumset `B + C` with
`B, C ⊆ [N]` and `min {#B, #C} ≥ k`.  The condition defining `k` is `pairEvent N k`, so `φ δ N` is
the supremum of `sumsetThresholdSet δ N`; that set is downward closed, contains `0`, and is
bounded above by `N`, so the supremum is attained and `φ` deserves the name "largest integer".

The point of the definition is that the two directions formalized in this project are exactly upper
and lower bounds on `φ`:

* `dense_subset_without_large_sumsets` exhibits a dense set with no large sumset, hence *upper*
  bounds `φ` — this is `eventually_phi_lt_pairCardThreshold` below, whose asymptotic form is
  `limsup_phi_mul_log_div_log_le_three`:
  `limsup_N φ(δ, N) log (1 / δ) / log N ≤ 3` for every constant density `δ ∈ (0, 1)`.
* `pairEvent_of_zarankiewicz_lt_density` shows every dense set does contain a large sumset, hence
  *lower* bounds `φ` — this is `le_phi_of_zarankiewicz_lt` below.

The asymptotic statement bounds the `limsup` and not just the `liminf` because
`dense_subset_without_large_sumsets` produces a dense subset of `[N]` with no large sumset for
*every* sufficiently large `N`: the resulting bound on `φ(δ, N)` holds eventually, not merely
infinitely often.

The last section is the *upper* half of Corollary 1.2 of the paper, which sandwiches `φ` between
`(1 - γ) / log (1 / δ)` and `(3 + γ) / log (1 / δ)` and thereby settles Conjecture 4.10 and answers
Question 4.12 of Bryna Kra, Joel Moreira, Florian K. Richter and Donald Robertson, *Problems on
infinite sumset configurations in the integers and beyond* (Bull. Amer. Math. Soc. **62** (2025),
537--574, arXiv:2311.06197), in the negative.  The lower half of the sandwich is quoted in the paper
from Hernández and Hetzel and is not formalized here.  The two readings Corollary 1.2 records are
`limsup_phi_div_log_le` (Conjecture 4.10) and `liminf_phi_div_log_eq_zero` together with
`liminf_phi_logDensity_div_log_eq_zero` (Question 4.12).
-/

namespace DenseSetsWithoutLargeSumsets

open Filter

open scoped Pointwise

noncomputable section

/-- The set of `k` such that every `S ⊆ [N]` with `#S ≥ δ N` contains a sumset `B + C` with
`B, C ⊆ [N]` and `min {#B, #C} ≥ k`. -/
def sumsetThresholdSet (δ : unitInterval) (N : ℕ) : Set ℕ :=
  {k | ∀ S : Finset ℕ, S ⊆ interval N → (δ : ℝ) * (N : ℝ) ≤ (S.card : ℝ) → pairEvent N k S}

/-- `φ δ N`, the largest integer `k` such that every `A ⊆ [N]` with `#A ≥ δ N` contains a sumset
`B + C` with `B, C ⊆ [N]` and `min {#B, #C} ≥ k`. -/
def phi (δ : unitInterval) (N : ℕ) : ℕ := sSup (sumsetThresholdSet δ N)

section Basic

variable {δ : unitInterval} {N k l : ℕ}

/-- `sumsetThresholdSet` is downward closed: asking for a *larger* common size is a stronger
requirement. -/
lemma sumsetThresholdSet_of_le (hkl : k ≤ l) (hl : l ∈ sumsetThresholdSet δ N) :
    k ∈ sumsetThresholdSet δ N := by
  intro S hS hcard
  obtain ⟨A, B, hA, hB, hAcard, hBcard, hAB⟩ := hl S hS hcard
  exact ⟨A, B, hA, hB, hkl.trans hAcard, hkl.trans hBcard, hAB⟩

lemma zero_mem_sumsetThresholdSet (δ : unitInterval) (N : ℕ) :
    0 ∈ sumsetThresholdSet δ N := fun _ _ _ =>
  ⟨∅, ∅, Finset.empty_subset _, Finset.empty_subset _, Nat.zero_le _, Nat.zero_le _, by simp⟩

lemma sumsetThresholdSet_nonempty (δ : unitInterval) (N : ℕ) :
    (sumsetThresholdSet δ N).Nonempty :=
  ⟨0, zero_mem_sumsetThresholdSet δ N⟩

lemma card_interval (N : ℕ) : (interval N).card = N := by
  simp [interval]

/-- Taking `S = [N]` shows that no `k > N` belongs to `sumsetThresholdSet δ N`. -/
lemma le_of_mem_sumsetThresholdSet (hk : k ∈ sumsetThresholdSet δ N) : k ≤ N := by
  have hcard : (δ : ℝ) * (N : ℝ) ≤ ((interval N).card : ℝ) := by
    rw [card_interval]
    exact mul_le_of_le_one_left (by positivity) δ.2.2
  obtain ⟨A, _, hA, _, hAcard, _, _⟩ := hk (interval N) subset_rfl hcard
  exact hAcard.trans ((Finset.card_le_card hA).trans_eq (card_interval N))

lemma bddAbove_sumsetThresholdSet (δ : unitInterval) (N : ℕ) :
    BddAbove (sumsetThresholdSet δ N) :=
  ⟨N, fun _ hk => le_of_mem_sumsetThresholdSet hk⟩

/-- The supremum defining `φ` is attained, so `φ δ N` really is the *largest* such integer. -/
lemma phi_mem_sumsetThresholdSet (δ : unitInterval) (N : ℕ) :
    phi δ N ∈ sumsetThresholdSet δ N :=
  Nat.sSup_mem (sumsetThresholdSet_nonempty δ N) (bddAbove_sumsetThresholdSet δ N)

lemma le_phi (hk : k ∈ sumsetThresholdSet δ N) : k ≤ phi δ N :=
  le_csSup (bddAbove_sumsetThresholdSet δ N) hk

lemma phi_le_of_forall_mem_le (h : ∀ l ∈ sumsetThresholdSet δ N, l ≤ k) : phi δ N ≤ k :=
  csSup_le (sumsetThresholdSet_nonempty δ N) h

lemma phi_le_self (δ : unitInterval) (N : ℕ) : phi δ N ≤ N :=
  phi_le_of_forall_mem_le fun _ hl => le_of_mem_sumsetThresholdSet hl

/-- The defining property of `φ`: every `δ`-dense `S ⊆ [N]` contains a sumset `A + B` with
`min {#A, #B} ≥ k`, for every `k ≤ φ δ N`. -/
lemma pairEvent_of_le_phi (hk : k ≤ phi δ N) {S : Finset ℕ} (hS : S ⊆ interval N)
    (hcard : (δ : ℝ) * (N : ℝ) ≤ (S.card : ℝ)) : pairEvent N k S :=
  sumsetThresholdSet_of_le hk (phi_mem_sumsetThresholdSet δ N) S hS hcard

/-- `φ δ N < k` is *exactly* the assertion that some `δ`-dense subset of `[N]` avoids all sumsets
with both summands of size at least `k`.  Upper bounds on `φ` and the constructions of
`dense_subset_without_large_sumsets` are therefore the same statement. -/
lemma phi_lt_iff_existsDenseSetWithoutLargeSumsets :
    phi δ N < k ↔ existsDenseSetWithoutLargeSumsets N k δ := by
  constructor
  · intro hlt
    by_contra hcon
    refine absurd (le_phi (δ := δ) (N := N) (k := k) fun S hS hcard => ?_) hlt.not_ge
    by_contra hpair
    exact hcon ⟨S, hS, hcard, hpair⟩
  · rintro ⟨S, hS, hcard, hpair⟩
    by_contra hle
    exact hpair (pairEvent_of_le_phi (not_lt.mp hle) hS hcard)

alias ⟨_, phi_lt_of_existsDenseSetWithoutLargeSumsets⟩ :=
  phi_lt_iff_existsDenseSetWithoutLargeSumsets

end Basic

/-! ### The lower bound coming from the Zarankiewicz function -/

/-- The Zarankiewicz lower bound of `SumsetFromZarankiewicz`, read as a lower bound on `φ`. -/
lemma le_phi_of_zarankiewicz_lt {δ : unitInterval} {N k : ℕ}
    (hz : (SimpleGraph.zarankiewicz (N.sqrt + 1) (N.sqrt + 1) k k : ℝ) + 1 < (δ : ℝ) * N) :
    k ≤ phi δ N :=
  le_phi fun _ hS hcard => pairEvent_of_zarankiewicz_lt_density hS hcard hz

/-! ### The upper bound coming from the main theorem -/

/-- The main theorem, restated as an upper bound on `φ`: for densities in the admissible range,
`φ (δ n, n) < ⌈(3 + γ) log n / log (1 / δ n)⌉` for all large `n`. -/
theorem eventually_phi_lt_pairCardThreshold
    {γ c : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hc_pos : 0 < c) (hc_lt : c < 1)
    (δ : ℕ → unitInterval)
    (hδ_lower : ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ),
      Real.rpow (n : ℝ) (-denseSubsetDensityExponent γ c) < (δ n : ℝ))
    (hδ_upper : ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ), (δ n : ℝ) ≤ 1 - c) :
    ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ),
      phi (δ n) n < pairCardThreshold (3 + γ) n (δ n) := by
  filter_upwards [dense_subset_without_large_sumsets hγ_pos hγ_le hc_pos hc_lt δ
    hδ_lower hδ_upper] with n hn
  exact phi_lt_of_existsDenseSetWithoutLargeSumsets hn

/-- The same bound with the ceiling removed. -/
theorem eventually_phi_lt_log_div_log
    {γ c : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) (hc_pos : 0 < c) (hc_lt : c < 1)
    (δ : ℕ → unitInterval)
    (hδ_lower : ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ),
      Real.rpow (n : ℝ) (-denseSubsetDensityExponent γ c) < (δ n : ℝ))
    (hδ_upper : ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ), (δ n : ℝ) ≤ 1 - c) :
    ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ),
      (phi (δ n) n : ℝ) < (3 + γ) * Real.log (n : ℝ) / Real.log (1 / (δ n : ℝ)) := by
  filter_upwards [eventually_phi_lt_pairCardThreshold hγ_pos hγ_le hc_pos hc_lt δ
    hδ_lower hδ_upper] with n hn
  exact Nat.lt_ceil.mp hn

/-! ### The asymptotic form of the upper bound -/

section Limsup

variable {δ : unitInterval}

/-- The normalized threshold `φ (δ, N) log (1 / δ) / log N` is nonnegative, which is what makes
its `limsup` well behaved. -/
lemma phi_mul_log_div_log_nonneg (δ : unitInterval) (N : ℕ) :
    0 ≤ (phi δ N : ℝ) * Real.log (1 / (δ : ℝ)) / Real.log (N : ℝ) := by
  refine div_nonneg (mul_nonneg (Nat.cast_nonneg _) ?_) (Real.log_natCast_nonneg N)
  rcases eq_or_lt_of_le δ.2.1 with hδ | hδ
  · simp [← hδ]
  · exact Real.log_nonneg ((one_le_div hδ).mpr δ.2.2)

/-- For a fixed density `δ ∈ (0, 1)` the main theorem bounds `φ (δ, N)` for all large `N`. -/
lemma eventually_phi_mul_log_div_log_le (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1)
    {γ : ℝ} (hγ_pos : 0 < γ) (hγ_le : γ ≤ 1) :
    ∀ᶠ N : ℕ in (Filter.atTop : Filter ℕ),
      (phi δ N : ℝ) * Real.log (1 / (δ : ℝ)) / Real.log (N : ℝ) ≤ 3 + γ := by
  set c : ℝ := 1 - (δ : ℝ) with hc
  have hc_pos : 0 < c := by simp only [hc]; linarith
  have hc_lt : c < 1 := by simp only [hc]; linarith
  have hα_pos : 0 < denseSubsetDensityExponent γ c :=
    denseSubsetDensityExponent_pos hγ_pos hc_pos hc_lt
  have hδ_lower : ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ),
      Real.rpow (n : ℝ) (-denseSubsetDensityExponent γ c) < (δ : ℝ) :=
    by simpa using
      ((tendsto_rpow_neg_atTop hα_pos).comp tendsto_natCast_atTop_atTop).eventually_lt_const hδ_pos
  have hδ_upper : ∀ᶠ n : ℕ in (Filter.atTop : Filter ℕ), (δ : ℝ) ≤ 1 - c :=
    .of_forall fun _ => by simp only [hc]; linarith
  have hlog_pos : 0 < Real.log (1 / (δ : ℝ)) := Real.log_pos ((one_lt_div hδ_pos).mpr hδ_lt)
  filter_upwards [eventually_phi_lt_log_div_log hγ_pos hγ_le hc_pos hc_lt (fun _ => δ)
      hδ_lower hδ_upper, Filter.eventually_ge_atTop 2] with N hN hN_two
  have hlogN_pos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hN_two)
  rw [div_le_iff₀ hlogN_pos]
  exact ((lt_div_iff₀ hlog_pos).mp hN).le

/-- **The main theorem as an asymptotic bound on `φ`.**  For every fixed density `δ ∈ (0, 1)`,
`limsup_N φ (δ, N) · log (1 / δ) / log N ≤ 3`.

This is a `limsup` and not a `liminf` bound because `dense_subset_without_large_sumsets` produces
a dense sumset-free subset of `[N]` for *every* sufficiently large `N`. -/
theorem limsup_phi_mul_log_div_log_le_three (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) :
    Filter.limsup
        (fun N : ℕ => (phi δ N : ℝ) * Real.log (1 / (δ : ℝ)) / Real.log (N : ℝ))
        (Filter.atTop : Filter ℕ) ≤ 3 := by
  have hcobdd : Filter.IsCoboundedUnder (· ≤ ·) (Filter.atTop : Filter ℕ)
      fun N : ℕ => (phi δ N : ℝ) * Real.log (1 / (δ : ℝ)) / Real.log (N : ℝ) :=
    Filter.isCoboundedUnder_le_of_le _ (phi_mul_log_div_log_nonneg δ)
  refine forall_gt_imp_ge_iff_le_of_dense.mp fun a ha => ?_
  refine Filter.limsup_le_of_le hcobdd ?_
  filter_upwards [eventually_phi_mul_log_div_log_le hδ_pos hδ_lt
    (γ := min (a - 3) 1) (lt_min (by linarith) one_pos) (min_le_right _ _)] with N hN
  exact hN.trans (by linarith [min_le_left (a - 3) (1 : ℝ)])

end Limsup

/-! ### Vanishing densities: Question 4.12 of Kra, Moreira, Richter and Robertson

Corollary 1.2 of *Dense sets without large sumsets* answers Question 4.12 of *Problems on infinite
sumset configurations in the integers and beyond* in the negative.  That question asks whether
`liminf_N φ (δ N, N) / log N > 0` for **some** sequence `δ N → 0`, and specifically whether one may
take `δ N = 1 / log N`.

Both parts are negative, and in the strongest possible form: for **every** sequence `δ N → 0` the
ratio `φ (δ N, N) / log N` tends to `0`, so its `liminf` is `0` and never positive.  Monotonicity of
`φ` in the density is what removes the restriction `δ ≥ n ^ (-α)` under which Corollary 1.2 is
stated.

The mechanism is that the bound behind `limsup_phi_mul_log_div_log_le_three` costs a factor
`log (1 / δ)`: at a fixed density `δ ∈ (0, 1)` it gives `φ (δ, N) / log N ≲ 3 / log (1 / δ)` for all
large `N`, and `log (1 / δ) → ∞` as `δ → 0`.  Since `φ` is monotone in the density, comparing a
vanishing sequence `δ N` against a small *constant* density `δ` is enough to conclude.
-/

section VanishingDensity

variable {δ δ' : unitInterval} {N : ℕ}

/-- Requiring a large sumset inside *every* `δ`-dense set is a stronger demand for smaller `δ`, so
`sumsetThresholdSet` is monotone in the density. -/
lemma sumsetThresholdSet_mono (h : (δ : ℝ) ≤ (δ' : ℝ)) :
    sumsetThresholdSet δ N ⊆ sumsetThresholdSet δ' N := fun _ hk S hS hcard =>
  hk S hS ((mul_le_mul_of_nonneg_right h (Nat.cast_nonneg N)).trans hcard)

/-- `φ` is monotone in the density. -/
lemma phi_mono (h : (δ : ℝ) ≤ (δ' : ℝ)) : phi δ N ≤ phi δ' N :=
  le_phi (sumsetThresholdSet_mono h (phi_mem_sumsetThresholdSet δ N))

lemma phi_div_log_nonneg (δ : unitInterval) (N : ℕ) :
    0 ≤ (phi δ N : ℝ) / Real.log (N : ℝ) :=
  div_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg N)

/-- At a fixed density `δ ∈ (0, 1)` the main theorem bounds `φ (δ, N) / log N` by `4 / log (1 / δ)`
for all large `N`.  This is `eventually_phi_mul_log_div_log_le` with `γ = 1`, rearranged. -/
lemma eventually_phi_div_log_le (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) :
    ∀ᶠ N : ℕ in (Filter.atTop : Filter ℕ),
      (phi δ N : ℝ) / Real.log (N : ℝ) ≤ 4 / Real.log (1 / (δ : ℝ)) := by
  have hlog_pos : 0 < Real.log (1 / (δ : ℝ)) := Real.log_pos ((one_lt_div hδ_pos).mpr hδ_lt)
  filter_upwards [eventually_phi_mul_log_div_log_le hδ_pos hδ_lt (γ := 1) one_pos le_rfl]
    with N hN
  rw [le_div_iff₀ hlog_pos, div_mul_eq_mul_div]
  linarith

/-- The upper bound of Corollary 1.2, in `limsup` form: for every fixed density `δ ∈ (0, 1)` the
ratio `φ (δ, N) / log N` stays bounded, with the explicit bound `4 / log (1 / δ)`.  This is the half
of Conjecture 4.10 of Kra, Moreira, Richter and Robertson supplied by the main theorem; the matching
lower bound of Corollary 1.2, that the ratio stays bounded *away from zero*, is quoted in the paper
from Hernández and Hetzel and is not formalized here. -/
theorem limsup_phi_div_log_le (hδ_pos : 0 < (δ : ℝ)) (hδ_lt : (δ : ℝ) < 1) :
    Filter.limsup (fun N : ℕ => (phi δ N : ℝ) / Real.log (N : ℝ)) (Filter.atTop : Filter ℕ) ≤
      4 / Real.log (1 / (δ : ℝ)) :=
  Filter.limsup_le_of_le (Filter.isCoboundedUnder_le_of_le _ (phi_div_log_nonneg δ))
    (eventually_phi_div_log_le hδ_pos hδ_lt)

/-- **Corollary 1.2 answers Question 4.12 in the negative.**  For *every* sequence of densities
`δ N → 0` the normalized threshold `φ (δ N, N) / log N` tends to `0`. -/
theorem tendsto_phi_div_log_atTop_nhds_zero (δ : ℕ → unitInterval)
    (hδ : Filter.Tendsto (fun N : ℕ => (δ N : ℝ)) (Filter.atTop : Filter ℕ) (nhds 0)) :
    Filter.Tendsto (fun N : ℕ => (phi (δ N) N : ℝ) / Real.log (N : ℝ))
      (Filter.atTop : Filter ℕ) (nhds 0) := by
  refine tendsto_order.mpr ⟨fun a ha => .of_forall fun N => ha.trans_le (phi_div_log_nonneg _ _),
    fun a ha => ?_⟩
  -- Compare `δ N` with the constant density `x = exp (-(8 / a))`, chosen so that
  -- `4 / log (1 / x) = a / 2 < a`.
  have ha' : (0 : ℝ) < 8 / a := by positivity
  set x : ℝ := Real.exp (-(8 / a)) with hx_def
  have hx_pos : 0 < x := Real.exp_pos _
  have hx_lt : x < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha')
  have hx_log : Real.log (1 / x) = 8 / a := by
    rw [one_div, Real.log_inv, hx_def, Real.log_exp, neg_neg]
  set y : unitInterval := ⟨x, hx_pos.le, hx_lt.le⟩ with hy_def
  have hy_coe : (y : ℝ) = x := rfl
  filter_upwards [hδ.eventually_lt_const hx_pos,
    eventually_phi_div_log_le (δ := y) (hy_coe ▸ hx_pos) (hy_coe ▸ hx_lt),
    Filter.eventually_ge_atTop 2] with N hsmall hbound hN_two
  have hlogN_pos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hN_two)
  have hmono : (phi (δ N) N : ℝ) / Real.log (N : ℝ) ≤ (phi y N : ℝ) / Real.log (N : ℝ) := by
    gcongr
    exact_mod_cast phi_mono (δ := δ N) (δ' := y) (hy_coe ▸ hsmall.le)
  rw [hy_coe, hx_log] at hbound
  have : (4 : ℝ) / (8 / a) = a / 2 := by field_simp; norm_num
  linarith

/-- Question 4.12 verbatim: the `liminf` in question is `0`, never positive. -/
theorem liminf_phi_div_log_eq_zero (δ : ℕ → unitInterval)
    (hδ : Filter.Tendsto (fun N : ℕ => (δ N : ℝ)) (Filter.atTop : Filter ℕ) (nhds 0)) :
    Filter.liminf (fun N : ℕ => (phi (δ N) N : ℝ) / Real.log (N : ℝ))
      (Filter.atTop : Filter ℕ) = 0 :=
  (tendsto_phi_div_log_atTop_nhds_zero δ hδ).liminf_eq

/-! #### The specific sequence `δ N = 1 / log N` -/

/-- The sequence `δ N = 1 / log N` singled out in Question 4.12, clamped into `[0, 1]` so that it
takes values in `unitInterval`.  For `N ≥ 3` no clamping happens, see `coe_logDensity`. -/
def logDensity (N : ℕ) : unitInterval :=
  Set.projIcc 0 1 zero_le_one (1 / Real.log (N : ℝ))

lemma one_le_log_three : 1 ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  exact (Real.exp_one_lt_d9.trans (by norm_num)).le

lemma one_le_log_of_three_le (hN : 3 ≤ N) : 1 ≤ Real.log (N : ℝ) :=
  one_le_log_three.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hN))

lemma coe_logDensity (hN : 3 ≤ N) : (logDensity N : ℝ) = 1 / Real.log (N : ℝ) := by
  have hlog := one_le_log_of_three_le hN
  have hmem : 1 / Real.log (N : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one (by linarith)).mpr hlog⟩
  rw [logDensity, Set.projIcc_of_mem _ hmem]

lemma tendsto_coe_logDensity :
    Filter.Tendsto (fun N : ℕ => (logDensity N : ℝ)) (Filter.atTop : Filter ℕ) (nhds 0) := by
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ))
      (Filter.atTop : Filter ℕ) Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine hlog.inv_tendsto_atTop.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 3] with N hN
  rw [Pi.inv_apply, coe_logDensity hN, one_div]

/-- **One cannot take `δ N = 1 / log N` in Question 4.12.** -/
theorem tendsto_phi_logDensity_div_log_atTop_nhds_zero :
    Filter.Tendsto (fun N : ℕ => (phi (logDensity N) N : ℝ) / Real.log (N : ℝ))
      (Filter.atTop : Filter ℕ) (nhds 0) :=
  tendsto_phi_div_log_atTop_nhds_zero _ tendsto_coe_logDensity

/-- The second half of Question 4.12 verbatim. -/
theorem liminf_phi_logDensity_div_log_eq_zero :
    Filter.liminf (fun N : ℕ => (phi (logDensity N) N : ℝ) / Real.log (N : ℝ))
      (Filter.atTop : Filter ℕ) = 0 :=
  tendsto_phi_logDensity_div_log_atTop_nhds_zero.liminf_eq

/-! #### The rate for `δ N = 1 / log N`

The qualitative answer above says nothing about *how* fast `φ (1 / log N, N) / log N` decays.  Since
`1 / log N` decays more slowly than every negative power of `N`, it lies in the admissible density
range of `dense_subset_without_large_sumsets`, and the main bound applies to it directly with
`log (1 / δ N) = log log N`. -/

lemma eventually_log_lt_rpow {α : ℝ} (hα : 0 < α) :
    ∀ᶠ x : ℝ in (Filter.atTop : Filter ℝ), Real.log x < x ^ α := by
  filter_upwards [(isLittleO_log_rpow_atTop hα).def one_half_pos,
    Filter.eventually_gt_atTop (1 : ℝ)] with x hx hx_one
  have hpow_pos : 0 < x ^ α := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.norm_of_nonneg (Real.log_nonneg hx_one.le), Real.norm_of_nonneg hpow_pos.le] at hx
  linarith

lemma eventually_two_le_log :
    ∀ᶠ N : ℕ in (Filter.atTop : Filter ℕ), 2 ≤ Real.log (N : ℝ) :=
  tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 2)

/-- `1 / log N` decays more slowly than `N ^ (-α)` for every `α > 0`, so it satisfies the lower
constraint on the density range of the main theorem. -/
lemma eventually_rpow_neg_lt_coe_logDensity {α : ℝ} (hα : 0 < α) :
    ∀ᶠ N : ℕ in (Filter.atTop : Filter ℕ),
      Real.rpow (N : ℝ) (-α) < (logDensity N : ℝ) := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_log_lt_rpow hα),
    Filter.eventually_ge_atTop 3] with N hN hN_three
  have hlog_pos : 0 < Real.log (N : ℝ) := lt_of_lt_of_le one_pos (one_le_log_of_three_le hN_three)
  rw [coe_logDensity hN_three]
  change (N : ℝ) ^ (-α) < 1 / Real.log (N : ℝ)
  rw [Real.rpow_neg (Nat.cast_nonneg N), ← one_div]
  exact one_div_lt_one_div_of_lt hlog_pos hN

/-- `1 / log N` is eventually at most `1 / 2`, the upper constraint on the density range. -/
lemma eventually_coe_logDensity_le_half :
    ∀ᶠ N : ℕ in (Filter.atTop : Filter ℕ), (logDensity N : ℝ) ≤ 1 - 1 / 2 := by
  filter_upwards [eventually_two_le_log, Filter.eventually_ge_atTop 3] with N hN hN_three
  rw [coe_logDensity hN_three]
  have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hN
  norm_num at this ⊢
  exact this

/-- **The quantitative answer to the second half of Question 4.12**: eventually
`φ (1 / log N, N) < 4 log N / log log N`, which is `o (log N)`. -/
theorem eventually_phi_logDensity_lt_log_div_log_log :
    ∀ᶠ N : ℕ in (Filter.atTop : Filter ℕ),
      (phi (logDensity N) N : ℝ) < 4 * Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) := by
  have hα : 0 < denseSubsetDensityExponent 1 (1 / 2) :=
    denseSubsetDensityExponent_pos one_pos (by norm_num) (by norm_num)
  filter_upwards [eventually_phi_lt_log_div_log (γ := 1) (c := 1 / 2) one_pos le_rfl
      (by norm_num) (by norm_num) logDensity (eventually_rpow_neg_lt_coe_logDensity hα)
      eventually_coe_logDensity_le_half,
    Filter.eventually_ge_atTop 3] with N hN hN_three
  rwa [coe_logDensity hN_three, one_div_one_div, show (3 : ℝ) + 1 = 4 by norm_num] at hN

end VanishingDensity

end

end DenseSetsWithoutLargeSumsets
