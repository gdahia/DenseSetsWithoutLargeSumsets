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

end

end DenseSetsWithoutLargeSumsets
