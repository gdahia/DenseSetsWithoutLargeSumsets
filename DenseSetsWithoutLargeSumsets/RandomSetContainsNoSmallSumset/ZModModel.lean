/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.Constants
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.ThresholdEstimates

/-!
# The model of `[n]` in `ZMod q`

For `n > lowerSizeThreshold C γ` we fix a prime `q` with `2 * n ≤ q ≤ 4 * n` and a map
`ℕ → ZMod q` that is a Freiman isomorphism of order `2` on `[n]`. We also record that such `n`
and every `δ` with `n ^ (-lowerDensityExponent C γ) < δ < 1` satisfy `1 < n`, `0 < δ` and
`0 < pairCardThreshold (3 + γ) n δ`.

## Main definitions

* `zmodModelQ`: the prime `q`.
* `zmodModelEmbedding`: the map `ℕ → ZMod q`.

## Main statements

* `zmodModelEmbedding_iso`: `zmodModelEmbedding` is a Freiman isomorphism of order `2` from `[n]`
  onto its image.
* `pairCardThreshold_le_density_log_of_lower_density`: if `δ ≤ 1 - c`, then
  `pairCardThreshold (3 + γ) n δ ≤ densityCoefficient (3 + γ) c * log n`.
-/

@[expose] public section

namespace DenseSetsWithoutLargeSumsets

open Nat hiding div_pos
open scoped Pointwise

noncomputable section

/-- A prime `q` with `2 * n ≤ q ≤ 4 * n` such that `[n]` is Freiman isomorphic of order `2` to a
subset of `ZMod q`. -/
abbrev zmodModelQ {γ C : ℝ} {n : ℕ}
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hn : lowerSizeThreshold C γ < n) : ℕ :=
  Classical.choose (exists_zmod_model n (lowerSizeThreshold_lt_nat_pos hγ_pos C_pos hn))

private lemma zmodModelQ_spec {γ C : ℝ} {n : ℕ} (hγ_pos : 0 < γ) (C_pos : 0 < C)
    (hn : lowerSizeThreshold C γ < n) :
    Nat.Prime (zmodModelQ hγ_pos C_pos hn) ∧ 2 * n ≤ zmodModelQ hγ_pos C_pos hn ∧
      zmodModelQ hγ_pos C_pos hn ≤ 4 * n ∧
        ∃ ψ : ℕ → ZMod (zmodModelQ hγ_pos C_pos hn),
          IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ :=
  Classical.choose_spec (exists_zmod_model n (lowerSizeThreshold_lt_nat_pos hγ_pos C_pos hn))

lemma zmodModelQ_prime {γ C : ℝ} {n : ℕ} (hγ_pos : 0 < γ) (C_pos : 0 < C)
    (hn : lowerSizeThreshold C γ < n) :
    Nat.Prime (zmodModelQ hγ_pos C_pos hn) :=
  (zmodModelQ_spec hγ_pos C_pos hn).1

lemma zmodModelQ_lower {γ C : ℝ} {n : ℕ} (hγ_pos : 0 < γ) (C_pos : 0 < C)
    (hn : lowerSizeThreshold C γ < n) :
    2 * n ≤ zmodModelQ hγ_pos C_pos hn :=
  (zmodModelQ_spec hγ_pos C_pos hn).2.1

lemma zmodModelQ_upper {γ C : ℝ} {n : ℕ} (hγ_pos : 0 < γ) (C_pos : 0 < C)
    (hn : lowerSizeThreshold C γ < n) :
    zmodModelQ hγ_pos C_pos hn ≤ 4 * n :=
  (zmodModelQ_spec hγ_pos C_pos hn).2.2.1

/-- A map `ℕ → ZMod q`, with `q = zmodModelQ hγ_pos C_pos hn`, that is a Freiman isomorphism of
order `2` from `[n]` onto its image. -/
abbrev zmodModelEmbedding {γ C : ℝ} {n : ℕ}
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hn : lowerSizeThreshold C γ < n) :
    ℕ → ZMod (zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) :=
  Classical.choose
    (Classical.choose_spec (exists_zmod_model n (lowerSizeThreshold_lt_nat_pos hγ_pos C_pos
      hn))).2.2.2

/-- The map `zmodModelEmbedding` is a Freiman isomorphism of order `2` from `[n]` onto its
image. -/
lemma zmodModelEmbedding_iso {γ C : ℝ} {n : ℕ} (hγ_pos : 0 < γ) (C_pos : 0 < C)
    (hn : lowerSizeThreshold C γ < n) :
    IsAddFreimanIso 2 (interval n) (zmodModelEmbedding hγ_pos C_pos hn '' (interval n))
      (zmodModelEmbedding hγ_pos C_pos hn) :=
  Classical.choose_spec (zmodModelQ_spec hγ_pos C_pos hn).2.2.2

private lemma two_lt_nat_of_lowerSizeThreshold_lt {C γ : ℝ} {n : ℕ}
    (hn : lowerSizeThreshold C γ < n) : 2 < n :=
  mod_cast (two_le_lowerSizeThreshold C γ).trans_lt hn

lemma one_lt_nat_of_lowerSizeThreshold_lt {C γ : ℝ} {n : ℕ} (hn : lowerSizeThreshold C γ < n) :
    1 < n :=
  one_lt_two.trans (two_lt_nat_of_lowerSizeThreshold_lt hn)

lemma unitInterval_pos_of_density_lower {C γ : ℝ} {n : ℕ} {δ : unitInterval}
    (hn : lowerSizeThreshold C γ < n) (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) :
    0 < (δ : ℝ) :=
  (Real.rpow_pos_of_pos (old_model_threshold_nat_pos hn) _).trans hδ_lower

lemma unitInterval_lt_one {δ : unitInterval} (hδ_upper : (δ : ℝ) < 1) : (δ : ℝ) < 1 :=
  hδ_upper

lemma pairCardThreshold_pos_of_lower_density {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    0 < pairCardThreshold (3 + γ) n δ :=
  pairCardThreshold_pos_of_density (by linarith) (unitInterval_pos_of_density_lower hn hδ_lower)
    hδ_upper (one_lt_nat_of_lowerSizeThreshold_lt hn)

/-- If `n ^ (-lowerDensityExponent C γ) < δ ≤ 1 - c`, then
`pairCardThreshold (3 + γ) n δ ≤ densityCoefficient (3 + γ) c * log n`. -/
lemma pairCardThreshold_le_density_log_of_lower_density {γ C c : ℝ} {n : ℕ}
    {δ : unitInterval} (hγ_pos : 0 < γ) (hc_pos : 0 < c) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ))
    (hδ_upper : (δ : ℝ) ≤ 1 - c) :
    (pairCardThreshold (3 + γ) n δ : ℝ) ≤
      densityCoefficient (3 + γ) c * Real.log (n : ℝ) :=
  pairCardThreshold_le_densityCoefficient_mul_log (by linarith) hc_pos
    (two_lt_nat_of_lowerSizeThreshold_lt hn).le (unitInterval_pos_of_density_lower hn hδ_lower)
    hδ_upper

end

end DenseSetsWithoutLargeSumsets
