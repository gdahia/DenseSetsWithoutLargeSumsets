/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.RandomSetContainsNoSmallSumset.ThresholdEstimates
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.FreimanDimension
import DenseSetsWithoutLargeSumsets.Probability
import DenseSetsWithoutLargeSumsets.Common
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.GeneralizedArithmeticProgression
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.LargeSumsetsFromMediumSizedSubsets.MediumSizedSubsets
import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.Chang.Reduction
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.NumberTheory.Bertrand

/-!
The chosen `ZMod q` Freiman model of `interval n`.

Packages `exists_zmod_model` into the concrete choice `zmodModelQ`/`zmodModelEmbedding` used
throughout the rest of the argument, together with the basic size facts about `n` and `δ` that
follow from being above the thresholds.
-/

namespace DenseSetsWithoutLargeSumsets

open Nat hiding div_pos
open scoped Pointwise

noncomputable section

abbrev zmodModelQ {γ C : ℝ} {n : ℕ}
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hn : lowerSizeThreshold C γ < n) : ℕ :=
  Classical.choose (exists_zmod_model n (lowerSizeThreshold_lt_nat_pos hγ_pos C_pos hn))

private lemma zmodModelQ_spec {γ C : ℝ} {n : ℕ}
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hn : lowerSizeThreshold C γ < n) :
    Nat.Prime (zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) ∧
      2 * n ≤ zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn ∧
        zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn ≤ 4 * n ∧
          ∃ ψ : ℕ → ZMod (zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn),
            IsAddFreimanIso 2 (interval n) (ψ '' (interval n)) ψ := by
  unfold zmodModelQ
  exact Classical.choose_spec (exists_zmod_model n (lowerSizeThreshold_lt_nat_pos hγ_pos C_pos hn))

lemma zmodModelQ_prime {γ C : ℝ} {n : ℕ}
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hn : lowerSizeThreshold C γ < n) :
    Nat.Prime (zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) := by
  exact (zmodModelQ_spec hγ_pos C_pos hn).1

lemma zmodModelQ_lower {γ C : ℝ} {n : ℕ}
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hn : lowerSizeThreshold C γ < n) :
    2 * n ≤ zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn := by
  exact (zmodModelQ_spec hγ_pos C_pos hn).2.1

lemma zmodModelQ_upper {γ C : ℝ} {n : ℕ}
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hn : lowerSizeThreshold C γ < n) :
    zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn ≤ 4 * n := by
  exact (zmodModelQ_spec hγ_pos C_pos hn).2.2.1

abbrev zmodModelEmbedding {γ C : ℝ} {n : ℕ}
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hn : lowerSizeThreshold C γ < n) :
    ℕ → ZMod (zmodModelQ (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) :=
  Classical.choose
    (Classical.choose_spec (exists_zmod_model n (lowerSizeThreshold_lt_nat_pos hγ_pos C_pos
      hn))).2.2.2

lemma zmodModelEmbedding_iso {γ C : ℝ} {n : ℕ}
    (hγ_pos : 0 < γ) (C_pos : 0 < C) (hn : lowerSizeThreshold C γ < n) :
    IsAddFreimanIso 2 (interval n)
      (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn '' (interval n))
      (zmodModelEmbedding (γ := γ) (C := C) (n := n) hγ_pos C_pos hn) := by
  unfold zmodModelEmbedding
  exact Classical.choose_spec
    (Classical.choose_spec (exists_zmod_model n (lowerSizeThreshold_lt_nat_pos hγ_pos C_pos
      hn))).2.2.2

private lemma two_lt_nat_of_lowerSizeThreshold_lt {C γ : ℝ} {n : ℕ} (hn : lowerSizeThreshold C γ
  < n) :
    2 < n := by
  exact_mod_cast (two_le_lowerSizeThreshold C γ).trans_lt hn

private lemma two_le_nat_of_lowerSizeThreshold_lt {C γ : ℝ} {n : ℕ} (hn : lowerSizeThreshold C γ
  < n) :
    2 ≤ n := by
  exact (two_lt_nat_of_lowerSizeThreshold_lt hn).le

lemma one_lt_nat_of_lowerSizeThreshold_lt {C γ : ℝ} {n : ℕ} (hn : lowerSizeThreshold C γ
  < n) :
    1 < n := by
  exact (by norm_num : 1 < 2).trans (two_lt_nat_of_lowerSizeThreshold_lt hn)

lemma unitInterval_pos_of_density_lower {C γ : ℝ} {n : ℕ} {δ : unitInterval}
    (hn : lowerSizeThreshold C γ < n) (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) :
    0 < (δ : ℝ) := by
  exact (Real.rpow_pos_of_pos (old_model_threshold_nat_pos hn) _).trans hδ_lower

lemma unitInterval_lt_one {δ : unitInterval}
    (hδ_upper : (δ : ℝ) < 1) :
    (δ : ℝ) < 1 := by
  linarith

lemma pairCardThreshold_pos_of_lower_density {γ C : ℝ} {n : ℕ} {δ : unitInterval}
    (hγ_pos : 0 < γ) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ)) (hδ_upper : (δ : ℝ) < 1) :
    0 < pairCardThreshold (3 + γ) n δ := by
  apply pairCardThreshold_pos_of_density
  · linarith
  · exact unitInterval_pos_of_density_lower hn hδ_lower
  · exact unitInterval_lt_one hδ_upper
  · exact one_lt_nat_of_lowerSizeThreshold_lt hn

lemma pairCardThreshold_le_density_log_of_lower_density {γ C c : ℝ} {n : ℕ}
    {δ : unitInterval} (hγ_pos : 0 < γ) (hc_pos : 0 < c) (hn : lowerSizeThreshold C γ < n)
    (hδ_lower : (n : ℝ) ^ (-lowerDensityExponent C γ) < (δ : ℝ))
    (hδ_upper : (δ : ℝ) ≤ 1 - c) :
    (pairCardThreshold (3 + γ) n δ : ℝ) ≤
      densityCoefficient (3 + γ) c * Real.log (n : ℝ) := by
  refine pairCardThreshold_le_densityCoefficient_mul_log ?_ hc_pos
    (two_le_nat_of_lowerSizeThreshold_lt hn) (unitInterval_pos_of_density_lower hn hδ_lower)
    hδ_upper
  linarith


end

end DenseSetsWithoutLargeSumsets
