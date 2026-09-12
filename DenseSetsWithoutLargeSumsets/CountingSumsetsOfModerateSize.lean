/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module -- shake: keep-all

public import DenseSetsWithoutLargeSumsets.CountingSumsetsOfModerateSize.Enumeration
public import DenseSetsWithoutLargeSumsets.CountingSumsetsOfModerateSize.Probability
import APAP.Prereqs.Chang
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.NormNum.Prime

/-!
# Counting sumsets of moderate size

This umbrella module re-exports the enumeration and probability bounds.
-/

@[expose] public section
