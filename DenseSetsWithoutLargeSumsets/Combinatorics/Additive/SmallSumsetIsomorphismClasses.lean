/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module -- shake: keep-all

public import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.SmallSumsetIsomorphismClasses.CoreAndCovers
public import DenseSetsWithoutLargeSumsets.Combinatorics.Additive.SmallSumsetIsomorphismClasses.ClassCountBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.Tactic.Positivity.Finset

/-!
# Isomorphism classes with small self-sumsets

This umbrella module re-exports the combinatorial class covers and analytic counting bounds.
-/

@[expose] public section
