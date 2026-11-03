/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal

/-!
# Monotonicity of the triangle removal constant

The constant `triangleRemovalBound ε` of the triangle removal lemma in Mathlib is built from the
bound `SzemerediRegularity.bound` of Szemerédi's regularity lemma. This file shows that the
regularity bound decreases as `ε` grows, and deduces that `triangleRemovalBound` is monotone up to
a factor `3 / 4`. This lets a removal constant at a complicated argument be bounded below by the
removal constant at a simpler, smaller argument.

## Main statements

* `SzemerediRegularity.bound_le_bound`: the regularity bound is antitone in `ε` and monotone in the
  size of the initial partition.
* `SimpleGraph.mul_triangleRemovalBound_le`: `3 / 4 * triangleRemovalBound ε ≤
  triangleRemovalBound ε'` for `0 < ε ≤ ε'`.
* `SimpleGraph.triangleRemovalBound_le_cube`: `triangleRemovalBound ε ≤ ε ^ 3 / 128`.
-/

public section

open Real

variable {ε ε' : ℝ} {l l' : ℕ}

namespace SzemerediRegularity

lemma initialBound_le_initialBound (hε : 0 < ε) (h : ε ≤ ε') (hl : l' ≤ l) :
    initialBound ε' l' ≤ initialBound ε l := by
  unfold initialBound
  refine max_le_max le_rfl (max_le_max hl (Nat.add_le_add_right (Nat.floor_le_floor
    (div_le_div_of_nonneg_right ?_ (log_nonneg (by norm_num)))) 1))
  exact log_le_log (div_pos (by norm_num) (pow_pos (hε.trans_le h) 5))
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hε.le h 5))

/-- The regularity bound is antitone in `ε` and monotone in the size of the initial partition. -/
lemma bound_le_bound (hε : 0 < ε) (h : ε ≤ ε') (hl : l' ≤ l) : bound ε' l' ≤ bound ε l := by
  have hm : stepBound^[⌊4 / ε' ^ 5⌋₊] (initialBound ε' l') ≤
      stepBound^[⌊4 / ε ^ 5⌋₊] (initialBound ε l) :=
    ((stepBound_mono.iterate _) (initialBound_le_initialBound hε h hl)).trans
      (Function.monotone_iterate_of_id_le le_stepBound
        (Nat.floor_le_floor (div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (pow_le_pow_left₀ hε.le h 5))) _)
  unfold bound
  exact Nat.mul_le_mul hm (Nat.pow_le_pow_right (by norm_num) hm)

end SzemerediRegularity

namespace SimpleGraph

open SzemerediRegularity

/-- Up to a factor `3 / 4`, the triangle removal constant is monotone. -/
lemma mul_triangleRemovalBound_le (hε : 0 < ε) (h : ε ≤ ε') :
    3 / 4 * triangleRemovalBound ε ≤ triangleRemovalBound ε' := by
  have hε' := hε.trans_le h
  have hceil : ⌈4 / ε'⌉₊ ≤ ⌈4 / ε⌉₊ :=
    Nat.ceil_le_ceil (div_le_div_of_nonneg_left (by norm_num) hε h)
  have hb : ε / (16 * bound (ε / 8) ⌈4 / ε⌉₊) ≤ ε' / (16 * bound (ε' / 8) ⌈4 / ε'⌉₊) := by
    have := bound_pos (ε / 8) ⌈4 / ε⌉₊
    have := bound_pos (ε' / 8) ⌈4 / ε'⌉₊
    refine div_le_div₀ hε'.le h (by positivity) ?_
    gcongr
    exact bound_le_bound (by positivity) (by linarith) hceil
  have hq : ∀ x : ℝ, 0 < x → 3 / 4 ≤ 1 - min 1 x / 4 ∧ 1 - min 1 x / 4 ≤ 1 := fun x hx ↦
    ⟨by linarith [min_le_left 1 x], by linarith [le_min zero_le_one hx.le]⟩
  have hT := (triangleRemovalBound_pos hε).le
  unfold triangleRemovalBound at hT ⊢
  refine le_min ?_ ?_
  · refine (mul_le_of_le_one_left hT (by norm_num)).trans ((min_le_left _ _).trans ?_)
    gcongr
  · refine (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)).trans ?_
    have h₀ := hq ε hε
    have h₁ := hq ε' hε'
    have : (ε / (16 * bound (ε / 8) ⌈4 / ε⌉₊)) ^ 3 ≤ (ε' / (16 * bound (ε' / 8) ⌈4 / ε'⌉₊)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hb 3
    nlinarith [pow_pos (by positivity : 0 < ε / (16 * bound (ε / 8) ⌈4 / ε⌉₊)) 3]

/-- The triangle removal constant is at most `ε ^ 3 / 128`. -/
lemma triangleRemovalBound_le_cube (hε : 0 < ε) : triangleRemovalBound ε ≤ ε ^ 3 / 128 := by
  refine (min_le_left _ _).trans ?_
  rw [inv_le_comm₀ (by positivity) (by positivity), inv_div,
    (by ring : 128 / ε ^ 3 = 2 * (4 / ε) ^ 3)]
  gcongr
  exact Nat.le_ceil _

end SimpleGraph
