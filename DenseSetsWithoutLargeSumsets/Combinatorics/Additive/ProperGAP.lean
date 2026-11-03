/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GAP.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Set.Card

/-!
# The number of proper generalized arithmetic progressions in `ZMod q`

A generalized arithmetic progression `P : ChangFreimanRuzsa.GAP (ZMod q)` is determined by its
origin, its steps and its side lengths. If `P` is proper (`ChangFreimanRuzsa.GAP.Proper`), a side
length is at most the number of points of `P`. This bounds the number of proper progressions of
given dimension and size.

## Main definitions

* `properGAPsZModOfDim d s hq`: the proper progressions of dimension `d` with at most `s` points
  in `ZMod q`.

## Main statements

* `properGAPsZModOfDim_card`: there are at most `q ^ (d + 1) * s ^ d` of them.
-/

@[expose] public section

namespace DenseSetsWithoutLargeSumsets

open Finset ChangFreimanRuzsa

noncomputable section

/-- A progression of dimension `0` has one point. -/
lemma card_toFinset_eq_one_of_dim_eq_zero {G : Type*} [DecidableEq G] [AddCommMonoid G]
    (P : GAP G) (hdim : P.dim = 0) : #P.toFinset = 1 := by
  apply le_antisymm (P.card_le_prod_length.trans_eq ?_) (card_pos.2 P.nonempty)
  apply prod_eq_one
  intro i _
  exact absurd hdim i.pos.ne'

private lemma length_le_card_toFinset {G : Type*} [DecidableEq G] [AddCommMonoid G] {P : GAP G}
    (hP : P.Proper) (i : Fin P.dim) : P.length i ≤ #P.toFinset := by
  rw [P.card_eq_prod_length hP, prod_eq_mul_prod_sdiff_singleton_of_mem (mem_univ i)]
  apply Nat.le_mul_of_pos_right
  apply prod_pos
  intro j _
  exact P.length_pos j

/-- A progression of dimension `d` is the progression with its origin, steps and lengths, numbered
by `Fin d`. -/
private lemma eq_ofSteps_cast {G : Type*} [AddCommMonoid G] {d : ℕ} (P : GAP G)
    (hdim : P.dim = d) :
    P = GAP.ofSteps P.origin (fun i ↦ P.step (Fin.cast hdim.symm i))
      (fun i ↦ P.length (Fin.cast hdim.symm i)) := by
  subst hdim
  exact P.ofSteps_step_length.symm

/-- The proper progressions of dimension `d` with at most `s` points in `ZMod q`, as a set. -/
def properGAPsZModOfDimSet (q d : ℕ) (s : ℝ) : Set (GAP (ZMod q)) :=
  {P : GAP (ZMod q) | P.Proper ∧ P.dim = d ∧ #P.toFinset ≤ s}

/-- The data that determine a proper progression of dimension `d` with at most `s` points: the
origin, the steps, and the side lengths minus one. -/
private abbrev GapCode (q d s : ℕ) : Type :=
  (ZMod q) × (Fin d → ZMod q) × (Fin d → Fin s)

private def gapCode {q d s : ℕ} (P : GAP (ZMod q)) (hP : P.Proper) (hdim : P.dim = d)
    (hcard : #P.toFinset ≤ s) : GapCode q d s :=
  (P.origin, fun i ↦ P.step (Fin.cast hdim.symm i), fun i ↦
    ⟨P.length (Fin.cast hdim.symm i) - 1, by
      grind [P.length_pos (Fin.cast hdim.symm i),
        length_le_card_toFinset hP (Fin.cast hdim.symm i)]⟩)

private lemma gapCode_injective {q d s : ℕ} :
    Function.Injective fun P : properGAPsZModOfDimSet q d s ↦
      gapCode P.1 P.2.1 P.2.2.1 (mod_cast P.2.2.2) := by
  intro P Q h
  obtain ⟨horigin, h⟩ := Prod.mk.inj h
  obtain ⟨hstep, hlength⟩ := Prod.mk.inj h
  apply Subtype.ext
  rw [eq_ofSteps_cast P.1 P.2.2.1, eq_ofSteps_cast Q.1 Q.2.2.1, horigin, hstep]
  congr with i
  grind [congrArg Fin.val (congrFun hlength i), P.1.length_pos (Fin.cast P.2.2.1.symm i),
    Q.1.length_pos (Fin.cast Q.2.2.1.symm i)]

lemma properGAPsZModOfDimSet_finite {q : ℕ} (d s : ℕ) (hq : 0 < q) :
    (properGAPsZModOfDimSet q d s).Finite := by
  have : NeZero q := ⟨hq.ne'⟩
  exact Set.finite_coe_iff.mp (Finite.of_injective _ (gapCode_injective (q := q) (d := d) (s := s)))

/-- The proper progressions of dimension `d` with at most `s` points in `ZMod q`. -/
def properGAPsZModOfDim {q : ℕ} (d s : ℕ) (hq : 0 < q) : Finset (GAP (ZMod q)) :=
  (properGAPsZModOfDimSet_finite d s hq).toFinset

lemma mem_properGAPsZModOfDim {q d s : ℕ} (hq : 0 < q) {P : GAP (ZMod q)} :
    P ∈ properGAPsZModOfDim d s hq ↔ P.Proper ∧ P.dim = d ∧ #P.toFinset ≤ s := by
  simp [properGAPsZModOfDim, properGAPsZModOfDimSet]

private lemma card_gapCode {q d s : ℕ} [NeZero q] :
    Fintype.card (GapCode q d s) = q ^ (d + 1) * s ^ d := by
  simp [GapCode, Fintype.card_prod, Fintype.card_pi, ZMod.card, Fintype.card_fin, pow_succ,
    mul_assoc, mul_comm]

/-- There are at most `q ^ (d + 1) * s ^ d` proper progressions of dimension `d` with at most `s`
points in `ZMod q`. -/
lemma properGAPsZModOfDim_card {q d s : ℕ} (hq : 0 < q) :
    #(properGAPsZModOfDim d s hq) ≤ q ^ (d + 1) * s ^ d := by
  have : NeZero q := ⟨hq.ne'⟩
  rw [properGAPsZModOfDim, ← Set.ncard_eq_toFinset_card (properGAPsZModOfDimSet q d s)
    (properGAPsZModOfDimSet_finite d s hq), ← Nat.card_coe_set_eq, ← card_gapCode,
    ← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_injective _ (gapCode_injective (q := q) (d := d) (s := s))

end

end DenseSetsWithoutLargeSumsets
