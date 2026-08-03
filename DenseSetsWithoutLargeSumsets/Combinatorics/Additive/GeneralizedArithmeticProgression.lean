/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
GAPs
-/

namespace DenseSetsWithoutLargeSumsets

open Filter Nat
open scoped Pointwise

noncomputable section

def gapMap {G : Type*} [AddCommMonoid G] {d : ℕ} (origin : G) (step : Fin d → G)
    (length : Fin d → ℕ) (w : (i : Fin d) → Fin (length i)) : G := origin + ∑ i, (w i : ℕ) • step i

structure ProperGAP (G : Type*) [DecidableEq G] [AddCommMonoid G] where
  dim : ℕ
  carrier : Finset G
  origin : G
  step : Fin dim → G
  length : Fin dim → ℕ
  length_one_lt : ∀ i, 1 < length i
  carrier_eq :
    carrier = Finset.univ.image (gapMap origin step length)
  proper :
    Function.Injective (gapMap origin step length)

instance {G : Type*} [DecidableEq G] [AddCommMonoid G] : CoeOut (ProperGAP G) (Finset G) where
  coe P := P.carrier

lemma ProperGAP.length_pos {G : Type*} [DecidableEq G] [AddCommMonoid G] (P : ProperGAP G)
    (i : Fin P.dim) : 0 < P.length i :=
  zero_lt_one.trans (P.length_one_lt i)

lemma properGAP_card_eq_prod_length {G : Type*} [DecidableEq G] [AddCommMonoid G]
    (P : ProperGAP G) : P.carrier.card = ∏ i, P.length i := by
  rw [P.carrier_eq, Finset.card_image_of_injective _ P.proper]
  simp [Fintype.card_pi]

lemma properGAP_length_le_card {G : Type*} [DecidableEq G] [AddCommMonoid G] (P : ProperGAP G)
    (i : Fin P.dim) : P.length i ≤ P.carrier.card := by
  rw [properGAP_card_eq_prod_length P,
      Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
  exact Nat.le_mul_of_pos_right _ (Finset.prod_pos fun j _ => P.length_pos j)

def properGAPsZModOfDimSet (q d : ℕ) (s : ℝ) : Set (ProperGAP (ZMod q)) :=
  {P : ProperGAP (ZMod q) | P.dim = d ∧ P.carrier.card ≤ s}

private abbrev gapEncodingParams (q d s : ℕ) : Type :=
  (ZMod q) × (Fin d → ZMod q) × (Fin d → Fin s)

private def encodeGapAsParams {q d s : ℕ} (P : ProperGAP (ZMod q)) (hdim : P.dim = d)
    (hcard : P.carrier.card ≤ s) : gapEncodingParams q d s :=
  (P.origin,
    (fun i : Fin d => P.step (hdim.symm ▸ i)),
    (fun i : Fin d =>
      ⟨P.length (hdim.symm ▸ i) - 1, by
        rw [Nat.sub_lt_iff_lt_add (P.length_pos (hdim.symm ▸ i))]
        simpa [Nat.add_comm] using
          Nat.lt_succ_of_le ((properGAP_length_le_card P (hdim.symm ▸ i)).trans hcard)⟩))

private lemma encodeGapAsParams_injective {q d s : ℕ} :
    Function.Injective (fun P : properGAPsZModOfDimSet q d s =>
      encodeGapAsParams P.1 P.2.1 (by exact_mod_cast P.2.2)) := by
  intro P Q h
  rcases P with
    ⟨⟨pdim, pcarrier, porigin, pstep, plen, plen_one_lt, pcarrier_eq, pproper⟩,
      hPdim, hPcard⟩
  rcases Q with
    ⟨⟨qdim, qcarrier, qorigin, qstep, qlen, qlen_one_lt, qcarrier_eq, qproper⟩,
      hQdim, hQcard⟩
  subst d
  cases hQdim
  apply Subtype.ext
  rw [ProperGAP.mk.injEq]
  dsimp [encodeGapAsParams] at h
  have horigin : porigin = qorigin := congrArg Prod.fst h
  have hstep_d : pstep = qstep :=
    congrArg (fun x => (x.2.1 : Fin pdim → ZMod q)) h
  have hlength_d : plen = qlen := by
    funext i
    have : plen i - 1 = qlen i - 1 := congrArg (fun x => ((x.2.2 i : Fin s) : ℕ)) h
    grind
  exact ⟨rfl, by rw [pcarrier_eq, qcarrier_eq, horigin, hstep_d, hlength_d],
    horigin, heq_of_eq hstep_d, heq_of_eq hlength_d⟩

private lemma properGAPsZModOfDimSet_finite {q : ℕ} (d s : ℕ) (hq : 0 < q) :
    (properGAPsZModOfDimSet q d s).Finite := by
  haveI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  haveI : Finite (gapEncodingParams q d s) := by
    dsimp [gapEncodingParams]
    infer_instance
  haveI : Finite (properGAPsZModOfDimSet q d s) :=
    Finite.of_injective
      (fun P : properGAPsZModOfDimSet q d s =>
        encodeGapAsParams P.1 P.2.1 (by exact_mod_cast P.2.2))
      (encodeGapAsParams_injective (q := q) (d := d) (s := s))
  exact Set.finite_coe_iff.mp inferInstance

def properGAPsZModOfDim {q : ℕ} (d s : ℕ) (hq : 0 < q) : Finset (ProperGAP (ZMod q)) :=
  (properGAPsZModOfDimSet_finite d s hq).toFinset

private lemma encodeGapAsParams_card {q d s : ℕ} [NeZero q] :
    Fintype.card (gapEncodingParams q d s) = q ^ (d + 1) * s ^ d := by
  simp [gapEncodingParams, Fintype.card_prod, Fintype.card_pi, ZMod.card,
    Fintype.card_fin, pow_succ, mul_assoc, mul_comm]

lemma properGAPsZModOfDim_card {q d s : ℕ} (_hs : 0 < s) (hq : 0 < q) :
    (properGAPsZModOfDim d s hq).card ≤ q ^ (d + 1) * s ^ d := by
  haveI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  rw [properGAPsZModOfDim,
    ← Set.ncard_eq_toFinset_card (properGAPsZModOfDimSet q d s)
      (properGAPsZModOfDimSet_finite d s hq)]
  rw [← Nat.card_coe_set_eq]
  rw [← encodeGapAsParams_card, ← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_injective
    (fun P : properGAPsZModOfDimSet q d s =>
      encodeGapAsParams P.1 P.2.1 (by exact_mod_cast P.2.2))
    (encodeGapAsParams_injective (q := q) (d := d) (s := s))

end

end DenseSetsWithoutLargeSumsets
