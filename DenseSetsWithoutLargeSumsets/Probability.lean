/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import DenseSetsWithoutLargeSumsets.Common
import Mathlib.Probability.Distributions.SetBernoulli

/-!
Finite Bernoulli random-subset model used by the probability statements.
-/

open scoped BigOperators

namespace DenseSetsWithoutLargeSumsets

open MeasureTheory

noncomputable section

/--
The `p`-random binomial subset of an ambient set, returned as a measure on finsets.

This wraps mathlib's `ProbabilityTheory.setBernoulli`, whose samples are sets, and maps each
finite sampled set to the corresponding finset.
-/
noncomputable def binomialFinsetSubset {α : Type*} (Ω : Set α) (p : unitInterval) :
    Measure (Finset α) :=
  by
    classical
    exact (ProbabilityTheory.setBernoulli Ω p).map fun S =>
      if hS : S.Finite then hS.toFinset else ∅

instance instIsFiniteMeasureBinomialFinsetSubset {α : Type*} (Ω : Set α) (p : unitInterval) :
    IsFiniteMeasure (binomialFinsetSubset Ω p) := by
  classical
  rw [binomialFinsetSubset]
  infer_instance

lemma setBernoulli_real_superset {α : Type*} [Countable α]
    {Ω T : Set α} (p : unitInterval) (hTΩ : T ⊆ Ω) (hT : T.Finite) :
    (ProbabilityTheory.setBernoulli Ω p).real {S : Set α | T ⊆ S} = (p : ℝ) ^ T.ncard := by
  classical
  lift T to Finset α using hT
  rw [MeasureTheory.measureReal_def, ProbabilityTheory.setBernoulli_apply']
  have hpre :
      ((fun q : α → Prop => {i | q i}) ⁻¹' {S : Set α | (T : Set α) ⊆ S}) =
        MeasureTheory.cylinder T {q : (i : T) → Prop | ∀ i : T, q i = True} := by
    ext q
    simp [MeasureTheory.mem_cylinder, Set.subset_def]
  let q₀ : (i : T) → Prop := fun _ => True
  have hcoords : {q : (i : T) → Prop | ∀ i : T, q i = True} = {q₀} := by
    ext q
    simp [q₀, funext_iff]
  have hmeas : MeasurableSet {q : (i : T) → Prop | ∀ i : T, q i = True} := by
    rw [hcoords]
    exact measurableSet_singleton q₀
  rw [hpre]
  have hcyl :
      (MeasureTheory.Measure.infinitePi fun i =>
          unitInterval.toNNReal p • MeasureTheory.Measure.dirac (i ∈ Ω) +
            unitInterval.toNNReal (unitInterval.symm p) • MeasureTheory.Measure.dirac False)
        (MeasureTheory.cylinder T {q : (i : T) → Prop | ∀ i : T, q i = True}) =
      MeasureTheory.Measure.pi
        (fun i : T =>
          unitInterval.toNNReal p • MeasureTheory.Measure.dirac ((i : α) ∈ Ω) +
            unitInterval.toNNReal (unitInterval.symm p) • MeasureTheory.Measure.dirac False)
        {q : (i : T) → Prop | ∀ i : T, q i = True} :=
    MeasureTheory.Measure.infinitePi_cylinder
      (μ := fun i =>
        unitInterval.toNNReal p • MeasureTheory.Measure.dirac (i ∈ Ω) +
          unitInterval.toNNReal (unitInterval.symm p) • MeasureTheory.Measure.dirac False)
      hmeas
  rw [hcyl, hcoords, MeasureTheory.Measure.pi_singleton]
  have hterm (i : T) :
      (unitInterval.toNNReal p • MeasureTheory.Measure.dirac ((i : α) ∈ Ω) +
            unitInterval.toNNReal (unitInterval.symm p) • MeasureTheory.Measure.dirac False)
          {q₀ i} = unitInterval.toNNReal p := by
    have hiΩ : (i : α) ∈ Ω := hTΩ i.property
    simp [q₀, hiΩ]
  rw [Finset.prod_congr rfl (fun i _ => hterm i)]
  simp

lemma binomialFinsetSubset_real_superset_nat
    {Ω : Set ℕ} (p : unitInterval) (hΩ : Ω.Finite) {T : Finset ℕ} :
    (binomialFinsetSubset Ω p).real {S : Finset ℕ | T ⊆ S} ≤ (p : ℝ) ^ T.card := by
  classical
  let f : Set ℕ → Finset ℕ := fun S => if hS : S.Finite then hS.toFinset else ∅
  let g : Set ℕ → Finset ℕ := fun S => (hΩ.subset (Set.inter_subset_right (s := S))).toFinset
  have hfg : f =ᵐ[ProbabilityTheory.setBernoulli Ω p] g := by
    filter_upwards [ProbabilityTheory.setBernoulli_ae_subset (u := Ω) (p := p)] with S hSΩ
    have hSfin : S.Finite := hΩ.subset hSΩ
    ext x
    by_cases hxS : x ∈ S
    · simp [f, g, hSfin, hxS, hSΩ hxS]
    · simp [f, g, hSfin, hxS]
  have hg_meas : Measurable g := by
    refine measurable_to_countable' ?_
    intro F
    by_cases hFΩ : (F : Set ℕ) ⊆ Ω
    · let E : Set (Set ℕ) :=
        ⋂ x ∈ hΩ.toFinset,
          if x ∈ F then {S : Set ℕ | x ∈ S} else {S : Set ℕ | x ∉ S}
      have measurable_E : MeasurableSet E := by
        refine MeasurableSet.biInter (hΩ.toFinset.countable_toSet) ?_
        intro x hx
        by_cases hxF : x ∈ F
        · simpa [hxF] using measurable_set_mem x
        · simpa [hxF] using (measurable_set_mem x).not
      convert measurable_E using 1
      · ext S
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · intro hSF
          dsimp only [E]
          simp only [Set.mem_iInter]
          intro x hxΩfin
          have hxΩ : x ∈ Ω := hΩ.mem_toFinset.mp hxΩfin
          by_cases hxF : x ∈ F
          · rw [if_pos hxF]
            have : x ∈ g S := by
              rw [hSF]
              exact hxF
            simpa [g, hxΩ] using this
          · rw [if_neg hxF]
            intro hxS
            have : x ∈ g S := by simp [g, hxS, hxΩ]
            rw [hSF] at this
            exact hxF this
        · intro hE
          ext x
          by_cases hxΩ : x ∈ Ω
          · have hxΩfin : x ∈ hΩ.toFinset := hΩ.mem_toFinset.mpr hxΩ
            have hEx : S ∈
                (if x ∈ F then {S : Set ℕ | x ∈ S} else {S : Set ℕ | x ∉ S}) := by
              change S ∈ E at hE
              exact (Set.mem_iInter.mp (Set.mem_iInter.mp hE x) hxΩfin)
            by_cases hxF : x ∈ F
            · simpa [g, hxΩ, hxF] using hEx
            · simpa [g, hxΩ, hxF] using hEx
          · have hxF : x ∉ F := fun hx => hxΩ (hFΩ hx)
            simp [g, hxΩ, hxF]
    · convert MeasurableSet.empty using 1
      · ext S
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        intro hSF
        apply hFΩ
        intro x hxF
        have : x ∈ g S := by simpa [hSF, hxF]
        have hxpair : x ∈ S ∧ x ∈ Ω := by simpa [g] using this
        exact hxpair.2
  rw [binomialFinsetSubset,
    MeasureTheory.map_measureReal_apply_of_aemeasurable ⟨g, hg_meas, hfg⟩
      (({S : Finset ℕ | T ⊆ S}).to_countable.measurableSet)]
  by_cases hTΩ : (T : Set ℕ) ⊆ Ω
  · refine (MeasureTheory.measureReal_mono
      (μ := ProbabilityTheory.setBernoulli Ω p)
      (s₂ := {S : Set ℕ | (T : Set ℕ) ⊆ S}) ?_ (by finiteness)).trans_eq ?_
    · intro S hS t ht
      by_cases hSfin : S.Finite
      · apply hSfin.mem_toFinset.mp
        simpa [f, hSfin] using hS ht
      · by_cases hTempty : T = ∅
        · simp [hTempty] at ht
        · simp [f, hSfin, hTempty] at hS
    · simpa using
        setBernoulli_real_superset (Ω := Ω) (T := (T : Set ℕ)) p hTΩ T.finite_toSet
  · refine (le_of_eq ?_).trans (pow_nonneg p.2.1 T.card)
    rw [MeasureTheory.measureReal_eq_zero_iff, MeasureTheory.measure_eq_zero_iff_ae_notMem]
    filter_upwards [ProbabilityTheory.setBernoulli_ae_subset (u := Ω) (p := p)] with S hSΩ hTS
    apply hTΩ
    intro x hxT
    have hSfin : S.Finite := hΩ.subset hSΩ
    exact hSΩ (hSfin.mem_toFinset.mp (by simpa [f, hSfin] using hTS hxT))

lemma binomialFinsetSubset_real_singleton_nat_of_subset
    {Ω : Set ℕ} (p : unitInterval) (hΩ : Ω.Finite) {T : Finset ℕ}
    (hTΩ : (T : Set ℕ) ⊆ Ω) :
    (binomialFinsetSubset Ω p).real ({T} : Set (Finset ℕ)) =
      (p : ℝ) ^ T.card * (1 - (p : ℝ)) ^ (Ω.ncard - T.card) := by
  classical
  let f : Set ℕ → Finset ℕ := fun S => if hS : S.Finite then hS.toFinset else ∅
  let g : Set ℕ → Finset ℕ := fun S => (hΩ.subset (Set.inter_subset_right (s := S))).toFinset
  have hfg : f =ᵐ[ProbabilityTheory.setBernoulli Ω p] g := by
    filter_upwards [ProbabilityTheory.setBernoulli_ae_subset (u := Ω) (p := p)] with S hSΩ
    have hSfin : S.Finite := hΩ.subset hSΩ
    ext x
    by_cases hxS : x ∈ S
    · simp [f, g, hSfin, hxS, hSΩ hxS]
    · simp [f, g, hSfin, hxS]
  have hg_meas : Measurable g := by
    refine measurable_to_countable' ?_
    intro F
    by_cases hFΩ : (F : Set ℕ) ⊆ Ω
    · let E : Set (Set ℕ) :=
        ⋂ x ∈ hΩ.toFinset,
          if x ∈ F then {S : Set ℕ | x ∈ S} else {S : Set ℕ | x ∉ S}
      have measurable_E : MeasurableSet E := by
        refine MeasurableSet.biInter (hΩ.toFinset.countable_toSet) ?_
        intro x hx
        by_cases hxF : x ∈ F
        · simpa [hxF] using measurable_set_mem x
        · simpa [hxF] using (measurable_set_mem x).not
      convert measurable_E using 1
      · ext S
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · intro hSF
          dsimp only [E]
          simp only [Set.mem_iInter]
          intro x hxΩfin
          have hxΩ : x ∈ Ω := hΩ.mem_toFinset.mp hxΩfin
          by_cases hxF : x ∈ F
          · rw [if_pos hxF]
            have : x ∈ g S := by
              rw [hSF]
              exact hxF
            simpa [g, hxΩ] using this
          · rw [if_neg hxF]
            intro hxS
            have : x ∈ g S := by simp [g, hxS, hxΩ]
            rw [hSF] at this
            exact hxF this
        · intro hE
          ext x
          by_cases hxΩ : x ∈ Ω
          · have hxΩfin : x ∈ hΩ.toFinset := hΩ.mem_toFinset.mpr hxΩ
            have hEx : S ∈
                (if x ∈ F then {S : Set ℕ | x ∈ S} else {S : Set ℕ | x ∉ S}) := by
              change S ∈ E at hE
              exact (Set.mem_iInter.mp (Set.mem_iInter.mp hE x) hxΩfin)
            by_cases hxF : x ∈ F
            · simpa [g, hxΩ, hxF] using hEx
            · simpa [g, hxΩ, hxF] using hEx
          · have hxF : x ∉ F := fun hx => hxΩ (hFΩ hx)
            simp [g, hxΩ, hxF]
    · convert MeasurableSet.empty using 1
      · ext S
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        intro hSF
        apply hFΩ
        intro x hxF
        have : x ∈ g S := by simpa [hSF, hxF]
        have hxpair : x ∈ S ∧ x ∈ Ω := by simpa [g] using this
        exact hxpair.2
  have hf_ae : AEMeasurable f (ProbabilityTheory.setBernoulli Ω p) := ⟨g, hg_meas, hfg⟩
  have hmap :
      (binomialFinsetSubset Ω p).real ({T} : Set (Finset ℕ)) =
        (ProbabilityTheory.setBernoulli Ω p).real (f ⁻¹' ({T} : Set (Finset ℕ))) := by
    rw [binomialFinsetSubset]
    exact MeasureTheory.map_measureReal_apply_of_aemeasurable
      hf_ae (({T} : Set (Finset ℕ)).to_countable.measurableSet)
  have hpre_ae :
      f ⁻¹' ({T} : Set (Finset ℕ)) =ᵐ[ProbabilityTheory.setBernoulli Ω p]
        ({((T : Finset ℕ) : Set ℕ)} : Set (Set ℕ)) := by
    filter_upwards [ProbabilityTheory.setBernoulli_ae_subset (u := Ω) (p := p)] with S hSΩ
    have hSfin : S.Finite := hΩ.subset hSΩ
    apply propext
    constructor
    · intro hST
      change f S = T at hST
      have hto : hSfin.toFinset = T := by simpa [f, hSfin] using hST
      ext x
      rw [← hSfin.mem_toFinset, hto]
      rfl
    · intro hST
      change S = ((T : Finset ℕ) : Set ℕ) at hST
      have hset : S = ((T : Finset ℕ) : Set ℕ) := hST
      subst S
      change f ((T : Finset ℕ) : Set ℕ) = T
      simp [f]
  rw [hmap, MeasureTheory.measureReal_congr hpre_ae]
  simpa [Set.ncard_coe_finset, Set.ncard_sdiff' hTΩ hΩ] using
    ProbabilityTheory.setBernoulli_real_singleton
      (u := Ω) (s := ((T : Finset ℕ) : Set ℕ)) p hTΩ hΩ

end

end DenseSetsWithoutLargeSumsets
