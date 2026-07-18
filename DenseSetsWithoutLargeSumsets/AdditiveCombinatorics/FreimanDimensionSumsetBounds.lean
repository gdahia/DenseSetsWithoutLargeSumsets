/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
import Mathlib.Tactic.SetNotationForOrder
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Nat.Choose.Cast
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.Basic
import DenseSetsWithoutLargeSumsets.AdditiveCombinatorics.SumOfSetsInSeveralDimensions

/-!
# Sumset bounds from Freiman dimension

This file transports geometric sumset bounds through rational Freiman models and derives lower
bounds for the sumset of two sets from the Freiman dimension of their union.
-/

namespace DenseSetsWithoutLargeSumsets

open scoped Pointwise Affine

noncomputable section

/-- The real image of a finite set under a rational Freiman model. -/
def freimanRealImage {G : Type*} [DecidableEq G] {d : ℕ}
    (f : G → (Fin d → ℚ)) (S : Finset G) : Finset (Fin d → ℝ) :=
  (S.image f).image rationalVectorToReal

/-- Rational coordinate vectors embed injectively into real coordinate vectors. -/
lemma rationalVectorToReal_injective {d : ℕ} :
    Function.Injective (rationalVectorToReal (d := d)) := by
  intro x y hxy
  ext i
  have : (x i : ℝ) = (y i : ℝ) := congrFun hxy i
  exact_mod_cast this

lemma rationalVectorToReal_add {d : ℕ} (x y : Fin d → ℚ) :
    rationalVectorToReal (x + y) = rationalVectorToReal x + rationalVectorToReal y := by
  ext i
  simp [rationalVectorToReal]

lemma card_image_eq_of_kernel_iff {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    {s : Finset α} {f : α → β} {g : α → γ}
    (h : ∀ x ∈ s, ∀ y ∈ s, (f x = f y ↔ g x = g y)) :
    (s.image f).card = (s.image g).card := by
  classical
  refine Finset.card_bij
    (fun b hb => g (Classical.choose (Finset.mem_image.mp hb))) ?_ ?_ ?_
  · intro b hb
    exact Finset.mem_image.2
      ⟨Classical.choose (Finset.mem_image.mp hb),
        (Classical.choose_spec (Finset.mem_image.mp hb)).1, rfl⟩
  · intro b₁ hb₁ b₂ hb₂ hgb
    obtain ⟨hx₁, hfb₁⟩ := Classical.choose_spec (Finset.mem_image.mp hb₁)
    obtain ⟨hx₂, hfb₂⟩ := Classical.choose_spec (Finset.mem_image.mp hb₂)
    exact hfb₁ ▸ hfb₂ ▸ (h _ hx₁ _ hx₂).2 hgb
  · intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    have hfx : f x ∈ s.image f := Finset.mem_image.2 ⟨x, hx, rfl⟩
    refine ⟨f x, hfx, ?_⟩
    obtain ⟨hy, hfy⟩ := Classical.choose_spec (Finset.mem_image.mp hfx)
    exact (h _ hy _ hx).1 hfy

lemma card_add_freimanRealImage {G : Type*} [DecidableEq G] [AddCommMonoid G]
    {r : ℕ} {X A B : Finset G} {f : G → (Fin r → ℚ)}
    (hiso : IsAddFreimanIso 2 (X : Set G)
      ((X.image f : Finset (Fin r → ℚ)) : Set (Fin r → ℚ)) f)
    (hAX : A ⊆ X) (hBX : B ⊆ X) :
    (freimanRealImage f A + freimanRealImage f B).card = (A + B).card := by
  classical
  let s : Finset (G × G) := A ×ˢ B
  let g : G × G → G := fun p => p.1 + p.2
  let h : G × G → (Fin r → ℝ) := fun p => rationalVectorToReal (f p.1 + f p.2)
  have hsum :
      freimanRealImage f A + freimanRealImage f B = s.image h := by
    ext y
    constructor
    · intro hy
      rw [Finset.mem_add] at hy
      obtain ⟨a', ha', b', hb', rfl⟩ := hy
      rw [freimanRealImage, Finset.mem_image] at ha' hb'
      obtain ⟨az, haz, rfl⟩ := ha'
      obtain ⟨bz, hbz, rfl⟩ := hb'
      rw [Finset.mem_image] at haz hbz
      obtain ⟨a, ha, rfl⟩ := haz
      obtain ⟨b, hb, rfl⟩ := hbz
      exact Finset.mem_image.2
        ⟨(a, b), by simp [s, ha, hb], by simp [h, rationalVectorToReal_add]⟩
    · intro hy
      rw [Finset.mem_image] at hy
      obtain ⟨p, hp, rfl⟩ := hy
      rw [Finset.mem_product] at hp
      rw [Finset.mem_add]
      refine ⟨rationalVectorToReal (f p.1), ?_, rationalVectorToReal (f p.2), ?_, ?_⟩
      · exact Finset.mem_image.2 ⟨f p.1, Finset.mem_image.2 ⟨p.1, hp.1, rfl⟩, rfl⟩
      · exact Finset.mem_image.2 ⟨f p.2, Finset.mem_image.2 ⟨p.2, hp.2, rfl⟩, rfl⟩
      · simp [h, rationalVectorToReal_add]
  have horig : A + B = s.image g := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_add] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact Finset.mem_image.2 ⟨(a, b), by simp [s, ha, hb], rfl⟩
    · intro hx
      rw [Finset.mem_image] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      rw [Finset.mem_product] at hp
      rw [Finset.mem_add]
      exact ⟨p.1, hp.1, p.2, hp.2, rfl⟩
  rw [hsum, horig]
  apply card_image_eq_of_kernel_iff
  intro x hx y hy
  rw [Finset.mem_product] at hx hy
  constructor
  · intro hxy
    exact (hiso.add_eq_add (hAX hx.1) (hBX hx.2) (hAX hy.1) (hBX hy.2)).1
      (rationalVectorToReal_injective hxy)
  · intro hxy
    exact congrArg rationalVectorToReal
      ((hiso.add_eq_add (hAX hx.1) (hBX hx.2) (hAX hy.1) (hBX hy.2)).2 hxy)

/--
Auxiliary transport lemma: a Freiman model preserves the cardinal comparison between `B` and `A`
after taking real coordinate images.
-/
lemma card_freimanRealImage_le {G : Type*} [DecidableEq G] [AddCommMonoid G]
    {r : ℕ} {X A B : Finset G} {f : G → (Fin r → ℚ)}
    (hiso : IsAddFreimanIso 2 (X : Set G)
      ((X.image f : Finset (Fin r → ℚ)) : Set (Fin r → ℚ)) f)
    (hAX : A ⊆ X) (hBX : B ⊆ X) :
    B.card ≤ A.card → (freimanRealImage f B).card ≤ (freimanRealImage f A).card := by
  intro hBA
  rw [freimanRealImage, Finset.card_image_of_injective _ rationalVectorToReal_injective,
    Finset.card_image_of_injOn (hiso.bijOn.injOn.mono fun _ h => hBX h),
    freimanRealImage, Finset.card_image_of_injective _ rationalVectorToReal_injective,
    Finset.card_image_of_injOn (hiso.bijOn.injOn.mono fun _ h => hAX h)]
  exact hBA

/-- The affine span of `A ∪ B` has dimension at most one more than the affine span of `A + B`. -/
lemma finsetAffineDim_union_le_sum_add_one {D : ℕ} (A B : Finset (Fin D → ℝ))
    (hA : A.Nonempty) (hB : B.Nonempty) :
    finsetAffineDim (A ∪ B) ≤ finsetAffineDim (A + B) + 1 := by
  classical
  rcases hA with ⟨a, ha⟩
  rcases hB with ⟨b, hb⟩
  let V := Fin D → ℝ
  let U : Submodule ℝ V := (affineSpan ℝ ((A + B : Finset V) : Set V)).direction
  let L : Submodule ℝ V := Submodule.span ℝ ({b - a} : Set V)
  have hdir :
      (affineSpan ℝ ((A ∪ B : Finset V) : Set V)).direction ≤ U ⊔ L := by
    rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ
      (s := ((A ∪ B : Finset V) : Set V)) (p := a)]
    · apply Submodule.span_le.mpr
      rintro v ⟨x, hx, rfl⟩
      rw [Finset.mem_coe, Finset.mem_union] at hx
      rcases hx with hxA | hxB
      · apply (le_sup_left : U ≤ U ⊔ L)
        simpa [U, vsub_eq_sub, add_sub_add_right_eq_sub] using
          (affineSpan ℝ ((A + B : Finset V) : Set V)).vsub_mem_direction
            (subset_affineSpan ℝ ((A + B : Finset V) : Set V) (Finset.add_mem_add hxA hb))
            (subset_affineSpan ℝ ((A + B : Finset V) : Set V) (Finset.add_mem_add ha hb))
      · change (x -ᵥ a : V) ∈ ↑(U ⊔ L)
        convert (U ⊔ L).add_mem (x := x - b) (y := b - a) ?_ ?_ using 1
        · simp only [vsub_eq_sub]
          abel
        · apply (le_sup_left : U ≤ U ⊔ L)
          simpa [U, vsub_eq_sub, add_comm, add_left_comm, add_assoc] using
            (affineSpan ℝ ((A + B : Finset V) : Set V)).vsub_mem_direction
              (subset_affineSpan ℝ ((A + B : Finset V) : Set V) (Finset.add_mem_add ha hxB))
              (subset_affineSpan ℝ ((A + B : Finset V) : Set V) (Finset.add_mem_add ha hb))
        · apply (le_sup_right : L ≤ U ⊔ L)
          apply Submodule.subset_span
          simp
    · simp [ha]
  refine (Submodule.finrank_mono hdir).trans ?_
  refine (Submodule.finrank_add_le_finrank_add_finrank U L).trans ?_
  apply Nat.add_le_add_left
  simpa [L] using finrank_span_le_card (s := ({b - a} : Set V))

/--
Auxiliary transport lemma: if `X` has Freiman dimension `r`, then the affine dimension of the
model of `A + B` is at least `r - 1`.
-/
lemma freimanDim_le_sumsetAffineDim_add_one
    {G : Type*} [DecidableEq G] [AddCommMonoid G]
    {r : ℕ} {X A B : Finset G} {f : G → (Fin r → ℚ)}
    (_hiso : IsAddFreimanIso 2 (X : Set G)
      ((X.image f : Finset (Fin r → ℚ)) : Set (Fin r → ℚ)) f)
    (haff : finsetAffineDim ((X.image f).image rationalVectorToReal) = r)
    (_hAX : A ⊆ X) (_hBX : B ⊆ X) (hX : X ⊆ A ∪ B)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    r ≤ finsetAffineDim (freimanRealImage f A + freimanRealImage f B) + 1 := by
  refine haff.symm.trans_le ?_
  refine (finsetAffineDim_mono (T := freimanRealImage f A ∪ freimanRealImage f B) ?_).trans ?_
  · intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [Finset.mem_image] at hz
    obtain ⟨x, hxX, rfl⟩ := hz
    rcases Finset.mem_union.mp (hX hxX) with hxA | hxB
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.2 ⟨f x,
        Finset.mem_image.2 ⟨x, hxA, rfl⟩, rfl⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.2 ⟨f x,
        Finset.mem_image.2 ⟨x, hxB, rfl⟩, rfl⟩))
  · apply finsetAffineDim_union_le_sum_add_one
    · rw [freimanRealImage, Finset.image_nonempty, Finset.image_nonempty]
      exact hA
    · rw [freimanRealImage, Finset.image_nonempty, Finset.image_nonempty]
      exact hB

lemma sub_mul_sub_choose_le_sum_min (b r : ℕ) :
    (r - 1) * b - Nat.choose (r + 1) 2 ≤
      (Finset.Icc 1 (b - 1)).sum (fun t => min (r - 1) (b - t)) := by
  classical
  by_cases hb0 : b = 0
  · simp [hb0]
  by_cases hr0 : r = 0
  · simp [hr0]
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
  have hreflect :
      (Finset.Icc 1 (b - 1)).sum (fun t => min (r - 1) (b - t)) =
        (Finset.Ico 1 b).sum (fun s => min (r - 1) s) := by
    rw [← Finset.Ico_add_one_right_eq_Icc 1 (b - 1)]
    convert
      (Finset.sum_Ico_reflect (fun s => min (r - 1) s) 1
        (m := b) (n := b) (Nat.le_succ b)) using 1
    · congr 2
      all_goals omega
    · congr 2
      all_goals omega
  rw [hreflect]
  by_cases hbr : b ≤ r
  · have hsum :
        (Finset.Ico 1 b).sum (fun s => min (r - 1) s) = Nat.choose b 2 := by
      have hmin :
          (Finset.Ico 1 b).sum (fun s => min (r - 1) s) =
            (Finset.Ico 1 b).sum (fun s => s) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.mem_Ico] at hs
        apply Nat.min_eq_right
        omega
      rw [hmin]
      convert Nat.sum_Icc_choose (b - 1) 1 using 1
      · simp
        congr 2
        all_goals omega
      · congr 1
        all_goals omega
    rw [hsum]
    apply Nat.sub_le_iff_le_add.mpr
    have hq :
        (((r - 1) * b : ℕ) : ℚ) ≤
          (Nat.choose b 2 : ℚ) + (Nat.choose (r + 1) 2 : ℚ) := by
      rw [Nat.cast_mul, Nat.cast_sub hr1, Nat.cast_choose_two ℚ,
        Nat.cast_choose_two ℚ]
      push_cast
      ring_nf
      nlinarith [sq_nonneg ((r : ℚ) - b),
        (0 : ℚ) < r, (Nat.cast_nonneg b : (0 : ℚ) ≤ b)]
    exact_mod_cast hq
  · have hrb : r ≤ b := by omega
    rw [← Finset.sum_Ico_consecutive (fun s => min (r - 1) s) hr1 hrb]
    have hfirst :
        (Finset.Ico 1 r).sum (fun s => min (r - 1) s) = Nat.choose r 2 := by
      have hmin :
          (Finset.Ico 1 r).sum (fun s => min (r - 1) s) =
            (Finset.Ico 1 r).sum (fun s => s) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.mem_Ico] at hs
        apply Nat.min_eq_right
        omega
      rw [hmin]
      convert Nat.sum_Icc_choose (r - 1) 1 using 1
      · simp
        congr 2
        all_goals omega
      · congr 1
        all_goals omega
    have hsecond :
        (Finset.Ico r b).sum (fun s => min (r - 1) s) = (b - r) * (r - 1) := by
      trans (Finset.Ico r b).sum (fun _s => r - 1)
      · apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.mem_Ico] at hs
        apply Nat.min_eq_left
        omega
      · simp [Finset.sum_const, Nat.card_Ico]
    rw [hfirst, hsecond]
    apply Nat.sub_le_iff_le_add.mpr
    have hq :
        (((r - 1) * b : ℕ) : ℚ) ≤
          (Nat.choose r 2 : ℚ) + ((b - r) * (r - 1) : ℕ) +
            (Nat.choose (r + 1) 2 : ℚ) := by
      rw [Nat.cast_mul, Nat.cast_sub hr1, Nat.cast_choose_two ℚ,
        Nat.cast_mul, Nat.cast_sub hrb, Nat.cast_sub hr1, Nat.cast_choose_two ℚ]
      push_cast
      ring_nf
      nlinarith [(by exact_mod_cast hrb : (r : ℚ) ≤ b),
        (0 : ℚ) < r,
        (Nat.cast_nonneg b : (0 : ℚ) ≤ b)]
    exact_mod_cast hq

lemma sub_mul_sub_choose_le_sum_min_of_le {a b r d : ℕ} (hba : b ≤ a) (hrd : r ≤ d + 1) :
    (r - 1) * b - Nat.choose (r + 1) 2 ≤
      (Finset.Icc 1 (b - 1)).sum (fun t => min d (a - t)) := by
  refine (sub_mul_sub_choose_le_sum_min b r).trans ?_
  apply Finset.sum_le_sum
  intro t ht
  rw [Finset.mem_Icc] at ht
  apply min_le_min
  · omega
  · omega

/--
Auxiliary transport lemma: the asymmetric bound obtained in a real Freiman model transfers back to
the original sets, with the arithmetic weakening from affine dimension `d` and `r ≤ d + 1`.
-/
lemma card_add_lower_bound_of_freimanModel {G : Type*} [DecidableEq G] [AddCommMonoid G]
    {r d : ℕ} {X A B : Finset G} {f : G → (Fin r → ℚ)}
    (hiso : IsAddFreimanIso 2 (X : Set G)
      ((X.image f : Finset (Fin r → ℚ)) : Set (Fin r → ℚ)) f)
    (hAX : A ⊆ X) (hBX : B ⊆ X)
    (hBA : B.card ≤ A.card)
    (hrd : r ≤ d + 1)
    (hasym :
      (freimanRealImage f A).card +
          (Finset.Icc 1 ((freimanRealImage f B).card - 1)).sum
            (fun t => min d ((freimanRealImage f A).card - t)) ≤
        (freimanRealImage f A + freimanRealImage f B).card) :
    A.card + (r - 1) * B.card - Nat.choose (r + 1) 2 ≤ (A + B).card := by
  have hAcard : (freimanRealImage f A).card = A.card := by
    rw [freimanRealImage, Finset.card_image_of_injective _ rationalVectorToReal_injective,
      Finset.card_image_of_injOn (hiso.bijOn.injOn.mono fun _ h => hAX h)]
  have hBcard : (freimanRealImage f B).card = B.card := by
    rw [freimanRealImage, Finset.card_image_of_injective _ rationalVectorToReal_injective,
      Finset.card_image_of_injOn (hiso.bijOn.injOn.mono fun _ h => hBX h)]
  rw [hAcard, hBcard, card_add_freimanRealImage hiso hAX hBX] at hasym
  suffices A.card + ((r - 1) * B.card - Nat.choose (r + 1) 2) ≤ (A + B).card by omega
  exact (Nat.add_le_add_left (sub_mul_sub_choose_le_sum_min_of_le hBA hrd) A.card).trans hasym

/-- A sumset lower bound in terms of the Freiman dimension of the union. -/
lemma card_add_lower_bound_of_freimanDim_union {G : Type*} [DecidableEq G] [AddCommMonoid G] (r : ℕ)
    (A B : Finset G) (hr : 1 ≤ r) (hA : A.Nonempty) (hB : B.Nonempty)
    (hBA : B.card ≤ A.card)
    (hdim : freimanDim (A ∪ B) = r) :
    A.card + (r - 1) * B.card - Nat.choose (r + 1) 2 ≤ (A + B).card := by
  classical
  obtain ⟨f, hiso, haff⟩ := Nat.findGreatest_of_ne_zero hdim (Nat.ne_of_gt hr)
  let A₁ := freimanRealImage f A
  let B₁ := freimanRealImage f B
  let d := finsetAffineDim (A₁ + B₁)
  refine card_add_lower_bound_of_freimanModel (d := d) hiso Finset.subset_union_left
    Finset.subset_union_right hBA ?_ ?_
  · dsimp [d, A₁, B₁]
    exact freimanDim_le_sumsetAffineDim_add_one hiso haff Finset.subset_union_left
      Finset.subset_union_right Finset.Subset.rfl hA hB
  · refine card_add_lower_bound_of_affineDim A₁ B₁ ?_ ?_ rfl
    · dsimp [B₁]
      rw [freimanRealImage, Finset.image_nonempty, Finset.image_nonempty]
      exact hB
    · dsimp [A₁, B₁]
      exact card_freimanRealImage_le hiso Finset.subset_union_left Finset.subset_union_right hBA

/-- The unweakened sumset lower bound in terms of the Freiman dimension of the union. -/
lemma card_add_sum_min_le_of_freimanDim_union {G : Type*} [DecidableEq G] [AddCommMonoid G] (r : ℕ)
    (A B : Finset G) (hr : 1 ≤ r) (hA : A.Nonempty) (hB : B.Nonempty)
    (hBA : B.card ≤ A.card)
    (hdim : freimanDim (A ∪ B) = r) :
    A.card + (Finset.Icc 1 (B.card - 1)).sum
        (fun t => min (r - 1) (A.card - t)) ≤ (A + B).card := by
  classical
  obtain ⟨f, hiso, haff⟩ := Nat.findGreatest_of_ne_zero hdim (Nat.ne_of_gt hr)
  let A₁ := freimanRealImage f A
  let B₁ := freimanRealImage f B
  let d := finsetAffineDim (A₁ + B₁)
  have hAcard : A₁.card = A.card := by
    dsimp [A₁]
    rw [freimanRealImage, Finset.card_image_of_injective _ rationalVectorToReal_injective,
      Finset.card_image_of_injOn (hiso.bijOn.injOn.mono Finset.subset_union_left)]
  have hBcard : B₁.card = B.card := by
    dsimp [B₁]
    rw [freimanRealImage, Finset.card_image_of_injective _ rationalVectorToReal_injective,
      Finset.card_image_of_injOn (hiso.bijOn.injOn.mono Finset.subset_union_right)]
  rw [← card_add_freimanRealImage hiso Finset.subset_union_left Finset.subset_union_right]
  refine le_trans (b := A.card + (Finset.Icc 1 (B₁.card - 1)).sum
    (fun t => min d (A₁.card - t))) ?_ ?_
  · apply Nat.add_le_add_left
    rw [hBcard]
    apply Finset.sum_le_sum
    intro t ht
    rw [hAcard]
    apply min_le_min
    · have : r ≤ d + 1 :=
        freimanDim_le_sumsetAffineDim_add_one hiso haff Finset.subset_union_left
          Finset.subset_union_right Finset.Subset.rfl hA hB
      omega
    · exact le_rfl
  · rw [← hAcard]
    refine card_add_lower_bound_of_affineDim A₁ B₁ ?_ ?_ rfl
    · dsimp [B₁]
      rw [freimanRealImage, Finset.image_nonempty, Finset.image_nonempty]
      exact hB
    · dsimp [A₁, B₁]
      rw [hAcard, hBcard]
      exact hBA

end

end DenseSetsWithoutLargeSumsets
