import VerifiedAgora.tagger
/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.Distribution.Basic
import PhysLean.SpaceAndTime.Space.Basic
/-!

# The radial angular measure on Space

## i. Overview

The normal measure on `Space d` is `r^(d-1) dr dΩ` in spherical coordinates,
where `dΩ` is the angular measure on the unit sphere. The radial angular measure
is the measure `dr dΩ`, cancelling the radius contribution from the measure in spherical
coordinates.

This file is equivalent to `invPowMeasure`, which will slowly be deprecated.

## ii. Key results

- `radialAngularMeasure`: The radial angular measure on `Space d`.

## iii. Table of contents

- A. The definition of the radial angular measure
  - A.1. Basic equalities
- B. Integrals with respect to radialAngularMeasure
- C. HasTemperateGrowth of measures
  - C.1. Integrability of powers
  - C.2. radialAngularMeasure has temperate growth

## iv. References

-/
open SchwartzMap NNReal
noncomputable section

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F']

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory

/-!

## A. The definition of the radial angular measure

-/

/-- The measure on `Space d` weighted by `1 / ‖x‖ ^ (d - 1)`. -/
def radialAngularMeasure {d : ℕ} : Measure (Space d) :=
  volume.withDensity (fun x : Space d => ENNReal.ofReal (1 / ‖x‖ ^ (d - 1)))

/-!

### A.1. Basic equalities

-/

lemma radialAngularMeasure_eq_volume_withDensity {d : ℕ} : radialAngularMeasure =
    volume.withDensity (fun x : Space d => ENNReal.ofReal (1 / ‖x‖ ^ (d - 1))) := by
  rfl

@[simp]
lemma radialAngularMeasure_zero_eq_volume :
    radialAngularMeasure (d := 0) = volume := by
  simp [radialAngularMeasure]

lemma integrable_radialAngularMeasure_iff {d : ℕ} {f : Space d → F} :
    Integrable f (radialAngularMeasure (d := d)) ↔
      Integrable (fun x => (1 / ‖x‖ ^ (d - 1)) • f x) volume := by
  dsimp [radialAngularMeasure]
  erw [integrable_withDensity_iff_integrable_smul₀ (by fun_prop)]
  simp only [one_div]
  refine integrable_congr ?_
  filter_upwards with x
  rw [Real.toNNReal_of_nonneg, NNReal.smul_def]
  simp only [inv_nonneg, norm_nonneg, pow_nonneg, coe_mk]
  positivity

/-!

## B. Integrals with respect to radialAngularMeasure

-/

lemma integral_radialAngularMeasure {d : ℕ} (f : Space d → F) :
    ∫ x, f x ∂radialAngularMeasure = ∫ x, (1 / ‖x‖ ^ (d - 1)) • f x := by
  dsimp [radialAngularMeasure]
  erw [integral_withDensity_eq_integral_smul (by fun_prop)]
  congr
  funext x
  simp only [one_div]
  refine Eq.symm (Mathlib.Tactic.LinearCombination.smul_eq_const ?_ (f x))
  simp

/-!

## C. HasTemperateGrowth of measures

-/

/-!

### C.1. Integrability of powers

-/
private lemma integrable_neg_pow_on_ioi (n : ℕ) :
    IntegrableOn (fun x : ℝ => (|((1 : ℝ) + ↑x) ^ (- (n + 2) : ℝ)|)) (Set.Ioi 0) := by
  rw [MeasureTheory.integrableOn_iff_comap_subtypeVal]
  rw [← MeasureTheory.integrable_smul_measure (c := n + 1)]
  apply MeasureTheory.integrable_of_integral_eq_one
  trans (n + 1) * ∫ (x : ℝ) in Set.Ioi 0, ((1 + x) ^ (- (n + 2) : ℝ)) ∂volume
  · rw [← MeasureTheory.integral_subtype_comap]
    simp only [neg_add_rev, Function.comp_apply, integral_smul_measure, smul_eq_mul]
    congr
    funext x
    simp only [abs_eq_self]
    apply Real.rpow_nonneg
    apply add_nonneg
    · exact zero_le_one' ℝ
    · exact le_of_lt x.2
    exact measurableSet_Ioi
  have h0 (x : ℝ) (hx : x ∈ Set.Ioi 0) : ((1 : ℝ) + ↑x) ^ (- (n + 2) : ℝ) =
      ((1 + x) ^ ((n + 2)))⁻¹ := by
    rw [← Real.rpow_natCast]
    rw [← Real.inv_rpow]
    rw [← Real.rpow_neg_one, ← Real.rpow_mul]
    simp only [neg_mul, one_mul]
    simp only [neg_add_rev, Nat.cast_add, Nat.cast_ofNat]
    have hx : 0 < x := hx
    positivity
    apply add_nonneg
    · exact zero_le_one' ℝ
    · exact le_of_lt hx
  trans (n + 1) * ∫ (x : ℝ) in Set.Ioi 0, ((1 + x) ^ (n + 2))⁻¹ ∂volume
  · congr 1
    refine setIntegral_congr_ae₀ ?_ ?_
    · simp
    filter_upwards with x hx
    rw [h0 x hx]
  trans (n + 1) * ∫ (x : ℝ) in Set.Ioi 1, (x ^ (n + 2))⁻¹ ∂volume
  · congr 1
    let f := fun x : ℝ => (x ^ (n + 2))⁻¹
    change ∫ (x : ℝ) in Set.Ioi 0, f (1 + x) ∂volume = ∫ (x : ℝ) in Set.Ioi 1, f x ∂volume
    let fa := fun x : ℝ => 1 + x
    change ∫ (x : ℝ) in Set.Ioi 0, f (fa x) ∂volume = _
    rw [← MeasureTheory.MeasurePreserving.setIntegral_image_emb (ν := volume)]
    simp [fa]
    simp [fa]
    exact measurePreserving_add_left volume 1
    simp [fa]
    exact measurableEmbedding_addLeft 1
  · trans (n + 1) * ∫ (x : ℝ) in Set.Ioi 1, (x ^ (- (n + 2) : ℝ)) ∂volume
    · congr 1
      refine setIntegral_congr_ae₀ ?_ ?_
      · simp
      filter_upwards with x hx
      have hx : 1 < x := hx
      rw [← Real.rpow_natCast]
      rw [← Real.inv_rpow]
      rw [← Real.rpow_neg_one, ← Real.rpow_mul]
      simp only [neg_mul, one_mul]
      simp only [Nat.cast_add, Nat.cast_ofNat, neg_add_rev]
      positivity
      positivity
    rw [integral_Ioi_rpow_of_lt]
    field_simp
    have h0 : (-2 + -(n : ℝ) + 1) ≠ 0 := by
      by_contra h
      have h1 : (1 : ℝ) - 0 = 2 + n := by
        rw [← h]
        ring
      simp at h1
      linarith
    simp only [neg_add_rev, Real.one_rpow, mul_one]
    field_simp
    ring
    linarith
    linarith
  · simp
  · simp
  · simp

lemma radialAngularMeasure_integrable_pow_neg_two {d : ℕ} :
    Integrable (fun x : Space d => (1 + ‖x‖) ^ (- (d + 1) : ℝ))
      radialAngularMeasure := by
  match d with
  | 0 => simp
  | dm1 + 1 =>
  suffices h1 : Integrable (fun x => (1 + ‖x‖) ^ (-(dm1 + 2) : ℝ)) radialAngularMeasure by
    convert h1 using 3
    grind
  simp [radialAngularMeasure]
  rw [MeasureTheory.integrable_withDensity_iff]
  swap
  · fun_prop
  swap
  · rw [@ae_iff]
    simp
  conv =>
    enter [1, i]
    rw [ENNReal.toReal_ofReal (by positivity)]
  have h1 := (MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd
    (volume (α := Space dm1.succ)))
  have h2 : IntegrableOn (fun x : Space dm1.succ =>
      ((1 + ‖x‖) ^ (- (dm1 + 2) : ℝ)) * (‖x‖ ^ dm1)⁻¹) {0}ᶜ := by
    rw [MeasureTheory.integrableOn_iff_comap_subtypeVal]
    swap
    · refine MeasurableSet.compl_iff.mpr ?_
      simp
    let f := (fun x :Space dm1.succ =>
        ((1 + ‖x‖) ^ (- (dm1 + 2) : ℝ)) * (‖x‖ ^ dm1)⁻¹)
      ∘ @Subtype.val (Space dm1.succ) fun x =>
        (@Membership.mem (Space dm1.succ)
          (Set (Space dm1.succ)) Set.instMembership {0}ᶜ x)
    have hf : (f ∘ (homeomorphUnitSphereProd (Space dm1.succ)).symm)∘
      (homeomorphUnitSphereProd (Space dm1.succ)) = f := by
      funext x
      simp
    change Integrable f _
    rw [← hf]
    refine (h1.integrable_comp_emb ?_).mpr ?_
    · exact Homeomorph.measurableEmbedding
        (homeomorphUnitSphereProd (Space dm1.succ))
    haveI sfinite : SFinite (@Measure.comap ↑(Set.Ioi 0) ℝ Subtype.instMeasurableSpace
        Real.measureSpace.toMeasurableSpace Subtype.val volume) := by
      refine { out' := ?_ }
      have h1 := SFinite.out' (μ := volume (α := ℝ))
      obtain ⟨m, h⟩ := h1
      use fun n => Measure.comap Subtype.val (m n)
      apply And.intro
      · intro n
        refine (isFiniteMeasure_iff (Measure.comap Subtype.val (m n))).mpr ?_
        rw [MeasurableEmbedding.comap_apply]
        simp only [Set.image_univ, Subtype.range_coe_subtype, Set.mem_Ioi]
        have hm := h.1 n
        exact measure_lt_top (m n) {x | 0 < x}
        exact MeasurableEmbedding.subtype_coe measurableSet_Ioi
      · ext s hs
        rw [MeasurableEmbedding.comap_apply, Measure.sum_apply]
        conv_rhs =>
          enter [1, i]
          rw [MeasurableEmbedding.comap_apply (MeasurableEmbedding.subtype_coe measurableSet_Ioi)]
        have h2 := h.2
        rw [Measure.ext_iff'] at h2
        rw [← Measure.sum_apply]
        exact h2 (Subtype.val '' s)
        refine MeasurableSet.subtype_image measurableSet_Ioi hs
        exact hs
        exact MeasurableEmbedding.subtype_coe measurableSet_Ioi
    have hf' : (f ∘ (homeomorphUnitSphereProd (Space dm1.succ)).symm) =
      fun x =>((1 + x.2.val) ^ (- (dm1 + 2) : ℝ)) * (x.2.val ^ dm1)⁻¹ := by
      funext x
      simp only [Function.comp_apply, homeomorphUnitSphereProd_symm_apply_coe, f]
      rw [norm_smul]
      simp only [Real.norm_eq_abs, norm_eq_of_mem_sphere, mul_one]
      rw [abs_of_nonneg (le_of_lt x.2.2)]
    rw [hf']
    simp [Measure.volumeIoiPow]
    rw [MeasureTheory.prod_withDensity_right]
    swap
    · fun_prop
    rw [MeasureTheory.integrable_withDensity_iff]
    swap
    · refine Measurable.ennreal_ofReal ?_
      refine Measurable.pow_const ?_ dm1
      apply Measurable.comp
      · exact measurable_subtype_coe
      · exact measurable_snd
    swap
    · apply Filter.Eventually.of_forall
      intro x
      exact ENNReal.ofReal_lt_top
    have hf'' : (fun (x : ↑(Metric.sphere (α := (Space dm1.succ)) 0 1) ×
        ↑(Set.Ioi (α := ℝ) 0)) =>
        (((1 + x.2.val) ^ (- (dm1 + 2) : ℝ)) * (x.2.val ^ dm1)⁻¹ *
          (ENNReal.ofReal (↑x.2.val ^ dm1)).toReal))
        = fun x => ((1 + x.2.val) ^ (- (dm1 + 2) : ℝ)) := by
      funext x
      rw [ENNReal.toReal_ofReal]
      generalize (1 + ↑x.2.val)= l
      ring_nf
      have h2 : x.2.val ≠ 0 := by
        have h' := x.2.2
        simp [- Subtype.coe_prop] at h'
        linarith
      field_simp
      ring_nf
      simp only [Nat.succ_eq_add_one, inv_pow]
      field_simp
      exact pow_nonneg (le_of_lt x.2.2) dm1
    simp at hf''
    rw [hf'']
    apply (MeasureTheory.integrable_prod_iff' ?_).mpr ?_
    · refine aestronglyMeasurable_iff_aemeasurable.mpr ?_
      fun_prop
    · simp
      apply Integrable.const_mul
      have h1 := integrable_neg_pow_on_ioi dm1
      rw [MeasureTheory.integrableOn_iff_comap_subtypeVal] at h1
      simpa using h1
      exact measurableSet_Ioi
  rw [← MeasureTheory.integrableOn_univ]
  simp only [Nat.succ_eq_add_one, neg_add_rev] at h2
  apply MeasureTheory.IntegrableOn.congr_set_ae h2
  rw [← MeasureTheory.ae_eq_set_compl]
  trans (∅ : Set (Space dm1.succ))
  · apply Filter.EventuallyEq.of_eq
    rw [← Set.compl_empty]
    exact compl_compl _
  · symm
    simp

/-!

### C.2. radialAngularMeasure has temperate growth

-/

instance (d : ℕ) : Measure.HasTemperateGrowth (radialAngularMeasure (d := d)) where
  exists_integrable := by
    use d + 1
    simpa using radialAngularMeasure_integrable_pow_neg_two (d := d)

end Space
