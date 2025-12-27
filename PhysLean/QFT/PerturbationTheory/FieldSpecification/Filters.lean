import VerifiedAgora.tagger
/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.PerturbationTheory.FieldSpecification.CrAnFieldOp
/-!

# Filters of lists of CrAnFieldOp

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}

/-- Given a list of creation and annihilation states, the filtered list only containing
  the creation states. As a schematic example, for the list:
  - `[φ1c, φ1a, φ2c, φ2a]` this will return `[φ1c, φ2c]`.
-/
/-- Given a list of creation and annihilation states, the filtered list only containing
  the creation states. As a schematic example, for the list:
  - `[φ1c, φ1a, φ2c, φ2a]` this will return `[φ1c, φ2c]`.
-/
def createFilter (φs : List 𝓕.CrAnFieldOp) : List 𝓕.CrAnFieldOp := by sorry


@[target] lemma createFilter_cons_create {φ : 𝓕.CrAnFieldOp}
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create) (φs : List 𝓕.CrAnFieldOp) :
    createFilter (φ :: φs) = φ :: createFilter φs := by
  sorry


@[target] lemma createFilter_cons_annihilate {φ : 𝓕.CrAnFieldOp}
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate) (φs : List 𝓕.CrAnFieldOp) :
    createFilter (φ :: φs) = createFilter φs := by
  sorry


@[target] lemma createFilter_append (φs φs' : List 𝓕.CrAnFieldOp) :
    createFilter (φs ++ φs') = createFilter φs ++ createFilter φs' := by
  sorry


lemma createFilter_singleton_create (φ : 𝓕.CrAnFieldOp)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create) :
    createFilter [φ] = [φ] := by
  simp [createFilter, hφ]

lemma createFilter_singleton_annihilate (φ : 𝓕.CrAnFieldOp)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate) : createFilter [φ] = [] := by
  simp [createFilter, hφ]

/-- Given a list of creation and annihilation states, the filtered list only containing
  the annihilation states.
  As a schematic example, for the list:
  - `[φ1c, φ1a, φ2c, φ2a]` this will return `[φ1a, φ2a]`.
-/
def annihilateFilter (φs : List 𝓕.CrAnFieldOp) : List 𝓕.CrAnFieldOp :=
  List.filter (fun φ => 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate) φs

@[target] lemma annihilateFilter_cons_create {φ : 𝓕.CrAnFieldOp}
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create) (φs : List 𝓕.CrAnFieldOp) :
    annihilateFilter (φ :: φs) = annihilateFilter φs := by
  sorry


lemma annihilateFilter_cons_annihilate {φ : 𝓕.CrAnFieldOp}
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate) (φs : List 𝓕.CrAnFieldOp) :
    annihilateFilter (φ :: φs) = φ :: annihilateFilter φs := by
  simp only [annihilateFilter]
  rw [List.filter_cons_of_pos]
  simp [hφ]

@[target] lemma annihilateFilter_append (φs φs' : List 𝓕.CrAnFieldOp) :
    annihilateFilter (φs ++ φs') = annihilateFilter φs ++ annihilateFilter φs' := by
  sorry


@[target] lemma annihilateFilter_singleton_create (φ : 𝓕.CrAnFieldOp)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create) :
    annihilateFilter [φ] = [] := by
  sorry


@[target] lemma annihilateFilter_singleton_annihilate (φ : 𝓕.CrAnFieldOp)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate) :
    annihilateFilter [φ] = [φ] := by
  sorry


end FieldSpecification
