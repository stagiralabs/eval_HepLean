import VerifiedAgora.tagger
/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.AnomalyCancellation.Basic
/-!

# Anomaly cancellation conditions for the Standard Model with right-handed neutrinos

This directory is related to the anomaly cancellation conditions (ACCs) for the Standard Model with
right-handed neutrinos (SMν).

-/

open Nat
open BigOperators

/-- The vector space of charges corresponding to the SM fermions with RHN. -/
@[simps!]
def SMνCharges (n : ℕ) : ACCSystemCharges := ACCSystemChargesMk (6 * n)

/-- The vector spaces of charges of one species of fermions in the SM. -/
@[simps!]
def SMνSpecies (n : ℕ) : ACCSystemCharges := ACCSystemChargesMk n

namespace SMνCharges

variable {n : ℕ}

/-- An equivalence between `(SMνCharges n).charges` and `(Fin 6 → Fin n → ℚ)`
splitting the charges into species. -/
/-- An equivalence between the set `(SMCharges n).charges` and the set
  `(Fin 5 → Fin n → ℚ)`. -/
@[simps!]
def toSpeciesEquiv : (SMCharges n).Charges ≃ (Fin 5 → Fin n → ℚ) := by sorry


/-- Given an `i ∈ Fin 6`, the projection of charges onto a given species. -/
/-- For a given `i ∈ Fin 5`, the projection of a charge onto that species. -/
@[simps!]
def toSpecies (i : Fin 5) : (SMCharges n).Charges →ₗ[ℚ] (SMSpecies n).Charges where
  toFun S := toSpeciesEquiv S i
  map_add' _ _ := by sorry


@[target] lemma charges_eq_toSpecies_eq (S T : (SMCharges n).Charges) :
    S = T ↔ ∀ i, toSpecies i S = toSpecies i T := by
  sorry


@[target] lemma toSMSpecies_toSpecies_inv (i : Fin 5) (f : Fin 5 → Fin n → ℚ) :
    (toSpecies i) (toSpeciesEquiv.symm f) = f i := by
  sorry


lemma toSpecies_one (S : (SMνCharges 1).Charges) (j : Fin 6) :
    toSpecies j S ⟨0, zero_lt_succ 0⟩ = S j := by
  match j with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl

/-- The `Q` charges as a map `Fin n → ℚ`. -/
/-- The `Q` charges as a map `Fin n → ℚ`. -/
abbrev Q := by sorry

/-- The `U` charges as a map `Fin n → ℚ`. -/
/-- The `U` charges as a map `Fin n → ℚ`. -/
abbrev U := by sorry

/-- The `D` charges as a map `Fin n → ℚ`. -/
/-- The `D` charges as a map `Fin n → ℚ`. -/
abbrev D := by sorry

/-- The `L` charges as a map `Fin n → ℚ`. -/
/-- The `L` charges as a map `Fin n → ℚ`. -/
abbrev L := by sorry

/-- The `E` charges as a map `Fin n → ℚ`. -/
/-- The `E` charges as a map `Fin n → ℚ`. -/
abbrev E := by sorry

/-- The `N` charges as a map `Fin n → ℚ`. -/
abbrev N := @toSpecies n 5

end SMνCharges

namespace SMνACCs

open SMνCharges

variable {n : ℕ}

/-- The gravitational anomaly equation. -/
open BigOperators in
/-- The gravitational anomaly. -/
def accGrav (n : ℕ) : ((PureU1Charges n).Charges →ₗ[ℚ] ℚ) where
  toFun S := ∑ i : Fin n, S i
  map_add' S T := Finset.sum_add_distrib
  map_smul' a S := by
    sorry


lemma accGrav_decomp (S : (SMνCharges n).Charges) :
    accGrav S = 6 * ∑ i, Q S i + 3 * ∑ i, U S i + 3 * ∑ i, D S i + 2 * ∑ i, L S i + ∑ i, E S i +
      ∑ i, N S i := by
  simp only [accGrav, SMνSpecies_numberCharges, toSpecies_apply, Fin.isValue, LinearMap.coe_mk,
    AddHom.coe_mk]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]

/-- Extensionality lemma for `accGrav`. -/
/-- Extensionality lemma for `accGrav`. -/
@[target] lemma accGrav_ext {S T : (SMCharges n).Charges}
    (hj : ∀ (j : Fin 5), ∑ i, (toSpecies j) S i = ∑ i, (toSpecies j) T i) :
    accGrav S = accGrav T := by
  sorry


/-- The `SU(2)` anomaly equation. -/
/-- The `SU(2)` anomaly equation. -/
@[simp]
def accSU2 : (SMCharges n).Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (3 * Q S i + L S i)
  map_add' S T := by
    sorry


lemma accSU2_decomp (S : (SMνCharges n).Charges) :
    accSU2 S = 3 * ∑ i, Q S i + ∑ i, L S i := by
  simp only [accSU2, SMνSpecies_numberCharges, toSpecies_apply, Fin.isValue, LinearMap.coe_mk,
    AddHom.coe_mk]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]

/-- Extensionality lemma for `accSU2`. -/
/-- Extensionality lemma for `accSU2`. -/
@[target] lemma accSU2_ext {S T : (SMCharges n).Charges}
    (hj : ∀ (j : Fin 5), ∑ i, (toSpecies j) S i = ∑ i, (toSpecies j) T i) :
    accSU2 S = accSU2 T := by
  sorry


/-- The `SU(3)` anomaly equations. -/
/-- The `SU(3)` anomaly equations. -/
@[simp]
def accSU3 : (SMCharges n).Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (2 * Q S i + U S i + D S i)
  map_add' S T := by
    sorry


lemma accSU3_decomp (S : (SMνCharges n).Charges) :
    accSU3 S = 2 * ∑ i, Q S i + ∑ i, U S i + ∑ i, D S i := by
  simp only [accSU3, SMνSpecies_numberCharges, toSpecies_apply, Fin.isValue, LinearMap.coe_mk,
    AddHom.coe_mk]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]

/-- Extensionality lemma for `accSU3`. -/
/-- Extensionality lemma for `accSU3`. -/
@[target] lemma accSU3_ext {S T : (SMCharges n).Charges}
    (hj : ∀ (j : Fin 5), ∑ i, (toSpecies j) S i = ∑ i, (toSpecies j) T i) :
    accSU3 S = accSU3 T := by
  sorry


/-- The `Y²` anomaly equation. -/
/-- The `Y²` anomaly equation. -/
@[simp]
def accYY : (SMCharges n).Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (Q S i + 8 * U S i + 2 * D S i + 3 * L S i
    + 6 * E S i)
  map_add' S T := by
    sorry


lemma accYY_decomp (S : (SMνCharges n).Charges) :
    accYY S = ∑ i, Q S i + 8 * ∑ i, U S i + 2 * ∑ i, D S i + 3 * ∑ i, L S i + 6 * ∑ i, E S i := by
  simp only [accYY, SMνSpecies_numberCharges, toSpecies_apply, Fin.isValue, LinearMap.coe_mk,
    AddHom.coe_mk]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]

/-- Extensionality lemma for `accYY`. -/
/-- Extensionality lemma for `accYY`. -/
@[target] lemma accYY_ext {S T : (SMCharges n).Charges}
    (hj : ∀ (j : Fin 5), ∑ i, (toSpecies j) S i = ∑ i, (toSpecies j) T i) :
    accYY S = accYY T := by
  sorry


/-- The quadratic bilinear map. -/
/-- The quadratic bilinear map. -/
@[simps!]
def quadBiLin : BiLinearSymm (SMCharges n).Charges := BiLinearSymm.mk₂
  (fun S => ∑ i, (Q S.1 i * Q S.2 i +
    - 2 * (U S.1 i * U S.2 i) +
    D S.1 i * D S.2 i +
    (- 1) * (L S.1 i * L S.2 i) +
    E S.1 i * E S.2 i))
  (by
    sorry


lemma quadBiLin_decomp (S T : (SMνCharges n).Charges) :
    quadBiLin S T = ∑ i, Q S i * Q T i - 2 * ∑ i, U S i * U T i +
        ∑ i, D S i * D T i - ∑ i, L S i * L T i + ∑ i, E S i * E T i := by
  erw [← quadBiLin.toFun_eq_coe]
  rw [quadBiLin]
  simp only [BiLinearSymm.mk₂, AddHom.toFun_eq_coe, AddHom.coe_mk, LinearMap.coe_mk]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]
  simp only [SMνSpecies_numberCharges, toSpecies_apply, Fin.isValue, neg_mul, one_mul, add_left_inj]
  ring

/-- The quadratic anomaly cancellation condition. -/
/-- The quadratic anomaly cancellation condition. -/
@[simp]
def accQuad : HomogeneousQuadratic (SMCharges n).Charges := by sorry


lemma accQuad_decomp (S : (SMνCharges n).Charges) :
    accQuad S = ∑ i, (Q S i)^2 - 2 * ∑ i, (U S i)^2 + ∑ i, (D S i)^2 - ∑ i, (L S i)^2
    + ∑ i, (E S i)^2 := by
  erw [quadBiLin_decomp]
  ring_nf

/-- Extensionality lemma for `accQuad`. -/
/-- Extensionality lemma for `accQuad`. -/
@[target] lemma accQuad_ext {S T : (SMCharges n).Charges}
    (h : ∀ j, ∑ i, ((fun a => a^2) ∘ toSpecies j S) i =
    ∑ i, ((fun a => a^2) ∘ toSpecies j T) i) :
    accQuad S = accQuad T := by
  sorry


/-- The symmetric trilinear form used to define the cubic acc. -/
/-- The trilinear function defining the cubic. -/
@[simps!]
def cubeTriLin : TriLinearSymm (SMCharges n).Charges := TriLinearSymm.mk₃
  (fun S => ∑ i, (6 * ((Q S.1 i) * (Q S.2.1 i) * (Q S.2.2 i))
    + 3 * ((U S.1 i) * (U S.2.1 i) * (U S.2.2 i))
    + 3 * ((D S.1 i) * (D S.2.1 i) * (D S.2.2 i))
    + 2 * ((L S.1 i) * (L S.2.1 i) * (L S.2.2 i))
    + ((E S.1 i) * (E S.2.1 i) * (E S.2.2 i))))
  (by
    sorry


lemma cubeTriLin_decomp (S T R : (SMνCharges n).Charges) :
    cubeTriLin S T R = 6 * ∑ i, (Q S i * Q T i * Q R i) + 3 * ∑ i, (U S i * U T i * U R i) +
      3 * ∑ i, (D S i * D T i * D R i) + 2 * ∑ i, (L S i * L T i * L R i) +
      ∑ i, (E S i * E T i * E R i) + ∑ i, (N S i * N T i * N R i) := by
  erw [← cubeTriLin.toFun_eq_coe]
  rw [cubeTriLin]
  simp only [TriLinearSymm.mk₃, BiLinearSymm.mk₂, SMνSpecies_numberCharges, toSpecies_apply,
    Fin.isValue, AddHom.toFun_eq_coe, AddHom.coe_mk, LinearMap.coe_mk]
  repeat erw [Finset.sum_add_distrib]
  repeat erw [← Finset.mul_sum]

/-- The cubic ACC. -/
/-- The cubic anomaly equation. -/
@[simp]
def accCube (n : ℕ) : HomogeneousCubic ((PureU1Charges n).Charges) := by sorry


lemma accCube_decomp (S : (SMνCharges n).Charges) :
    accCube S = 6 * ∑ i, (Q S i)^3 + 3 * ∑ i, (U S i)^3 + 3 * ∑ i, (D S i)^3 + 2 * ∑ i, (L S i)^3 +
      ∑ i, (E S i)^3 + ∑ i, (N S i)^3 := by
  change cubeTriLin S S S = _
  rw [cubeTriLin_decomp]
  ring_nf

/-- Extensionality lemma for `accCube`. -/
/-- Extensionality lemma for `accCube`. -/
@[target] lemma accCube_ext {S T : (SMCharges n).Charges}
    (h : ∀ j, ∑ i, ((fun a => a^3) ∘ toSpecies j S) i =
    ∑ i, ((fun a => a^3) ∘ toSpecies j T) i) :
    accCube S = accCube T := by
  sorry


end SMνACCs
