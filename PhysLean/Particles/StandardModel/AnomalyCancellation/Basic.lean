import VerifiedAgora.tagger
/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.AnomalyCancellation.Basic
/-!
# Anomaly cancellation conditions for the n-family SM.

We define the ACC system for the Standard Model with`n`-families and no RHN.

-/

open Nat
open BigOperators

/-- Associate to each (including RHN) SM fermion a set of charges-/
/-- Associate to each (including RHN) SM fermion a set of charges-/
@[simps!]
def SMCharges (n : ℕ) : ACCSystemCharges := by sorry


/-- The vector space associated with a single species of fermions. -/
/-- The vector space associated with a single species of fermions. -/
@[simps!]
def SMSpecies (n : ℕ) : ACCSystemCharges := by sorry


namespace SMCharges

variable {n : ℕ}

/-- An equivalence between the set `(SMCharges n).charges` and the set
  `(Fin 5 → Fin n → ℚ)`. -/
/-- An equivalence between the set `(SMCharges n).charges` and the set
  `(Fin 5 → Fin n → ℚ)`. -/
@[simps!]
def toSpeciesEquiv : (SMCharges n).Charges ≃ (Fin 5 → Fin n → ℚ) := by sorry


/-- For a given `i ∈ Fin 5`, the projection of a charge onto that species. -/
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


/-- The `Q` charges as a map `Fin n → ℚ`. -/
/-- The `Q` charges as a map `Fin n → ℚ`. -/
abbrev Q := by sorry


/-- The `U` charges as a map `Fin n → ℚ`. -/
/-- The `U` charges as a map `Fin n → ℚ`. -/
abbrev U := by sorry


/-- The `D` charges as a map `Fin n → ℚ`. -/
abbrev D := @toSpecies n 2

/-- The `L` charges as a map `Fin n → ℚ`. -/
/-- The `L` charges as a map `Fin n → ℚ`. -/
abbrev L := by sorry


/-- The `E` charges as a map `Fin n → ℚ`. -/
/-- The `E` charges as a map `Fin n → ℚ`. -/
abbrev E := by sorry


end SMCharges

namespace SMACCs

open SMCharges

variable {n : ℕ}

/-- The gravitational anomaly equation. -/
open BigOperators in
/-- The gravitational anomaly. -/
def accGrav (n : ℕ) : ((PureU1Charges n).Charges →ₗ[ℚ] ℚ) where
  toFun S := ∑ i : Fin n, S i
  map_add' S T := Finset.sum_add_distrib
  map_smul' a S := by
    sorry


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


/-- The quadratic anomaly cancellation condition. -/
@[simp]
def accQuad : HomogeneousQuadratic (SMCharges n).Charges :=
  (@quadBiLin n).toHomogeneousQuad

/-- Extensionality lemma for `accQuad`. -/
/-- Extensionality lemma for `accQuad`. -/
@[target] lemma accQuad_ext {S T : (SMCharges n).Charges}
    (h : ∀ j, ∑ i, ((fun a => a^2) ∘ toSpecies j S) i =
    ∑ i, ((fun a => a^2) ∘ toSpecies j T) i) :
    accQuad S = accQuad T := by
  sorry


/-- The trilinear function defining the cubic. -/
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


/-- The cubic acc. -/
/-- The cubic anomaly equation. -/
@[simp]
def accCube (n : ℕ) : HomogeneousCubic ((PureU1Charges n).Charges) := by sorry


/-- Extensionality lemma for `accCube`. -/
/-- Extensionality lemma for `accCube`. -/
@[target] lemma accCube_ext {S T : (SMCharges n).Charges}
    (h : ∀ j, ∑ i, ((fun a => a^3) ∘ toSpecies j S) i =
    ∑ i, ((fun a => a^3) ∘ toSpecies j T) i) :
    accCube S = accCube T := by
  sorry


end SMACCs
