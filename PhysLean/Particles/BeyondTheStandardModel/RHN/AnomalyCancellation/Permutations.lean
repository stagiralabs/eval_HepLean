import VerifiedAgora.tagger
/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Basic
import Mathlib.RepresentationTheory.Basic
/-!
# Permutations of SM charges with RHN.

We define the group of permutations for the SM charges with RHN.
-/

open Nat
open Finset

namespace SMRHN

open SMνCharges
open SMνACCs
open BigOperators

/-- The group of `Sₙ` permutations for each species. -/
@[simp]
def PermGroup (n : ℕ) := Fin 6 → Equiv.Perm (Fin n)

variable {n : ℕ}

/-- The instance of a group on `PermGroup n` through the target space `Equiv.Perm (Fin n)`. -/
@[simp]
instance : Group (PermGroup n) := Pi.group

/-- The image of an element of `permGroup n` under the representation on charges. -/
/-- The image of an element of `permGroup n` under the representation on charges. -/
@[simps!]
def chargeMap (f : PermGroup n) : (SMCharges n).Charges →ₗ[ℚ] (SMCharges n).Charges where
  toFun S := by sorry


/-- The representation of `(permGroup n)` acting on the vector space of charges. -/
@[simp]
def repCharges {n : ℕ} : Representation ℚ (PermGroup n) (SMνCharges n).Charges where
  toFun f := chargeMap f⁻¹
  map_mul' f g := by
    simp only [PermGroup, mul_inv_rev]
    apply LinearMap.ext
    intro S
    rw [charges_eq_toSpecies_eq]
    intro i
    simp only [chargeMap_apply, Pi.mul_apply, Pi.inv_apply, Equiv.Perm.coe_mul,
      Module.End.mul_apply]
    repeat erw [toSMSpecies_toSpecies_inv]
    rfl
  map_one' := by
    refine LinearMap.ext fun S => ?_
    rw [charges_eq_toSpecies_eq]
    intro i
    erw [toSMSpecies_toSpecies_inv]
    rfl

lemma repCharges_toSpecies (f : PermGroup n) (S : (SMνCharges n).Charges) (j : Fin 6) :
    toSpecies j (repCharges f S) = toSpecies j S ∘ f⁻¹ j := by
  erw [toSMSpecies_toSpecies_inv]

/-- The sum over every charge in any species to some power `m` is invariant under the group
  action. -/
@[target] lemma toSpecies_sum_invariant (m : ℕ) (f : PermGroup n) (S : (SMCharges n).Charges) (j : Fin 5) :
    ∑ i, ((fun a => a ^ m) ∘ toSpecies j (repCharges f S)) i =
    ∑ i, ((fun a => a ^ m) ∘ toSpecies j S) i := by
  sorry


lemma accGrav_invariant (f : PermGroup n) (S : (SMνCharges n).Charges) :
    accGrav (repCharges f S) = accGrav S :=
  accGrav_ext (by simpa using toSpecies_sum_invariant 1 f S)

/-- The `SU(2)` anomaly equation is invariant under family permutations. -/
@[target] lemma accSU2_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accSU2 (repCharges f S) = accSU2 S := accSU2_ext
  (by sorry


/-- The `SU(3)` anomaly equation is invariant under family permutations. -/
@[target] lemma accSU3_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accSU3 (repCharges f S) = accSU3 S :=
  accSU3_ext
    (by sorry


lemma accYY_invariant (f : PermGroup n) (S : (SMνCharges n).Charges) :
    accYY (repCharges f S) = accYY S :=
  accYY_ext (by simpa using toSpecies_sum_invariant 1 f S)

/-- The quadratic anomaly equation is invariant under family permutations. -/
@[target] lemma accQuad_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accQuad (repCharges f S) = accQuad S := by sorry


/-- The cubic anomaly equation is invariant under family permutations. -/
@[target] lemma accCube_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accCube (repCharges f S) = accCube S := by sorry


end SMRHN
