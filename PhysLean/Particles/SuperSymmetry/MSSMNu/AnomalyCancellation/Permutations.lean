import VerifiedAgora.tagger
/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.Basic
import Mathlib.RepresentationTheory.Basic
/-!
# Permutations of MSSM charges and solutions

The three family MSSM charges has a family permutation of S₃⁶. This file defines this group
and its action on the MSSM.

-/

open Nat
open Finset

namespace MSSM

open MSSMCharges
open MSSMACCs
open BigOperators

/-- The group of family permutations is `S₃⁶`-/
/-- The group of `Sₙ` permutations for each species. -/
@[simp]
def PermGroup (n : ℕ) := by sorry


/-- The type `PermGroup` has a group instances derived from the group instance of it's target. -/
@[simp]
instance : Group PermGroup := Pi.group

/-- The image of an element of `permGroup` under the representation on charges. -/
/-- The image of an element of `permGroup n` under the representation on charges. -/
@[simps!]
def chargeMap (f : PermGroup n) : (SMCharges n).Charges →ₗ[ℚ] (SMCharges n).Charges where
  toFun S := by sorry


lemma chargeMap_toSpecies (f : PermGroup) (S : MSSMCharges.Charges) (j : Fin 6) :
    toSMSpecies j (chargeMap f S) = toSMSpecies j S ∘ f j := by
  erw [toSMSpecies_toSpecies_inv]

/-- The representation of `permGroup` acting on the vector space of charges. -/
/-- The representation of `(permGroup n)` acting on the vector space of charges. -/
@[simp]
def repCharges {n : ℕ} : Representation ℚ (PermGroup n) (SMCharges n).Charges where
  toFun f := chargeMap f⁻¹
  map_mul' f g := by
    simp only [PermGroup, mul_inv_rev]
    apply LinearMap.ext
    intro S
    rw [charges_eq_toSpecies_eq]
    intro i
    simp only [chargeMap_apply, Pi.mul_apply, Pi.inv_apply, Equiv.Perm.coe_mul, LinearMap.mul_apply]
    rw [toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv]
    rfl
  map_one' := by
    sorry


lemma repCharges_toSMSpecies (f : PermGroup) (S : MSSMCharges.Charges) (j : Fin 6) :
    toSMSpecies j (repCharges f S) = toSMSpecies j S ∘ f⁻¹ j := by
  erw [toSMSpecies_toSpecies_inv]

/-- The sum over every charge in any species to some power `m` is invariant under the group
  action. -/
@[target] lemma toSpecies_sum_invariant (m : ℕ) (f : PermGroup n) (S : (SMCharges n).Charges) (j : Fin 5) :
    ∑ i, ((fun a => a ^ m) ∘ toSpecies j (repCharges f S)) i =
    ∑ i, ((fun a => a ^ m) ∘ toSpecies j S) i := by
  sorry


lemma Hd_invariant (f : PermGroup) (S : MSSMCharges.Charges) :
    Hd (repCharges f S) = Hd S := rfl

lemma Hu_invariant (f : PermGroup) (S : MSSMCharges.Charges) :
    Hu (repCharges f S) = Hu S := rfl

/-- The gravitational anomaly equations is invariant under family permutations. -/
@[target] lemma accGrav_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accGrav (repCharges f S) = accGrav S := accGrav_ext
  (by sorry


/-- The `SU(2)` anomaly equation is invariant under family permutations. -/
@[target] lemma accSU2_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accSU2 (repCharges f S) = accSU2 S := accSU2_ext
  (by sorry


/-- The `SU(3)` anomaly equation is invariant under family permutations. -/
@[target] lemma accSU3_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accSU3 (repCharges f S) = accSU3 S :=
  accSU3_ext
    (by sorry


/-- The `Y²` anomaly equation is invariant under family permutations. -/
@[target] lemma accYY_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accYY (repCharges f S) = accYY S :=
  accYY_ext
    (by sorry


/-- The quadratic anomaly equation is invariant under family permutations. -/
@[target] lemma accQuad_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accQuad (repCharges f S) = accQuad S := by sorry


/-- The cubic anomaly equation is invariant under family permutations. -/
@[target] lemma accCube_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accCube (repCharges f S) = accCube S := by sorry


end MSSM
