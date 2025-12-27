import VerifiedAgora.tagger
/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Permutations
import PhysLean.QFT.AnomalyCancellation.GroupActions
/-!
# ACC system for SM with RHN and no gravitational anomaly.

We define the ACC system for the Standard Model with right-handed neutrinos and no gravitational
anomaly.
-/

namespace SMRHN
open SMνCharges
open SMνACCs
open BigOperators

/-- The ACC system for the SM plus RHN with no gravitational anomaly. -/
@[simps!]
def SMNoGrav (n : ℕ) : ACCSystem where
  toACCSystemCharges := SMνCharges n
  numberLinear := 2
  linearACCs := fun i =>
    match i with
    | 0 => @accSU2 n
    | 1 => accSU3
  numberQuadratic := 0
  quadraticACCs := fun i ↦ Fin.elim0 i
  cubicACC := accCube

namespace SMNoGrav

variable {n : ℕ}

/-- The charges in `(SMNoGrav n).LinSols` satisfy the `SU(2)` anomaly-equation. -/
@[target] lemma SU2Sol (S : (SMNoGrav n).LinSols) : accSU2 S.val = 0 := by
  sorry


/-- The charges in `(SMNoGrav n).LinSols` satisfy the `SU(3)` anomaly-equation. -/
@[target] lemma SU3Sol (S : (SMNoGrav n).LinSols) : accSU3 S.val = 0 := by
  sorry


lemma cubeSol (S : (SMNoGrav n).Sols) : accCube S.val = 0 := S.cubicSol

/-- An element of `charges` which satisfies the linear ACCs
  gives us a element of `LinSols`. -/
/-- An element of `charges` which satisfies the linear ACCs
  gives us a element of `AnomalyFreeLinear`. -/
def chargeToLinear (S : (SMNoGrav n).Charges) (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) :
    (SMNoGrav n).LinSols :=
  ⟨S, by
    sorry


/-- An element of `LinSols` which satisfies the quadratic ACCs
  gives us a element of `QuadSols`. -/
/-- An element of `AnomalyFreeLinear` which satisfies the quadratic ACCs
  gives us a element of `AnomalyFreeQuad`. -/
def linearToQuad (S : (SMNoGrav n).LinSols) : (SMNoGrav n).QuadSols :=
  ⟨S, by
    sorry


/-- An element of `QuadSols` which satisfies the quadratic ACCs
  gives us a element of `LinSols`. -/
/-- An element of `AnomalyFreeQuad` which satisfies the quadratic ACCs
  gives us a element of `AnomalyFree`. -/
def quadToAF (S : (SMNoGrav n).QuadSols) (hc : accCube S.val = 0) :
    (SMNoGrav n).Sols := by sorry


/-- An element of `charges` which satisfies the linear and quadratic ACCs
  gives us a element of `QuadSols`. -/
/-- An element of `charges` which satisfies the linear and quadratic ACCs
  gives us a element of `AnomalyFreeQuad`. -/
def chargeToQuad (S : (SMNoGrav n).Charges) (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) :
    (SMNoGrav n).QuadSols := by sorry


/-- An element of `charges` which satisfies the linear, quadratic and cubic ACCs
  gives us a element of `Sols`. -/
/-- An element of `charges` which satisfies the linear, quadratic and cubic ACCs
  gives us a element of `AnomalyFree`. -/
def chargeToAF (S : (SMNoGrav n).Charges) (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0)
    (hc : accCube S = 0) : (SMNoGrav n).Sols := by sorry


/-- An element of `LinSols` which satisfies the quadratic and cubic ACCs
  gives us a element of `Sols`. -/
/-- An element of `AnomalyFreeLinear` which satisfies the quadratic and cubic ACCs
  gives us a element of `AnomalyFree`. -/
def linearToAF (S : (SMNoGrav n).LinSols)
    (hc : accCube S.val = 0) : (SMNoGrav n).Sols := by sorry


/-- The permutations acting on the ACC system corresponding to the SM with RHN,
and no gravitational anomaly. -/
/-- The permutations acting on the ACC system corresponding to the SM with RHN. -/
def perm (n : ℕ) : ACCSystemGroupAction (SM n) where
  group := PermGroup n
  groupInst := inferInstance
  rep := repCharges
  linearInvariant := by
    sorry


end SMNoGrav

end SMRHN
