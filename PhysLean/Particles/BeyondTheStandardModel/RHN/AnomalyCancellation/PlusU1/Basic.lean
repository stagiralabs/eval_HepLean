import VerifiedAgora.tagger
/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Permutations
import PhysLean.QFT.AnomalyCancellation.GroupActions
/-!
# ACC system for SM with RHN

We define the ACC system for the Standard Model with right-handed neutrinos.
-/

namespace SMRHN
open SMνCharges
open SMνACCs
open BigOperators

/-- The ACC system for the SM plus RHN with an additional U1. -/
/-- The ACC system for the SM plus RHN with an additional U1. -/
@[simps!]
def PlusU1 (n : ℕ) : ACCSystem where
  numberLinear := by sorry


namespace PlusU1

variable {n : ℕ}

@[target] lemma gravSol (S : (SM n).LinSols) : accGrav S.val = 0 := by
  sorry


/-- The charges in `(SMNoGrav n).LinSols` satisfy the `SU(2)` anomaly-equation. -/
@[target] lemma SU2Sol (S : (SMNoGrav n).LinSols) : accSU2 S.val = 0 := by
  sorry


lemma SU3Sol (S : (PlusU1 n).LinSols) : accSU3 S.val = 0 := by
  have hS := S.linearSol
  simp only [PlusU1_numberLinear, PlusU1_linearACCs, Fin.isValue] at hS
  exact hS 2

lemma YYsol (S : (PlusU1 n).LinSols) : accYY S.val = 0 := by
  have hS := S.linearSol
  simp only [PlusU1_numberLinear, PlusU1_linearACCs, Fin.isValue] at hS
  exact hS 3

@[target] lemma quadSol (S : (PlusU1 n).QuadSols) : accQuad S.val = 0 := by
  sorry


lemma cubeSol (S : (PlusU1 n).Sols) : accCube S.val = 0 := by
  exact S.cubicSol

/-- An element of `charges` which satisfies the linear ACCs
  gives us a element of `LinSols`. -/
/-- An element of `charges` which satisfies the linear ACCs
  gives us a element of `AnomalyFreeLinear`. -/
def chargeToLinear (S : (SMNoGrav n).Charges) (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) :
    (SMNoGrav n).LinSols :=
  ⟨S, by
    sorry


/-- An element of `LinSols` which satisfies the quadratic ACCs
  gives us a element of `AnomalyFreeQuad`. -/
/-- An element of `AnomalyFreeLinear` which satisfies the quadratic ACCs
  gives us a element of `AnomalyFreeQuad`. -/
def linearToQuad (S : (SMNoGrav n).LinSols) : (SMNoGrav n).QuadSols :=
  ⟨S, by
    sorry


/-- An element of `QuadSols` which satisfies the quadratic ACCs
  gives us a element of `Sols`. -/
/-- An element of `AnomalyFreeQuad` which satisfies the quadratic ACCs
  gives us a element of `AnomalyFree`. -/
def quadToAF (S : (SMNoGrav n).QuadSols) (hc : accCube S.val = 0) :
    (SMNoGrav n).Sols := by sorry


/-- An element of `charges` which satisfies the linear and quadratic ACCs
  gives us a element of `QuadSols`. -/
def chargeToQuad (S : (PlusU1 n).Charges) (hGrav : accGrav S = 0)
    (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) (hYY : accYY S = 0) (hQ : accQuad S = 0) :
    (PlusU1 n).QuadSols :=
  linearToQuad (chargeToLinear S hGrav hSU2 hSU3 hYY) hQ

/-- An element of `charges` which satisfies the linear, quadratic and cubic ACCs
  gives us a element of `Sols`. -/
def chargeToAF (S : (PlusU1 n).Charges) (hGrav : accGrav S = 0) (hSU2 : accSU2 S = 0)
    (hSU3 : accSU3 S = 0) (hYY : accYY S = 0) (hQ : accQuad S = 0) (hc : accCube S = 0) :
    (PlusU1 n).Sols :=
  quadToAF (chargeToQuad S hGrav hSU2 hSU3 hYY hQ) hc

/-- An element of `LinSols` which satisfies the quadratic and cubic ACCs
  gives us a element of `Sols`. -/
def linearToAF (S : (PlusU1 n).LinSols) (hQ : accQuad S.val = 0)
    (hc : accCube S.val = 0) : (PlusU1 n).Sols :=
  quadToAF (linearToQuad S hQ) hc

/-- The permutations acting on the ACC system corresponding to the SM with RHN. -/
/-- The permutations acting on the ACC system corresponding to the SM with RHN. -/
def perm (n : ℕ) : ACCSystemGroupAction (SM n) where
  group := PermGroup n
  groupInst := inferInstance
  rep := repCharges
  linearInvariant := by
    sorry


end PlusU1

end SMRHN
