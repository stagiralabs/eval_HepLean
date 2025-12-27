import VerifiedAgora.tagger
/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Permutations
import PhysLean.QFT.AnomalyCancellation.GroupActions
/-!
# ACC system for SM with RHN (without hypercharge).

We define the ACC system for the Standard Model (without hypercharge) with right-handed neutrinos.
-/

namespace SMRHN
open SMνCharges
open SMνACCs
open BigOperators

/-- The ACC system for the SM plus RHN. -/
/-- The ACC system for the SM plus RHN. -/
@[simps!]
def SM (n : ℕ) : ACCSystem where
  numberLinear := by sorry


namespace SM

variable {n : ℕ}

@[target] lemma gravSol (S : (SM n).LinSols) : accGrav S.val = 0 := by
  sorry


lemma SU2Sol (S : (SM n).LinSols) : accSU2 S.val = 0 := by
  have hS := S.linearSol
  simp only [SM_numberLinear, SM_linearACCs, Fin.isValue] at hS
  exact hS 1

/-- The charges in `(SMNoGrav n).LinSols` satisfy the `SU(3)` anomaly-equation. -/
@[target] lemma SU3Sol (S : (SMNoGrav n).LinSols) : accSU3 S.val = 0 := by
  sorry


/-- The charges in `(SMNoGrav n).Sols` satisfy the cubic anomaly-equation. -/
@[target] lemma cubeSol (S : (SMNoGrav n).Sols) : accCube S.val = 0 := by
  sorry


/-- An element of `charges` which satisfies the linear ACCs
  gives us a element of `LinSols`. -/
def chargeToLinear (S : (SM n).Charges) (hGrav : accGrav S = 0)
    (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) : (SM n).LinSols :=
  ⟨S, by
    intro i
    simp only [SM_numberLinear] at i
    match i with
    | 0 => exact hGrav
    | 1 => exact hSU2
    | 2 => exact hSU3⟩

/-- An element of `LinSols` which satisfies the quadratic ACCs
  gives us a element of `QuadSols`. -/
def linearToQuad (S : (SM n).LinSols) : (SM n).QuadSols :=
  ⟨S, fun i ↦ Fin.elim0 i⟩

/-- An element of `QuadSols` which satisfies the quadratic ACCs
  gives us a element of `Sols`. -/
def quadToAF (S : (SM n).QuadSols) (hc : accCube S.val = 0) :
    (SM n).Sols := ⟨S, hc⟩

/-- An element of `charges` which satisfies the linear and quadratic ACCs
  gives us a element of `QuadSols`. -/
/-- An element of `charges` which satisfies the linear and quadratic ACCs
  gives us a element of `AnomalyFreeQuad`. -/
def chargeToQuad (S : (SMNoGrav n).Charges) (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) :
    (SMNoGrav n).QuadSols := by sorry


/-- An element of `charges` which satisfies the linear, quadratic and cubic ACCs
  gives us a element of `Sols`. -/
def chargeToAF (S : (SM n).Charges) (hGrav : accGrav S = 0) (hSU2 : accSU2 S = 0)
    (hSU3 : accSU3 S = 0) (hc : accCube S = 0) : (SM n).Sols :=
  quadToAF (chargeToQuad S hGrav hSU2 hSU3) hc

/-- An element of `LinSols` which satisfies the quadratic and cubic ACCs
  gives us a element of `Sols`. -/
/-- An element of `AnomalyFreeLinear` which satisfies the quadratic and cubic ACCs
  gives us a element of `AnomalyFree`. -/
def linearToAF (S : (SMNoGrav n).LinSols)
    (hc : accCube S.val = 0) : (SMNoGrav n).Sols := by sorry


/-- The permutations acting on the ACC system corresponding to the SM with RHN. -/
/-- The permutations acting on the ACC system corresponding to the SM with RHN. -/
def perm (n : ℕ) : ACCSystemGroupAction (SM n) where
  group := PermGroup n
  groupInst := inferInstance
  rep := repCharges
  linearInvariant := by
    sorry


end SM

end SMRHN
