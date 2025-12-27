import VerifiedAgora.tagger
/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.QED.AnomalyCancellation.Basic
/-!
# The Pure U(1) case with 3 fermion

We show that S is a solution only if one of its charges is zero.
We define a surjective map from `LinSols` with a charge equal to zero to `Sols`.
-/

open Nat
open Finset

namespace PureU1

variable {n : ℕ}
namespace Three

@[target] lemma cube_for_linSol (S : (PureU1 3).LinSols) :
    (S.val (0 : Fin 3) = 0 ∨ S.val (1 : Fin 3) = 0 ∨ S.val (2 : Fin 3) = 0) ↔
    (PureU1 3).cubicACC S.val = 0 := by
  sorry


lemma cube_for_linSol (S : (PureU1 3).LinSols) :
    (S.val (0 : Fin 3) = 0 ∨ S.val (1 : Fin 3) = 0 ∨ S.val (2 : Fin 3) = 0) ↔
    (PureU1 3).cubicACC S.val = 0 := by
  rw [← cube_for_linSol']
  simp only [Fin.isValue, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
  exact Iff.symm or_assoc

lemma three_sol_zero (S : (PureU1 3).Sols) : S.val (0 : Fin 3) = 0 ∨ S.val (1 : Fin 3) = 0
    ∨ S.val (2 : Fin 3) = 0 := (cube_for_linSol S.1.1).mpr S.cubicSol

/-- Given a `LinSol` with a charge equal to zero a `Sol`. -/
/-- Given a `LinSol` with a charge equal to zero a `Sol`. -/
def solOfLinear (S : (PureU1 3).LinSols)
    (hS : S.val (0 : Fin 3) = 0 ∨ S.val (1 : Fin 3) = 0 ∨ S.val (2 : Fin 3) = 0) :
    (PureU1 3).Sols := by sorry


@[target] theorem solOfLinear_surjects (S : (PureU1 3).Sols) :
    ∃ (T : (PureU1 3).LinSols) (hT : T.val (0 : Fin 3) = 0 ∨ T.val (1 : Fin 3) = 0
    ∨ T.val (2 : Fin 3) = 0), solOfLinear T hT = S := by
  sorry


end Three

end PureU1
