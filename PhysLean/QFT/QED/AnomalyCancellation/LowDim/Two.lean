import VerifiedAgora.tagger
/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.QED.AnomalyCancellation.Basic
/-!
# The Pure U(1) case with 2 fermions

We define an equivalence between `LinSols` and `Sols`.
-/

open Nat
open Finset

namespace PureU1

variable {n : ℕ}

namespace Two

/-- An equivalence between `LinSols` and `Sols`. -/
/-- An equivalence between `LinSols` and `Sols`. -/
def equiv : (PureU1 2).LinSols ≃ (PureU1 2).Sols where
  toFun S := ⟨⟨S, fun i => Fin.elim0 i⟩, by
    sorry


end Two

end PureU1
