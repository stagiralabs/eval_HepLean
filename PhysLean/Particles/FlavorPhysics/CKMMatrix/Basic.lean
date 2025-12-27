import VerifiedAgora.tagger
/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Polyrith
/-!
# The CKM Matrix

The definition of the type of CKM matrices as unitary $3×3$-matrices.

An equivalence relation on CKM matrices is defined, where two matrices are equivalent if they are
related by phase shifts.

The notation `[V]ud` etc can be used for the elements of a CKM matrix, and
`[V]ud|us` etc for the ratios of elements.

-/

open Matrix Complex

noncomputable section

/-- Given three real numbers `a b c` the complex matrix with `exp (I * a)` etc on the
leading diagonal. -/
/-- Given three real numbers `a b c` the complex matrix with `exp (I * a)` etc on the
leading diagonal. -/
@[simp]
def phaseShiftMatrix (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℂ := by sorry


/-- The phase shift matrix for zero-phases is the identity. -/
/-- The phase shift matrix for zero-phases is the identity. -/
@[target] lemma phaseShiftMatrix_one : phaseShiftMatrix 0 0 0 = 1 := by
  sorry


/-- The conjugate transpose of the phase shift matrix is the phase-shift matrix
  with negated phases. -/
/-- The conjugate transpose of the phase shift matrix is the phase-shift matrix
  with negated phases. -/
@[target] lemma phaseShiftMatrix_star (a b c : ℝ) :
    (phaseShiftMatrix a b c)ᴴ = phaseShiftMatrix (- a) (- b) (- c) := by
  sorry


/-- The multiple of two phase shift matrices is equal to the phase shift matrix with
  added phases. -/
/-- The multiple of two phase shift matrices is equal to the phase shift matrix with
  added phases. -/
@[target] lemma phaseShiftMatrix_mul (a b c d e f : ℝ) :
    phaseShiftMatrix a b c * phaseShiftMatrix d e f = phaseShiftMatrix (a + d) (b + e) (c + f) := by
  sorry


/-- Given three real numbers `a b c` the unitary matrix with `exp (I * a)` etc on the
leading diagonal. -/
/-- Given three real numbers `a b c` the unitary matrix with `exp (I * a)` etc on the
leading diagonal. -/
@[simps!]
def phaseShift (a b c : ℝ) : unitaryGroup (Fin 3) ℂ :=
  ⟨phaseShiftMatrix a b c,
  by
    sorry


/-- The underlying matrix of the phase-shift element of the unitary group is the
  phase-shift matrix. -/
/-- The underlying matrix of the phase-shift element of the unitary group is the
  phase-shift matrix. -/
@[target] lemma phaseShift_coe_matrix (a b c : ℝ) : ↑(phaseShift a b c) = phaseShiftMatrix a b c := by sorry


/-- The relation on unitary matrices (CKM matrices) satisfied if two unitary matrices
  are related by phase shifts of quarks. -/
/-- The relation on unitary matrices (CKM matrices) satisfied if two unitary matrices
  are related by phase shifts of quarks. -/
def PhaseShiftRelation (U V : unitaryGroup (Fin 3) ℂ) : Prop := by sorry


/-- The relation `PhaseShiftRelation` is reflective. -/
/-- The relation `PhaseShiftRelation` is reflective. -/
@[target] lemma phaseShiftRelation_refl (U : unitaryGroup (Fin 3) ℂ) : PhaseShiftRelation U U := by
  sorry


/-- The relation `PhaseShiftRelation` is symmetric. -/
/-- The relation `PhaseShiftRelation` is symmetric. -/
@[target] lemma phaseShiftRelation_symm {U V : unitaryGroup (Fin 3) ℂ} :
    PhaseShiftRelation U V → PhaseShiftRelation V U := by
  sorry


/-- The relation `PhaseShiftRelation` is transitive. -/
/-- The relation `PhaseShiftRelation` is transitive. -/
@[target] lemma phaseShiftRelation_trans {U V W : unitaryGroup (Fin 3) ℂ} :
    PhaseShiftRelation U V → PhaseShiftRelation V W → PhaseShiftRelation U W := by
  sorry


/-- The relation `PhaseShiftRelation` is an equivalence relation. -/
/-- The relation `PhaseShiftRelation` is an equivalence relation. -/
@[target] lemma phaseShiftRelation_equiv : Equivalence PhaseShiftRelation where
  refl := by sorry


/-- The type of CKM matrices. -/
/-- The type of CKM matrices. -/
def CKMMatrix : Type := by sorry


/-- Two CKM matrices are equal if their underlying unitary matrices are equal. -/
/-- Two CKM matrices are equal if their underlying unitary matrices are equal. -/
@[target] lemma CKMMatrix_ext {U V : CKMMatrix} (h : U.val = V.val) : U = V := by
  sorry


/-- The `ud`th element of the CKM matrix. -/
scoped[CKMMatrix] notation (name := ud_element) "[" V "]ud" => V.1 0 0

/-- The `us`th element of the CKM matrix. -/
scoped[CKMMatrix] notation (name := us_element) "[" V "]us" => V.1 0 1

/-- The `ub`th element of the CKM matrix. -/
scoped[CKMMatrix] notation (name := ub_element) "[" V "]ub" => V.1 0 2

/-- The `cd`th element of the CKM matrix. -/
scoped[CKMMatrix] notation (name := cd_element) "[" V "]cd" => V.1 1 0

/-- The `cs`th element of the CKM matrix. -/
scoped[CKMMatrix] notation (name := cs_element) "[" V "]cs" => V.1 1 1

/-- The `cb`th element of the CKM matrix. -/
scoped[CKMMatrix] notation (name := cb_element) "[" V "]cb" => V.1 1 2

/-- The `td`th element of the CKM matrix. -/
scoped[CKMMatrix] notation (name := td_element) "[" V "]td" => V.1 2 0

/-- The `ts`th element of the CKM matrix. -/
scoped[CKMMatrix] notation (name := ts_element) "[" V "]ts" => V.1 2 1

/-- The `tb`th element of the CKM matrix. -/
scoped[CKMMatrix] notation (name := tb_element) "[" V "]tb" => V.1 2 2

/-- The setoid of CKM matrices defined by phase shifts of fermions. -/
instance CKMMatrixSetoid : Setoid CKMMatrix := ⟨PhaseShiftRelation, phaseShiftRelation_equiv⟩

/-- The matrix obtained from `V` by shifting the phases of the fermions. -/
/-- The matrix obtained from `V` by shifting the phases of the fermions. -/
@[simps!]
def phaseShiftApply (V : CKMMatrix) (a b c d e f : ℝ) : CKMMatrix := by sorry


namespace phaseShiftApply

/-- A CKM matrix is equivalent to a phase-shift of itself. -/
/-- An equivalence between `LinSols` and `Sols`. -/
def equiv : (PureU1 2).LinSols ≃ (PureU1 2).Sols where
  toFun S := ⟨⟨S, fun i => Fin.elim0 i⟩, by
    sorry


/-- The `ud` component of the CKM matrix obtained after applying a phase shift. -/
/-- The `ud` component of the CKM matrix obtained after applying a phase shift. -/
@[target] lemma ud (V : CKMMatrix) (a b c d e f : ℝ) :
    (phaseShiftApply V a b c d e f).1 0 0 = cexp (a * I + d * I) * V.1 0 0 := by
  sorry


/-- The `us` component of the CKM matrix obtained after applying a phase shift. -/
/-- The `us` component of the CKM matrix obtained after applying a phase shift. -/
@[target] lemma us (V : CKMMatrix) (a b c d e f : ℝ) :
    (phaseShiftApply V a b c d e f).1 0 1 = cexp (a * I + e * I) * V.1 0 1 := by
  sorry


/-- The `ub` component of the CKM matrix obtained after applying a phase shift. -/
/-- The `ub` component of the CKM matrix obtained after applying a phase shift. -/
@[target] lemma ub (V : CKMMatrix) (a b c d e f : ℝ) :
    (phaseShiftApply V a b c d e f).1 0 2 = cexp (a * I + f * I) * V.1 0 2 := by
  sorry


/-- The `cd` component of the CKM matrix obtained after applying a phase shift. -/
/-- The `cd` component of the CKM matrix obtained after applying a phase shift. -/
@[target] lemma cd (V : CKMMatrix) (a b c d e f : ℝ) :
    (phaseShiftApply V a b c d e f).1 1 0= cexp (b * I + d * I) * V.1 1 0 := by
  sorry


/-- The `cs` component of the CKM matrix obtained after applying a phase shift. -/
lemma cs (V : CKMMatrix) (a b c d e f : ℝ) :
    (phaseShiftApply V a b c d e f).1 1 1 = cexp (b * I + e * I) * V.1 1 1 := by
  simp only [Fin.isValue, phaseShiftApply_coe]
  rw [mul_apply, Fin.sum_univ_three]
  rw [mul_apply, mul_apply, mul_apply, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [Fin.isValue, cons_val', cons_val_zero, empty_val', cons_val_fin_one, vecCons_const,
    cons_val_one, head_fin_const, zero_mul, head_cons, zero_add, cons_val_two, tail_cons, add_zero,
    mul_zero]
  rw [exp_add]
  ring_nf

/-- The `cb` component of the CKM matrix obtained after applying a phase shift. -/
/-- The `cb` component of the CKM matrix obtained after applying a phase shift. -/
@[target] lemma cb (V : CKMMatrix) (a b c d e f : ℝ) :
    (phaseShiftApply V a b c d e f).1 1 2 = cexp (b * I + f * I) * V.1 1 2 := by
  sorry


/-- The `td` component of the CKM matrix obtained after applying a phase shift. -/
/-- The `td` component of the CKM matrix obtained after applying a phase shift. -/
@[target] lemma td (V : CKMMatrix) (a b c d e f : ℝ) :
    (phaseShiftApply V a b c d e f).1 2 0= cexp (c * I + d * I) * V.1 2 0 := by
  sorry


/-- The `ts` component of the CKM matrix obtained after applying a phase shift. -/
lemma ts (V : CKMMatrix) (a b c d e f : ℝ) :
    (phaseShiftApply V a b c d e f).1 2 1 = cexp (c * I + e * I) * V.1 2 1 := by
  simp only [Fin.isValue, phaseShiftApply_coe]
  rw [mul_apply, Fin.sum_univ_three]
  rw [mul_apply, mul_apply, mul_apply, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [Fin.isValue, cons_val', cons_val_zero, empty_val', cons_val_fin_one, vecCons_const,
    cons_val_two, tail_val', head_val', cons_val_one, head_cons, tail_cons, head_fin_const,
    zero_mul, add_zero, mul_zero, zero_add]
  change (0 * _ + _) * _ = _
  rw [exp_add]
  ring_nf

/-- The `tb` component of the CKM matrix obtained after applying a phase shift. -/
/-- The `tb` component of the CKM matrix obtained after applying a phase shift. -/
@[target] lemma tb (V : CKMMatrix) (a b c d e f : ℝ) :
    (phaseShiftApply V a b c d e f).1 2 2 = cexp (c * I + f * I) * V.1 2 2 := by
  sorry


end phaseShiftApply

/-- The absolute value of the `(i,j)`th element of `V`. -/
/-- The absolute value of the `(i,j)`th any representative of `⟦V⟧`. -/
def VAbs (i j : Fin 3) : Quotient CKMMatrixSetoid → ℝ := by sorry


/-- If two CKM matrices are equivalent (under phase shifts), then their absolute values
  are the same. -/
lemma VAbs'_equiv (i j : Fin 3) (V U : CKMMatrix) (h : V ≈ U) :
    VAbs' V i j = VAbs' U i j := by
  simp only [VAbs']
  obtain ⟨a, b, c, e, f, g, h⟩ := h
  rw [h]
  simp only [Submonoid.coe_mul, phaseShift_coe_matrix]
  rw [mul_apply, Fin.sum_univ_three]
  rw [mul_apply, Fin.sum_univ_three]
  rw [mul_apply, mul_apply, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [phaseShiftMatrix, Fin.isValue, cons_val', cons_val_zero, empty_val', cons_val_fin_one,
    vecCons_const, cons_val_one, cons_val_two, tail_cons, head_cons, head_fin_const]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, cons_val_zero, zero_mul, add_zero, mul_zero,
      mul_re, I_re, ofReal_re, I_im, ofReal_im, sub_self, Real.exp_zero,
      one_mul, mul_one,Fin.mk_one, cons_val_one, head_cons, zero_add,
      head_fin_const, Fin.reduceFinMk, cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, tail_cons,
      tail_val', head_val', Complex.norm_exp, Complex.norm_mul]
  all_goals change norm (0 * _ + _) = _
  all_goals simp [Complex.norm_exp]

/-- The absolute value of the `(i,j)`th any representative of `⟦V⟧`. -/
def VAbs (i j : Fin 3) : Quotient CKMMatrixSetoid → ℝ :=
  Quotient.lift (fun V => VAbs' V i j) (VAbs'_equiv i j)

/-- The absolute value of the `ud`th element of a representative of an equivalence class of
  CKM matrices. -/
/-- The absolute value of the `ud`th element of a representative of an equivalence class of
  CKM matrices. -/
@[simp]
abbrev VudAbs := by sorry


/-- The absolute value of the `us`th element of a representative of an equivalence class of
  CKM matrices. -/
/-- The absolute value of the `us`th element of a representative of an equivalence class of
  CKM matrices. -/
@[simp]
abbrev VusAbs := by sorry


/-- The absolute value of the `ub`th element of a representative of an equivalence class of
  CKM matrices. -/
/-- The absolute value of the `ub`th element of a representative of an equivalence class of
  CKM matrices. -/
@[simp]
abbrev VubAbs := by sorry


/-- The absolute value of the `cd`th element of a representative of an equivalence class of
  CKM matrices. -/
/-- The absolute value of the `cd`th element of a representative of an equivalence class of
  CKM matrices. -/
@[simp]
abbrev VcdAbs := by sorry


/-- The absolute value of the `cs`th element of a representative of an equivalence class of
  CKM matrices. -/
/-- The absolute value of the `cs`th element of a representative of an equivalence class of
  CKM matrices. -/
@[simp]
abbrev VcsAbs := by sorry


/-- The absolute value of the `cb`th element of a representative of an equivalence class of
  CKM matrices. -/
/-- The absolute value of the `cb`th element of a representative of an equivalence class of
  CKM matrices. -/
@[simp]
abbrev VcbAbs := by sorry


/-- The absolute value of the `td`th element of a representative of an equivalence class of
  CKM matrices. -/
/-- The absolute value of the `td`th element of a representative of an equivalence class of
  CKM matrices. -/
@[simp]
abbrev VtdAbs := by sorry


/-- The absolute value of the `ts`th element of a representative of an equivalence class of
  CKM matrices. -/
/-- The absolute value of the `ts`th element of a representative of an equivalence class of
  CKM matrices. -/
@[simp]
abbrev VtsAbs := by sorry


/-- The absolute value of the `tb`th element of a representative of an equivalence class of
  CKM matrices. -/
/-- The absolute value of the `tb`th element of a representative of an equivalence class of
  CKM matrices. -/
@[simp]
abbrev VtbAbs := by sorry


namespace CKMMatrix
open ComplexConjugate

section ratios

/-- The ratio of the `ub` and `ud` elements of a CKM matrix. -/
/-- The ratio of the `ub` and `ud` elements of a CKM matrix. -/
def Rubud (V : CKMMatrix) : ℂ := by sorry


/-- The ratio of the `ub` and `ud` elements of a CKM matrix. -/
scoped[CKMMatrix] notation (name := ub_ud_ratio) "[" V "]ub|ud" => Rubud V

/-- The ratio of the `us` and `ud` elements of a CKM matrix. -/
/-- The ratio of the `us` and `ud` elements of a CKM matrix. -/
def Rusud (V : CKMMatrix) : ℂ := by sorry


/-- The ratio of the `us` and `ud` elements of a CKM matrix. -/
scoped[CKMMatrix] notation (name := us_ud_ratio) "[" V "]us|ud" => Rusud V

/-- The ratio of the `ud` and `us` elements of a CKM matrix. -/
/-- The ratio of the `ud` and `us` elements of a CKM matrix. -/
def Rudus (V : CKMMatrix) : ℂ := by sorry


/-- The ratio of the `ud` and `us` elements of a CKM matrix. -/
scoped[CKMMatrix] notation (name := ud_us_ratio) "[" V "]ud|us" => Rudus V

/-- The ratio of the `ub` and `us` elements of a CKM matrix. -/
/-- The ratio of the `ub` and `us` elements of a CKM matrix. -/
def Rubus (V : CKMMatrix) : ℂ := by sorry


/-- The ratio of the `ub` and `us` elements of a CKM matrix. -/
scoped[CKMMatrix] notation (name := ub_us_ratio) "[" V "]ub|us" => Rubus V

/-- The ratio of the `cd` and `cb` elements of a CKM matrix. -/
/-- The ratio of the `cd` and `cb` elements of a CKM matrix. -/
def Rcdcb (V : CKMMatrix) : ℂ := by sorry


/-- The ratio of the `cd` and `cb` elements of a CKM matrix. -/
scoped[CKMMatrix] notation (name := cd_cb_ratio) "[" V "]cd|cb" => Rcdcb V

@[target] lemma Rcdcb_mul_cb {V : CKMMatrix} (h : [V]cb ≠ 0) : [V]cd = Rcdcb V * [V]cb := by
  sorry


/-- The ratio of the `cs` and `cb` elements of a CKM matrix. -/
/-- The ratio of the `cs` and `cb` elements of a CKM matrix. -/
def Rcscb (V : CKMMatrix) : ℂ := by sorry


/-- The ratio of the `cs` and `cb` elements of a CKM matrix. -/
scoped[CKMMatrix] notation (name := cs_cb_ratio) "[" V "]cs|cb" => Rcscb V

/-- Multiplying the ratio of the `cs` by `cb` element of a CKM matrix by the `cb` element
  returns the `cs` element, as long as the `cb` element is non-zero. -/
lemma Rcscb_mul_cb {V : CKMMatrix} (h : [V]cb ≠ 0) : [V]cs = Rcscb V * [V]cb := by
  rw [Rcscb]
  exact (div_mul_cancel₀ [V]cs h).symm

end ratios

end CKMMatrix

end
