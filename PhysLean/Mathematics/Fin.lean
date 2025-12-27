import VerifiedAgora.tagger
/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Tactic.Polyrith
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Equiv.Fin.Basic
/-!
# Fin lemmas

The purpose of this file is to define some results Fin currently
in Mathlib.

At some point these should either be up-streamed to Mathlib or replaced with definitions already
in Mathlib.

-/
namespace PhysLean.Fin

open Fin
variable {n : Nat}

/-- Given a `i` and `x` in `Fin n.succ.succ` returns an element of `Fin n.succ`
  subtracting 1 if `i.val ≤ x.val` else casting x. -/
/-- Given a `i` and `x` in `Fin n.succ.succ` returns an element of `Fin n.succ`
  subtracting 1 if `i.val ≤ x.val` else casting x. -/
def predAboveI (i x : Fin n.succ.succ) : Fin n.succ :=
  if h : x.val < i.val then
    ⟨x.val, by sorry


@[target] lemma predAboveI_self (i : Fin n.succ.succ) : predAboveI i i = ⟨i.val - 1, by sorry


@[target] lemma predAboveI_succAbove (i : Fin n.succ.succ) (x : Fin n.succ) :
    predAboveI i (Fin.succAbove i x) = x := by
  sorry

@[target] lemma succsAbove_predAboveI {i x : Fin n.succ.succ} (h : i ≠ x) :
    Fin.succAbove i (predAboveI i x) = x := by
  sorry


@[target] lemma predAboveI_eq_iff {i x : Fin n.succ.succ} (h : i ≠ x) (y : Fin n.succ) :
    y = predAboveI i x ↔ i.succAbove y = x := by
  sorry


@[target] lemma predAboveI_lt {i x : Fin n.succ.succ} (h : x.val < i.val) :
    predAboveI i x = ⟨x.val, by sorry


@[target] lemma predAboveI_ge {i x : Fin n.succ.succ} (h : i.val < x.val) :
    predAboveI i x = ⟨x.val - 1, by sorry


@[target] lemma succAbove_succAbove_predAboveI (i : Fin n.succ.succ) (j : Fin n.succ) (x : Fin n) :
    i.succAbove (j.succAbove x) =
    (i.succAbove j).succAbove ((predAboveI (i.succAbove j) i).succAbove x) := by
  sorry


/-- The equivalence between `Fin n.succ` and `Fin 1 ⊕ Fin n` extracting the
  `i`th component. -/
/-- The equivalence between `Fin n.succ` and `Fin 1 ⊕ Fin n` extracting the
  `i`th component. -/
def finExtractOne {n : ℕ} (i : Fin n.succ) : Fin n.succ ≃ Fin 1 ⊕ Fin n :=
  (finCongr (by sorry


@[target] lemma finExtractOne_apply_eq {n : ℕ} (i : Fin n.succ) :
    finExtractOne i i = Sum.inl 0 := by
  sorry


@[target] lemma finExtractOne_symm_inr {n : ℕ} (i : Fin n.succ) :
    (finExtractOne i).symm ∘ Sum.inr = i.succAbove := by
  sorry


@[target] lemma finExtractOne_symm_inr_apply {n : ℕ} (i : Fin n.succ) (x : Fin n) :
    (finExtractOne i).symm (Sum.inr x) = i.succAbove x := calc
  _ = ((finExtractOne i).symm ∘ Sum.inr) x := rfl
  _ = i.succAbove x := by sorry


@[target] lemma finExtractOne_symm_inl_apply {n : ℕ} (i : Fin n.succ) :
    (finExtractOne i).symm (Sum.inl 0) = i := by
  sorry


@[target] lemma finExtractOne_apply_neq {n : ℕ} (i j : Fin n.succ.succ) (hij : i ≠ j) :
    finExtractOne i j = Sum.inr (predAboveI i j) := by
  sorry


/-- Given an equivalence `Fin n.succ.succ ≃ Fin n.succ.succ`, and an `i : Fin n.succ.succ`,
  the map `Fin n.succ → Fin n.succ` obtained by dropping `i` and it's image. -/
/-- Given an equivalence `Fin n.succ.succ ≃ Fin n.succ.succ`, and an `i : Fin n.succ.succ`,
  the map `Fin n.succ → Fin n.succ` obtained by dropping `i` and it's image. -/
def finExtractOnPermHom {m : ℕ} (i : Fin n.succ.succ) (σ : Fin n.succ.succ ≃ Fin m.succ.succ) :
    Fin n.succ → Fin m.succ := by sorry


@[target] lemma finExtractOnPermHom_inv {m : ℕ} (i : Fin n.succ.succ)
    (σ : Fin n.succ.succ ≃ Fin m.succ.succ) :
    (finExtractOnPermHom (σ i) σ.symm) ∘ (finExtractOnPermHom i σ) = id := by
  sorry


/-- Given an equivalence `Fin n.succ.succ ≃ Fin n.succ.succ`, and an `i : Fin n.succ.succ`,
  the equivalence `Fin n.succ ≃ Fin n.succ` obtained by dropping `i` and it's image. -/
/-- Given an equivalence `Fin n.succ.succ ≃ Fin n.succ.succ`, and an `i : Fin n.succ.succ`,
  the equivalence `Fin n.succ ≃ Fin n.succ` obtained by dropping `i` and it's image. -/
def finExtractOnePerm {m : ℕ} (i : Fin n.succ.succ) (σ : Fin n.succ.succ ≃ Fin m.succ.succ) :
    Fin n.succ ≃ Fin m.succ where
  toFun x := finExtractOnPermHom i σ x
  invFun x := finExtractOnPermHom (σ i) σ.symm x
  left_inv x := by
    sorry


@[target] lemma finExtractOnePerm_equiv {n m : ℕ} (e : Fin n.succ.succ ≃ Fin m.succ.succ)
    (i : Fin n.succ.succ) :
    e ∘ i.succAbove = (e i).succAbove ∘ finExtractOnePerm i e := by
  sorry


@[target] lemma finExtractOnePerm_apply (i : Fin n.succ.succ) (σ : Fin n.succ.succ ≃ Fin n.succ.succ)
    (x : Fin n.succ) : finExtractOnePerm i σ x = predAboveI (σ i)
    (σ ((finExtractOne i).symm (Sum.inr x))) := by sorry


@[target] lemma finExtractOnePerm_symm_apply (i : Fin n.succ.succ) (σ : Fin n.succ.succ ≃ Fin n.succ.succ)
    (x : Fin n.succ) : (finExtractOnePerm i σ).symm x = predAboveI (σ.symm (σ i))
    (σ.symm ((finExtractOne (σ i)).symm (Sum.inr x))) := by sorry


/-- The equivalence of types `Fin n.succ.succ ≃ (Fin 1 ⊕ Fin 1) ⊕ Fin n` extracting
  the `i` and `(i.succAbove j)`. -/
/-- The equivalence of types `Fin n.succ.succ ≃ (Fin 1 ⊕ Fin 1) ⊕ Fin n` extracting
  the `i` and `(i.succAbove j)`. -/
def finExtractTwo {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ) :
    Fin n.succ.succ ≃ (Fin 1 ⊕ Fin 1) ⊕ Fin n := by sorry


@[target] lemma finExtractTwo_apply_fst {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ) :
    finExtractTwo i j i = Sum.inl (Sum.inl 0) := by
  sorry


@[target] lemma finExtractTwo_symm_inr {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ) :
    (finExtractTwo i j).symm ∘ Sum.inr = i.succAbove ∘ j.succAbove := by
  sorry


@[target] lemma finExtractTwo_symm_inr_apply {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ) (x : Fin n) :
    (finExtractTwo i j).symm (Sum.inr x) = i.succAbove (j.succAbove x) := by
  sorry


@[target] lemma finExtractTwo_symm_inl_inr_apply {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ) :
    (finExtractTwo i j).symm (Sum.inl (Sum.inr 0)) = i.succAbove j := by
  sorry


@[target] lemma finExtractTwo_symm_inl_inl_apply {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ) :
    (finExtractTwo i j).symm (Sum.inl (Sum.inl 0)) = i := by sorry


@[target] lemma finExtractTwo_apply_snd {n : ℕ} (i : Fin n.succ.succ) (j : Fin n.succ) :
    finExtractTwo i j (i.succAbove j) = Sum.inl (Sum.inr 0) := by
  sorry


/-- Takes two maps `Fin n → Fin n` and returns the equivalence they form. -/
/-- Takes two maps `Fin n → Fin n` and returns the equivalence they form. -/
def finMapToEquiv (f1 : Fin n → Fin m) (f2 : Fin m → Fin n)
    (h : ∀ x, f1 (f2 x) = x := by sorry


@[target] lemma finMapToEquiv_apply {f1 : Fin n → Fin m} {f2 : Fin m → Fin n}
    {h : ∀ x, f1 (f2 x) = x} {h' : ∀ x, f2 (f1 x) = x} (x : Fin n) :
    finMapToEquiv f1 f2 h h' x = f1 x := by sorry


@[target] lemma finMapToEquiv_symm_apply {f1 : Fin n → Fin m} {f2 : Fin m → Fin n}
    {h : ∀ x, f1 (f2 x) = x} {h' : ∀ x, f2 (f1 x) = x} (x : Fin m) :
    (finMapToEquiv f1 f2 h h').symm x = f2 x := by sorry


@[target] lemma finMapToEquiv_symm_eq {f1 : Fin n → Fin m} {f2 : Fin m → Fin n}
    {h : ∀ x, f1 (f2 x) = x} {h' : ∀ x, f2 (f1 x) = x} :
    (finMapToEquiv f1 f2 h h').symm = finMapToEquiv f2 f1 h' h := by
  sorry


/-- Given an equivalence between `Fin n` and `Fin m`, the induced equivalence between
  `Fin n.succ` and `Fin m.succ` derived by `Fin.cons`. -/
/-- Given an equivalence between `Fin n` and `Fin m`, the induced equivalence between
  `Fin n.succ` and `Fin m.succ` derived by `Fin.cons`. -/
def equivCons {n m : ℕ} (e : Fin n ≃ Fin m) : Fin n.succ ≃ Fin m.succ where
  toFun := Fin.cons 0 (Fin.succ ∘ e.toFun)
  invFun := Fin.cons 0 (Fin.succ ∘ e.invFun)
  left_inv i := by
    sorry


@[target] lemma equivCons_zero {n m : ℕ} (e : Fin n ≃ Fin m) :
    equivCons e 0 = 0 := by
  sorry


@[simp]
lemma equivCons_trans {n m k : ℕ} (e : Fin n ≃ Fin m) (f : Fin m ≃ Fin k) :
    Fin.equivCons (e.trans f) = (Fin.equivCons e).trans (Fin.equivCons f) := by
  refine Equiv.ext_iff.mpr fun x ↦ ?_
  simp only [Nat.succ_eq_add_one, equivCons, Equiv.toFun_as_coe, Equiv.coe_trans,
    Equiv.invFun_as_coe, Equiv.coe_fn_mk, Equiv.trans_apply]
  match x with
  | ⟨0, h⟩ => rfl
  | ⟨i + 1, h⟩ => rfl

@[target] lemma equivCons_castOrderIso {n m : ℕ} (h : n = m) :
    (Fin.equivCons (Fin.castOrderIso h).toEquiv) = (Fin.castOrderIso (by sorry


@[target] lemma equivCons_symm_succ {n m : ℕ} (e : Fin n ≃ Fin m) (i : ℕ) (hi : i + 1 < m.succ) :
    (Fin.equivCons e).symm ⟨i + 1, hi⟩ = (e.symm ⟨i, Nat.succ_lt_succ_iff.mp hi⟩).succ := by
  sorry


@[target] lemma equivCons_succ {n m : ℕ} (e : Fin n ≃ Fin m) (i : ℕ) (hi : i + 1 < n.succ) :
    (Fin.equivCons e) ⟨i + 1, hi⟩ = (e ⟨i, Nat.succ_lt_succ_iff.mp hi⟩).succ := by
  sorry


end PhysLean.Fin
