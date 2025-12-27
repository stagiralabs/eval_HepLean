import VerifiedAgora.tagger
/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Tactic.Polyrith
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
/-!
# Fin involutions

Some properties of involutions of `Fin n`.

These involutions are used in e.g. proving results about Wick contractions.

-/
namespace PhysLean.Fin

open Nat

/-- There is an equivalence between involutions of `Fin n.succ` and involutions of
  `Fin n` and an optional valid choice of an element in `Fin n` (which is where `0`
    in `Fin n.succ` will be sent). -/
/-- There is an equivalence between involutions of `Fin n.succ` and involutions of
  `Fin n` and an optional valid choice of an element in `Fin n` (which is where `0`
    in `Fin n.succ` will be sent). -/
def involutionCons (n : ℕ) : {f : Fin n.succ → Fin n.succ // Function.Involutive f } ≃
    (f : {f : Fin n → Fin n // Function.Involutive f}) × {i : Option (Fin n) //
      ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)} where
  toFun f := ⟨⟨
    fun i =>
    if h : f.1 i.succ = 0 then i
    else Fin.pred (f.1 i.succ) h, by
    sorry


@[target] lemma involutionCons_ext {n : ℕ} {f1 f2 : (f : {f : Fin n → Fin n // Function.Involutive f}) ×
    {i : Option (Fin n) // ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)}}
    (h1 : f1.1 = f2.1) (h2 : f1.2 = Equiv.subtypeEquivRight (by sorry


/-- Given an involution of `Fin n`, the optional choice of an element in `Fin n` which
  maps to itself is equivalent to the optional choice of an element in
  `Fin (Finset.univ.filter fun i => f.1 i = i).card`. -/
def involutionAddEquiv {n : ℕ} (f : {f : Fin n → Fin n // Function.Involutive f}) :
    {i : Option (Fin n) // ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)} ≃
    Option (Fin (Finset.univ.filter fun i => f.1 i = i).card) := by
  let e1 : {i : Option (Fin n) // ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)}
        ≃ Option {i : Fin n // f.1 i = i} :=
    { toFun := fun i => match i with
        | ⟨some i, h⟩ => some ⟨i, by simpa using h⟩
        | ⟨none, h⟩ => none
      invFun := fun i => match i with
        | some ⟨i, h⟩ => ⟨some i, by simpa using h⟩
        | none => ⟨none, by simp⟩
      left_inv := by
        intro a
        cases a
        aesop
      right_inv := by
        intro a
        cases a
        rfl
        simp_all only [Subtype.coe_eta] }
  let s : Finset (Fin n) := Finset.univ.filter fun i => f.1 i = i
  let e2' : { i : Fin n // f.1 i = i} ≃ {i // i ∈ s} := by
    apply Equiv.subtypeEquivProp
    simp [s]
  let e2 : {i // i ∈ s} ≃ Fin (Finset.card s) := by
    refine (Finset.orderIsoOfFin _ ?_).symm.toEquiv
    simp [s]
  refine e1.trans (Equiv.optionCongr (e2'.trans (e2)))

@[target] lemma involutionAddEquiv_none_image_zero {n : ℕ} :
    {f : {f : Fin n.succ → Fin n.succ // Function.Involutive f}}
    → involutionAddEquiv (involutionCons n f).1 (involutionCons n f).2 = none
    → f.1 ⟨0, Nat.zero_lt_succ n⟩ = ⟨0, Nat.zero_lt_succ n⟩ := by
  sorry


lemma involutionAddEquiv_cast {n : ℕ} {f1 f2 : {f : Fin n → Fin n // Function.Involutive f}}
    (hf : f1 = f2) :
    involutionAddEquiv f1 = (Equiv.subtypeEquivRight (by rw [hf]; simp)).trans
      ((involutionAddEquiv f2).trans (Equiv.optionCongr (finCongr (by rw [hf])))) := by
  subst hf
  rw [finCongr_refl, Equiv.optionCongr_refl]
  rfl

lemma involutionAddEquiv_cast' {m : ℕ} {f1 f2 : {f : Fin m → Fin m // Function.Involutive f}}
    {N : ℕ} (hf : f1 = f2) (n : Option (Fin N))
    (hn1 : N = (Finset.filter (fun i => f1.1 i = i) Finset.univ).card)
    (hn2 : N = (Finset.filter (fun i => f2.1 i = i) Finset.univ).card) :
    HEq ((involutionAddEquiv f1).symm (Option.map (finCongr hn1) n))
    ((involutionAddEquiv f2).symm (Option.map (finCongr hn2) n)) := by
  subst hf
  rfl

lemma involutionAddEquiv_none_succ {n : ℕ}
    {f : {f : Fin n.succ → Fin n.succ // Function.Involutive f}}
    (h : involutionAddEquiv (involutionCons n f).1 (involutionCons n f).2 = none)
    (x : Fin n) : f.1 x.succ = x.succ ↔ (involutionCons n f).1.1 x = x := by
  simp only [succ_eq_add_one, involutionCons, Fin.cons_update, Equiv.coe_fn_mk, dite_eq_left_iff]
  have hx : ¬ f.1 x.succ = ⟨0, Nat.zero_lt_succ n⟩:=
    involutionAddEquiv_none_image_zero h ▸
      fun hn => Fin.succ_ne_zero x (Function.Involutive.injective f.2 hn)
  exact Iff.intro (fun h2 ↦ by simp [h2]) (fun h2 ↦ (Fin.pred_eq_iff_eq_succ hx).mp (h2 hx))

/-!

## Equivalences of involutions with no fixed points.

The main aim of these equivalences is to define `involutionNoFixedZeroEquivProd`.

-/

/-- Fixed point free involutions of `Fin n.succ` can be separated based on where they sent
  `0`. -/
/-- Fixed point free involutions of `Fin n.succ` can be separated based on where they sent
  `0`. -/
def involutionNoFixedEquivSum {n : ℕ} :
    {f : Fin n.succ → Fin n.succ // Function.Involutive f
    ∧ ∀ i, f i ≠ i} ≃ Σ (k : Fin n), {f : Fin n.succ → Fin n.succ // Function.Involutive f
    ∧ (∀ i, f i ≠ i) ∧ f 0 = k.succ} where
  toFun f := ⟨(f.1 0).pred (f.2.2 0), ⟨f.1, f.2.1, by sorry


/-- The condition on fixed point free involutions of `Fin n.succ` for a fixed value of `f 0`,
  can be modified by conjugation with an equivalence. -/
/-- The condition on fixed point free involutions of `Fin n.succ` for a fixed value of `f 0`,
  can be modified by conjugation with an equivalence. -/
def involutionNoFixedZeroSetEquivEquiv {n : ℕ}
    (k : Fin n) (e : Fin n.succ ≃ Fin n.succ) :
    {f : Fin n.succ → Fin n.succ // Function.Involutive f ∧ (∀ i, f i ≠ i) ∧ f 0 = k.succ} ≃
    {f : Fin n.succ → Fin n.succ // Function.Involutive (e.symm ∘ f ∘ e) ∧
      (∀ i, (e.symm ∘ f ∘ e) i ≠ i) ∧ (e.symm ∘ f ∘ e) 0 = k.succ} where
  toFun f := ⟨e ∘ f.1 ∘ e.symm, by
    sorry


/-- The condition on fixed point free involutions of `Fin n.succ` for a fixed value of `f 0`
  given an equivalence `e`,
  can be modified so that only the condition on `f 0` is up-to the equivalence `e`. -/
/-- The condition on fixed point free involutions of `Fin n.succ` for a fixed value of `f 0`
  given an equivalence `e`,
  can be modified so that only the condition on `f 0` is up-to the equivalence `e`. -/
def involutionNoFixedZeroSetEquivSetEquiv {n : ℕ} (k : Fin n)
    (e : Fin n.succ ≃ Fin n.succ) :
    {f : Fin n.succ → Fin n.succ // Function.Involutive (e.symm ∘ f ∘ e) ∧
    (∀ i, (e.symm ∘ f ∘ e) i ≠ i) ∧ (e.symm ∘ f ∘ e) 0 = k.succ} ≃
    {f : Fin n.succ → Fin n.succ // Function.Involutive f ∧
      (∀ i, f i ≠ i) ∧ (e.symm ∘ f ∘ e) 0 = k.succ} := by
  sorry


/-- Fixed point free involutions of `Fin n.succ` fixing `(e.symm ∘ f ∘ e) = k.succ` for a given `e`
  are equivalent to fixing `f (e 0) = e k.succ`. -/
def involutionNoFixedZeroSetEquivEquiv' {n : ℕ} (k : Fin n) (e : Fin n.succ ≃ Fin n.succ) :
    {f : Fin n.succ → Fin n.succ // Function.Involutive f ∧
    (∀ i, f i ≠ i) ∧ (e.symm ∘ f ∘ e) 0 = k.succ} ≃
    {f : Fin n.succ → Fin n.succ // Function.Involutive f ∧
    (∀ i, f i ≠ i) ∧ f (e 0) = e k.succ} := by
  refine Equiv.subtypeEquivRight ?_
  simp only [succ_eq_add_one, ne_eq, Function.comp_apply, and_congr_right_iff]
  intro f hi h1
  exact Equiv.symm_apply_eq e

/-- Fixed point involutions of `Fin n.succ.succ` with `f 0 = k.succ` are equivalent
  to fixed point involutions with `f 0 = 1`. -/
/-- Fixed point involutions of `Fin n.succ.succ` with `f 0 = k.succ` are equivalent
  to fixed point involutions with `f 0 = 1`. -/
def involutionNoFixedZeroSetEquivSetOne {n : ℕ} (k : Fin n.succ) :
    {f : Fin n.succ.succ → Fin n.succ.succ // Function.Involutive f ∧
      (∀ i, f i ≠ i) ∧ f 0 = k.succ}
      ≃ {f : Fin n.succ.succ → Fin n.succ.succ // Function.Involutive f ∧
      (∀ i, f i ≠ i) ∧ f 0 = 1} := by
  sorry


/-- Fixed point involutions of `Fin n.succ.succ` fixing `f 0 = 1` are equivalent to
  fixed point involutions of `Fin n`. -/
/-- Fixed point involutions of `Fin n.succ.succ` fixing `f 0 = 1` are equivalent to
  fixed point involutions of `Fin n`. -/
def involutionNoFixedSetOne {n : ℕ} :
    {f : Fin n.succ.succ → Fin n.succ.succ // Function.Involutive f ∧
    (∀ i, f i ≠ i) ∧ f 0 = 1} ≃ {f : Fin n → Fin n // Function.Involutive f ∧
    (∀ i, f i ≠ i)} where
  toFun f := by
    sorry


/-- Fixed point involutions of `Fin n.succ.succ` for fixed `f 0 = k.succ` are
  equivalent to fixed point involutions of `Fin n`. -/
/-- Fixed point involutions of `Fin n.succ.succ` for fixed `f 0 = k.succ` are
  equivalent to fixed point involutions of `Fin n`. -/
def involutionNoFixedZeroSetEquiv {n : ℕ} (k : Fin n.succ) :
    {f : Fin n.succ.succ → Fin n.succ.succ // Function.Involutive f ∧
      (∀ i, f i ≠ i) ∧ f 0 = k.succ}
      ≃ {f : Fin n → Fin n // Function.Involutive f ∧ (∀ i, f i ≠ i)} := by
  sorry


/-- The type of fixed point free involutions of `Fin n.succ.succ` is equivalent to the sum
  of `Fin n.succ` copies of fixed point involutions of `Fin n`. -/
/-- The type of fixed point free involutions of `Fin n.succ.succ` is equivalent to the sum
  of `Fin n.succ` copies of fixed point involutions of `Fin n`. -/
def involutionNoFixedEquivSumSame {n : ℕ} :
    {f : Fin n.succ.succ → Fin n.succ.succ // Function.Involutive f ∧ (∀ i, f i ≠ i)}
    ≃ Σ (_ : Fin n.succ),
      {f : Fin n → Fin n // Function.Involutive f ∧ (∀ i, f i ≠ i)} := by
  sorry


/-- Ever fixed-point free involutions of `Fin n.succ.succ` can be decomposed into a
  element of `Fin n.succ` (where `0` is sent) and a fixed-point free involution of
  `Fin n`. -/
/-- Ever fixed-point free involutions of `Fin n.succ.succ` can be decomposed into a
  element of `Fin n.succ` (where `0` is sent) and a fixed-point free involution of
  `Fin n`. -/
def involutionNoFixedZeroEquivProd {n : ℕ} :
    {f : Fin n.succ.succ → Fin n.succ.succ // Function.Involutive f ∧ (∀ i, f i ≠ i)}
    ≃ Fin n.succ ×
    {f : Fin n → Fin n // Function.Involutive f ∧ (∀ i, f i ≠ i)} := by
  sorry


/-- The type of fixed-point free involutions of `Fin n` is finite. -/
instance {n : ℕ} : Fintype { f // Function.Involutive f ∧ ∀ (i : Fin n), f i ≠ i } := by
  have : DecidablePred fun x ↦ Function.Involutive x :=
    fun f ↦ Fintype.decidableForallFintype (α := Fin n)
  exact Subtype.fintype ..

lemma involutionNoFixed_card_succ {n : ℕ} :
    Fintype.card
    {f : Fin n.succ.succ → Fin n.succ.succ // Function.Involutive f ∧ (∀ i, f i ≠ i)}
    = n.succ *
    Fintype.card {f : Fin n → Fin n // Function.Involutive f ∧ (∀ i, f i ≠ i)} := by
  simp [Fintype.card_congr involutionNoFixedZeroEquivProd]

@[target] lemma involutionNoFixed_card_mul_two : (n : ℕ) →
    Fintype.card {f : Fin (2 * n) → Fin (2 * n) // Function.Involutive f ∧ (∀ i, f i ≠ i)}
    = (2 * n - 1)‼
  | 0 => rfl
  | Nat.succ n => by
    sorry


@[target] lemma involutionNoFixed_card_mul_two_plus_one : (n : ℕ) →
    Fintype.card {f : Fin (2 * n + 1) → Fin (2 * n + 1) // Function.Involutive f ∧ (∀ i, f i ≠ i)}
    = 0
  | 0 => rfl
  | Nat.succ n => by
    sorry


@[target] lemma involutionNoFixed_card_even : (n : ℕ) → (he : Even n) →
    Fintype.card {f : Fin n → Fin n // Function.Involutive f ∧ (∀ i, f i ≠ i)} = (n - 1)‼ := by
  sorry


@[target] lemma involutionNoFixed_card_odd : (n : ℕ) → (ho : Odd n) →
    Fintype.card {f : Fin n → Fin n // Function.Involutive f ∧ (∀ i, f i ≠ i)} = 0 := by
  sorry


end PhysLean.Fin
