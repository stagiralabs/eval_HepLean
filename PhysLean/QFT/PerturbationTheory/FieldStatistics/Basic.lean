import VerifiedAgora.tagger
/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.List.InsertIdx
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.FreeMonoid.Basic
/-!

# Field statistics

Basic properties related to whether a field, or list of fields, is bosonic or fermionic.

-/

/-- The type `FieldStatistic` is the type containing two elements `bosonic` and `fermionic`.
  This type is used to specify if a field or operator obeys bosonic or fermionic statistics. -/
inductive FieldStatistic : Type where
  | bosonic : FieldStatistic
  | fermionic : FieldStatistic
deriving DecidableEq

namespace FieldStatistic

variable {𝓕 : Type}

/-- The type `FieldStatistic` carries an instance of a commutative group in which
- `bosonic * bosonic = bosonic`
- `bosonic * fermionic = fermionic`
- `fermionic * bosonic = fermionic`
- `fermionic * fermionic = bosonic`

This group is isomorphic to `ℤ₂`. -/
@[simp]
instance : CommGroup FieldStatistic where
  one := bosonic
  mul a b :=
    match a, b with
    | bosonic, bosonic => bosonic
    | bosonic, fermionic => fermionic
    | fermionic, bosonic => fermionic
    | fermionic, fermionic => bosonic
  inv a := a
  mul_assoc a b c := by
    cases a <;> cases b <;> cases c <;>
    dsimp [HMul.hMul]
  one_mul a := by
    cases a <;> dsimp [HMul.hMul]
  mul_one a := by
    cases a <;> dsimp [HMul.hMul]
  inv_mul_cancel a := by
    cases a <;> dsimp only [HMul.hMul, Nat.succ_eq_add_one] <;> rfl
  mul_comm a b := by
    cases a <;> cases b <;> rfl

@[target] lemma bosonic_mul_bosonic : bosonic * bosonic = bosonic := by sorry


@[target] lemma bosonic_mul_fermionic : bosonic * fermionic = fermionic := by sorry


@[target] lemma fermionic_mul_bosonic : fermionic * bosonic = fermionic := by sorry


@[target] lemma fermionic_mul_fermionic : fermionic * fermionic = bosonic := by sorry


@[target] lemma mul_bosonic (a : FieldStatistic) : a * bosonic = a := by
  sorry


@[target] lemma mul_self (a : FieldStatistic) : a * a = 1 := by
  sorry


/-- Field statics form a finite type. -/
instance : Fintype FieldStatistic where
  elems := {bosonic, fermionic}
  complete := by
    intro c
    cases c
    · exact Finset.mem_insert_self bosonic {fermionic}
    · refine Finset.insert_eq_self.mp ?_
      exact rfl

@[target] lemma fermionic_not_eq_bonsic : ¬ fermionic = bosonic := by
  sorry


@[target] lemma bonsic_eq_fermionic_false : bosonic = fermionic ↔ false := by
  sorry


@[target] lemma neq_fermionic_iff_eq_bosonic (a : FieldStatistic) : ¬ a = fermionic ↔ a = bosonic := by
  sorry


@[target] lemma neq_bosonic_iff_eq_fermionic (a : FieldStatistic) : ¬ a = bosonic ↔ a = fermionic := by
  sorry


@[target] lemma bosonic_neq_iff_fermionic_eq (a : FieldStatistic) : ¬ bosonic = a ↔ fermionic = a := by
  sorry


@[target] lemma fermionic_neq_iff_bosonic_eq (a : FieldStatistic) : ¬ fermionic = a ↔ bosonic = a := by
  sorry


@[target] lemma eq_self_if_eq_bosonic {a : FieldStatistic} :
    (if a = bosonic then bosonic else fermionic) = a := by
  sorry


@[target] lemma eq_self_if_bosonic_eq {a : FieldStatistic} :
    (if bosonic = a then bosonic else fermionic) = a := by
  sorry


@[target] lemma mul_eq_one_iff (a b : FieldStatistic) : a * b = 1 ↔ a = b := by
  sorry


@[target] lemma one_eq_mul_iff (a b : FieldStatistic) : 1 = a * b ↔ a = b := by
  sorry


@[target] lemma mul_eq_iff_eq_mul (a b c : FieldStatistic) : a * b = c ↔ a = b * c := by
  sorry


lemma mul_eq_iff_eq_mul' (a b c : FieldStatistic) : a * b = c ↔ b = a * c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp only [bosonic_mul_fermionic, fermionic_not_eq_bonsic, mul_self,
      reduceCtorEq, fermionic_mul_bosonic, true_iff, iff_true]
  all_goals rfl

/-- The field statistics of a list of fields is fermionic if there is an odd number of fermions,
  otherwise it is bosonic. -/
def ofList (s : 𝓕 → FieldStatistic) : (φs : List 𝓕) → FieldStatistic
  | [] => bosonic
  | φ :: φs => if s φ = ofList s φs then bosonic else fermionic

@[target] lemma ofList_cons_eq_mul (s : 𝓕 → FieldStatistic) (φ : 𝓕) (φs : List 𝓕) :
    ofList s (φ :: φs) = s φ * ofList s φs := by
  sorry


lemma ofList_eq_prod (s : 𝓕 → FieldStatistic) : (φs : List 𝓕) →
    ofList s φs = (List.map s φs).prod
  | [] => rfl
  | φ :: φs => by
    rw [ofList_cons_eq_mul, List.map_cons, List.prod_cons, ofList_eq_prod]

@[target] lemma ofList_singleton (s : 𝓕 → FieldStatistic) (φ : 𝓕) : ofList s [φ] = s φ := by
  sorry


@[target] lemma ofList_freeMonoid (s : 𝓕 → FieldStatistic) (φ : 𝓕) : ofList s (FreeMonoid.of φ) = s φ := by sorry


@[target] lemma ofList_empty (s : 𝓕 → FieldStatistic) : ofList s [] = bosonic := by sorry


@[target] lemma ofList_append (s : 𝓕 → FieldStatistic) (φs φs' : List 𝓕) :
    ofList s (φs ++ φs') = if ofList s φs = ofList s φs' then bosonic else fermionic := by
  sorry


@[target] lemma ofList_append_eq_mul (s : 𝓕 → FieldStatistic) (φs φs' : List 𝓕) :
    ofList s (φs ++ φs') = ofList s φs * ofList s φs' := by
  sorry


@[target] lemma ofList_perm (s : 𝓕 → FieldStatistic) {l l' : List 𝓕} (h : l.Perm l') :
    ofList s l = ofList s l' := by
  sorry


@[target] lemma ofList_orderedInsert (s : 𝓕 → FieldStatistic) (le1 : 𝓕 → 𝓕 → Prop) [DecidableRel le1]
    (φs : List 𝓕) (φ : 𝓕) : ofList s (List.orderedInsert le1 φ φs) = ofList s (φ :: φs) := by sorry


@[target] lemma ofList_insertionSort (s : 𝓕 → FieldStatistic) (le1 : 𝓕 → 𝓕 → Prop) [DecidableRel le1]
    (φs : List 𝓕) : ofList s (List.insertionSort le1 φs) = ofList s φs := by sorry


@[target] lemma ofList_map_eq_finset_prod (s : 𝓕 → FieldStatistic) :
    (φs : List 𝓕) → (l : List (Fin φs.length)) → (hl : l.Nodup) →
    ofList s (l.map φs.get) = ∏ (i : Fin φs.length), if i ∈ l then s φs[i] else 1
  | [], [], _ => rfl
  | [], i :: l, hl => Fin.elim0 i
  | φ :: φs, [], hl => by
    sorry


@[target] lemma ofList_pair (s : 𝓕 → FieldStatistic) (φ1 φ2 : 𝓕) :
    ofList s [φ1, φ2] = s φ1 * s φ2 := by
  sorry


section ofListTake
open PhysLean.List
variable (q : 𝓕 → FieldStatistic)
@[target] lemma ofList_take_insert (n : ℕ) (φ : 𝓕) (φs : List 𝓕) :
    ofList q (List.take n φs) = ofList q (List.take n (List.insertIdx n φ φs)) := by
  sorry


@[target] lemma ofList_take_eraseIdx (n : ℕ) (φs : List 𝓕) :
    ofList q (List.take n (φs.eraseIdx n)) = ofList q (List.take n φs) := by
  sorry


@[target] lemma ofList_take_zero (φs : List 𝓕) :
    ofList q (List.take 0 φs) = 1 := by
  sorry


@[target] lemma ofList_take_succ_cons (n : ℕ) (φ1 : 𝓕) (φs : List 𝓕) :
    ofList q ((φ1 :: φs).take (n + 1)) = q φ1 * ofList q (φs.take n) := by
  sorry


@[target] lemma ofList_take_insertIdx_gt (n m : ℕ) (φ1 : 𝓕) (φs : List 𝓕) (hn : n < m) :
    ofList q ((List.insertIdx m φ1 φs).take n) = ofList q (φs.take n) := by
  sorry


@[target] lemma ofList_insert_lt_eq (n m : ℕ) (φ1 : 𝓕) (φs : List 𝓕) (hn : m ≤ n)
    (hm : m ≤ φs.length) :
    ofList q ((List.insertIdx m φ1 φs).take (n + 1)) =
    ofList q ((φ1 :: φs).take (n + 1)) := by
  sorry


lemma ofList_take_insertIdx_le (n m : ℕ) (φ1 : 𝓕) (φs : List 𝓕) (hn : m ≤ n) (hm : m ≤ φs.length) :
    ofList q ((List.insertIdx φs m φ1).take (n + 1)) = q φ1 * ofList q (φs.take n) := by
  rw [ofList_insert_lt_eq, ofList_take_succ_cons]
  · exact hn
  · exact hm

/-- The instance of an additive monoid on `FieldStatistic`. -/
instance : AddMonoid FieldStatistic where
  zero := bosonic
  add a b := a * b
  nsmul n a := ∏ (i : Fin n), a
  zero_add a := by
    cases a <;> simp only [instCommGroup] <;> rfl
  add_zero a := by
    cases a <;>
      simp only [instCommGroup] <;> rfl
  add_assoc a b c := by
    cases a <;> cases b <;> cases c <;> simp only [instCommGroup] <;> rfl
  nsmul_zero a := by
    simp only [Finset.univ_eq_empty, Finset.prod_const, instCommGroup, Finset.card_empty, pow_zero]
    rfl
  nsmul_succ a n := by
    simp only [instCommGroup, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl

@[target] lemma add_eq_mul (a b : FieldStatistic) : a + b = a * b := by sorry


end ofListTake
end FieldStatistic
