import VerifiedAgora.tagger
/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.Fin
import Mathlib.Data.Nat.Lattice
/-!
# List lemmas

-/
namespace PhysLean.List

open Fin
open PhysLean
variable {n : Nat}

@[target] lemma takeWile_eraseIdx {I : Type} (P : I → Prop) [DecidablePred P] :
    (l : List I) → (i : ℕ) → (hi : ∀ (i j : Fin l.length), i < j → P (l.get j) → P (l.get i)) →
    List.takeWhile P (List.eraseIdx l i) = (List.takeWhile P l).eraseIdx i
  | [], _, h => by
    sorry


@[target] lemma dropWile_eraseIdx {I : Type} (P : I → Prop) [DecidablePred P] :
    (l : List I) → (i : ℕ) → (hi : ∀ (i j : Fin l.length), i < j → P (l.get j) → P (l.get i)) →
    List.dropWhile P (List.eraseIdx l i) =
      if (List.takeWhile P l).length ≤ i then
        (List.dropWhile P l).eraseIdx (i - (List.takeWhile P l).length)
      else (List.dropWhile P l)
  | [], _, h => by
    sorry


@[target] lemma insertionSort_length {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (l : List I) :
    (List.insertionSort le1 l).length = l.length := by
  sorry


/-- The position `r0` ends up in `r` on adding it via `List.orderedInsert _ r0 r`. -/
/-- The position `r0` ends up in `r` on adding it via `List.orderedInsert _ r0 r`. -/
def orderedInsertPos {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I) (r0 : I) :
    Fin (List.orderedInsert le1 r0 r).length :=
  ⟨(List.takeWhile (fun b => decide ¬ le1 r0 b) r).length, by
    sorry


@[target] lemma orderedInsertPos_lt_length {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) : orderedInsertPos le1 r r0 < (r0 :: r).length := by
  sorry


@[target] lemma orderedInsert_get_orderedInsertPos {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    (List.orderedInsert le1 r0 r)[(orderedInsertPos le1 r r0).val] = r0 := by
  sorry


@[target] lemma orderedInsert_eraseIdx_orderedInsertPos {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    (List.orderedInsert le1 r0 r).eraseIdx ↑(orderedInsertPos le1 r r0) = r := by
  sorry


@[target] lemma orderedInsertPos_cons {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 r1 : I) :
    (orderedInsertPos le1 (r1 ::r) r0).val =
    if le1 r0 r1 then ⟨0, by sorry


@[target] lemma orderedInsertPos_sigma {I : Type} {f : I → Type}
    (le1 : I → I → Prop) [DecidableRel le1] (l : List (Σ i, f i))
    (k : I) (a : f k) :
    (orderedInsertPos (fun (i j : Σ i, f i) => le1 i.1 j.1) l ⟨k, a⟩).1 =
    (orderedInsertPos le1 (List.map (fun (i : Σ i, f i) => i.1) l) k).1 := by
  sorry


@[target] lemma orderedInsert_get_lt {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) (i : ℕ)
    (hi : i < orderedInsertPos le1 r r0) :
    (List.orderedInsert le1 r0 r)[i] = r.get ⟨i, by
      sorry


@[target] lemma orderedInsertPos_take_orderedInsert {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    (List.take (orderedInsertPos le1 r r0) (List.orderedInsert le1 r0 r)) =
    List.takeWhile (fun b => decide ¬le1 r0 b) r := by
  sorry


@[target] lemma orderedInsertPos_take_eq_orderedInsert {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    List.take (orderedInsertPos le1 r r0) r =
    List.take (orderedInsertPos le1 r r0) (List.orderedInsert le1 r0 r) := by
  sorry


lemma orderedInsertPos_drop_eq_orderedInsert {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    List.drop (orderedInsertPos le1 r r0) r =
    List.drop (orderedInsertPos le1 r r0).succ (List.orderedInsert le1 r0 r) := by
  conv_rhs => simp [orderedInsertPos, List.orderedInsert_eq_take_drop]
  have hr : r = List.takeWhile (fun b => !decide (le1 r0 b)) r ++
      List.dropWhile (fun b => !decide (le1 r0 b)) r := by
    exact Eq.symm (List.takeWhile_append_dropWhile)
  conv_lhs =>
    rhs
    rw [hr]
  rw [List.drop_append]
  simp [orderedInsertPos]

@[target] lemma orderedInsertPos_take {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    List.take (orderedInsertPos le1 r r0) r = List.takeWhile (fun b => decide ¬le1 r0 b) r := by
  sorry


@[target] lemma orderedInsertPos_drop {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    List.drop (orderedInsertPos le1 r r0) r = List.dropWhile (fun b => decide ¬le1 r0 b) r := by
  sorry


@[target] lemma orderedInsertPos_succ_take_orderedInsert {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    (List.take (orderedInsertPos le1 r r0).succ (List.orderedInsert le1 r0 r)) =
    List.takeWhile (fun b => decide ¬le1 r0 b) r ++ [r0] := by
  sorry


@[target] lemma lt_orderedInsertPos_rel {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r0 : I) (r : List I) (n : Fin r.length)
    (hn : n.val < (orderedInsertPos le1 r r0).val) : ¬ le1 r0 (r.get n) := by
  sorry


lemma lt_orderedInsertPos_rel_fin {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r0 : I) (r : List I) (n : Fin (List.orderedInsert le1 r0 r).length)
    (hn : n < (orderedInsertPos le1 r r0)) : ¬ le1 r0 ((List.orderedInsert le1 r0 r).get n) := by
  have htake : (List.orderedInsert le1 r0 r).get n ∈ List.take (orderedInsertPos le1 r r0) r := by
    rw [orderedInsertPos_take_eq_orderedInsert, List.mem_take_iff_getElem]
    use n
    simp only [List.get_eq_getElem, Fin.is_le', inf_of_le_left, Fin.val_fin_lt, exists_prop,
      and_true]
    exact hn
  rw [orderedInsertPos_take] at htake
  simpa using List.mem_takeWhile_imp htake

@[target] lemma gt_orderedInsertPos_rel {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    [IsTotal I le1] [IsTrans I le1] (r0 : I) (r : List I) (hs : List.Sorted le1 r)
    (n : Fin r.length)
    (hn : ¬ n.val < (orderedInsertPos le1 r r0).val) : le1 r0 (r.get n) := by
  sorry


@[target] lemma orderedInsert_eraseIdx_lt_orderedInsertPos {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) (i : ℕ)
    (hi : i < orderedInsertPos le1 r r0)
    (hr : ∀ (i j : Fin r.length), i < j → ¬le1 r0 (r.get j) → ¬le1 r0 (r.get i)) :
    (List.orderedInsert le1 r0 r).eraseIdx i = List.orderedInsert le1 r0 (r.eraseIdx i) := by
  sorry


@[target] lemma orderedInsert_eraseIdx_orderedInsertPos_le {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) (i : ℕ)
    (hi : orderedInsertPos le1 r r0 ≤ i)
    (hr : ∀ (i j : Fin r.length), i < j → ¬le1 r0 (r.get j) → ¬le1 r0 (r.get i)) :
    (List.orderedInsert le1 r0 r).eraseIdx (Nat.succ i) =
    List.orderedInsert le1 r0 (r.eraseIdx i) := by
  sorry


/-- The equivalence between `Fin (r0 :: r).length` and `Fin (List.orderedInsert le1 r0 r).length`
  according to where the elements map, i.e. `0` is taken to `orderedInsertPos le1 r r0`. -/
/-- The equivalence between `Fin (r0 :: r).length` and `Fin (List.orderedInsert le1 r0 r).length`
  according to where the elements map, i.e. `0` is taken to `orderedInsertPos le1 r r0`. -/
def orderedInsertEquiv {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I) (r0 : I) :
    Fin (r0 :: r).length ≃ Fin (List.orderedInsert le1 r0 r).length := by
  sorry


@[target] lemma orderedInsertEquiv_zero {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) : orderedInsertEquiv le1 r r0 ⟨0, by sorry


@[target] lemma orderedInsertEquiv_succ {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) (n : ℕ) (hn : Nat.succ n < (r0 :: r).length) :
    orderedInsertEquiv le1 r r0 ⟨Nat.succ n, hn⟩ =
    Fin.cast (List.orderedInsert_length le1 r r0).symm
    ((Fin.succAbove ⟨(orderedInsertPos le1 r r0), orderedInsertPos_lt_length le1 r r0⟩)
    ⟨n, Nat.succ_lt_succ_iff.mp hn⟩) := by
  sorry


@[target] lemma orderedInsertEquiv_fin_succ {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) (n : Fin r.length) :
    orderedInsertEquiv le1 r r0 n.succ = Fin.cast (List.orderedInsert_length le1 r r0).symm
    ((Fin.succAbove ⟨(orderedInsertPos le1 r r0), orderedInsertPos_lt_length le1 r r0⟩)
      ⟨n, n.isLt⟩) := by
  sorry


@[target] lemma orderedInsertEquiv_monotone_fin_succ {I : Type}
    (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) (n m : Fin r.length)
    (hx : orderedInsertEquiv le1 r r0 n.succ < orderedInsertEquiv le1 r r0 m.succ) :
    n < m := by
  sorry


@[target] lemma orderedInsertEquiv_congr {α : Type} {r : α → α → Prop} [DecidableRel r] (a : α)
    (l l' : List α) (h : l = l') :
    orderedInsertEquiv r l a = (Fin.castOrderIso (by sorry


@[target] lemma get_eq_orderedInsertEquiv {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) :
    (r0 :: r).get = (List.orderedInsert le1 r0 r).get ∘ (orderedInsertEquiv le1 r r0) := by
  sorry


@[target] lemma orderedInsertEquiv_get {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) :
    (r0 :: r).get ∘ (orderedInsertEquiv le1 r r0).symm = (List.orderedInsert le1 r0 r).get := by
  sorry


lemma orderedInsert_eraseIdx_orderedInsertEquiv_zero
    {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I) (r0 : I) :
    (List.orderedInsert le1 r0 r).eraseIdx (orderedInsertEquiv le1 r r0 ⟨0, by simp⟩) = r := by
  simp [orderedInsertEquiv]

@[target] lemma orderedInsert_eraseIdx_orderedInsertEquiv_succ
    {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I) (r0 : I) (n : ℕ)
    (hn : Nat.succ n < (r0 :: r).length)
    (hr : ∀ (i j : Fin r.length), i < j → ¬le1 r0 (r.get j) → ¬le1 r0 (r.get i)) :
    (List.orderedInsert le1 r0 r).eraseIdx (orderedInsertEquiv le1 r r0 ⟨Nat.succ n, hn⟩) =
    (List.orderedInsert le1 r0 (r.eraseIdx n)) := by
  sorry


@[target] lemma orderedInsert_eraseIdx_orderedInsertEquiv_fin_succ
    {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I) (r0 : I) (n : Fin r.length)
    (hr : ∀ (i j : Fin r.length), i < j → ¬le1 r0 (r.get j) → ¬le1 r0 (r.get i)) :
    (List.orderedInsert le1 r0 r).eraseIdx (orderedInsertEquiv le1 r r0 n.succ) =
    (List.orderedInsert le1 r0 (r.eraseIdx n)) := by
  sorry


lemma orderedInsertEquiv_sigma {I : Type} {f : I → Type}
    (le1 : I → I → Prop) [DecidableRel le1] (l : List (Σ i, f i))
    (i : I) (a : f i) :
    (orderedInsertEquiv (fun i j => le1 i.fst j.fst) l ⟨i, a⟩) =
    (Fin.castOrderIso (by simp)).toEquiv.trans
    ((orderedInsertEquiv le1 (List.map (fun i => i.1) l) i).trans
    (Fin.castOrderIso (by simp [List.orderedInsert_length])).toEquiv) := by
  ext x
  match x with
  | ⟨0, h0⟩ =>
    simp only [Fin.zero_eta, Equiv.trans_apply, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply,
      Fin.cast_zero, Fin.coe_cast]
    rw [orderedInsertEquiv_zero, orderedInsertEquiv_zero]
    simp [orderedInsertPos_sigma]
  | ⟨Nat.succ n, h0⟩ =>
    simp only [Nat.succ_eq_add_one, Equiv.trans_apply, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, Fin.cast_mk, Fin.coe_cast]
    erw [orderedInsertEquiv_succ, orderedInsertEquiv_succ]
    simp only [orderedInsertPos_sigma, Fin.coe_cast]
    rw [Fin.succAbove, Fin.succAbove]
    simp only [Fin.castSucc_mk, Fin.mk_lt_mk, Fin.succ_mk]
    split
    · rfl
    · rfl

@[target] lemma orderedInsert_eq_insertIdx_orderedInsertPos {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    List.orderedInsert le1 r0 r = List.insertIdx (orderedInsertPos le1 r r0).1 r0 r := by
  sorry


/-- The equivalence between `Fin l.length ≃ Fin (List.insertionSort r l).length` induced by the
  sorting algorithm. -/
def insertionSortEquiv {α : Type} (r : α → α → Prop) [DecidableRel r] : (l : List α) →
    Fin l.length ≃ Fin (List.insertionSort r l).length
  | [] => Equiv.refl _
  | a :: l =>
    (Fin.equivCons (insertionSortEquiv r l)).trans (orderedInsertEquiv r (List.insertionSort r l) a)

@[target] lemma insertionSortEquiv_get {α : Type} {r : α → α → Prop} [DecidableRel r] : (l : List α) →
    l.get ∘ (insertionSortEquiv r l).symm = (List.insertionSort r l).get
  | [] => by sorry


@[target] lemma insertionSortEquiv_congr {α : Type} {r : α → α → Prop} [DecidableRel r] (l l' : List α)
    (h : l = l') : insertionSortEquiv r l = (Fin.castOrderIso (by sorry


lemma insertionSortEquiv_congr_apply {α : Type} {r : α → α → Prop} [DecidableRel r] (l l' : List α)
    (h : l = l') (i : Fin l.length) :
    insertionSortEquiv r l i =
    Fin.cast (by simp [h])
    ((insertionSortEquiv r l') (Fin.cast (by simp [h]) i)) := by
  rw [insertionSortEquiv_congr l l' h]
  simp

lemma insertionSort_get_comp_insertionSortEquiv {α : Type} {r : α → α → Prop} [DecidableRel r]
    (l : List α) : (List.insertionSort r l).get ∘ (insertionSortEquiv r l) = l.get := by
  rw [← insertionSortEquiv_get]
  funext x
  simp

@[target] lemma insertionSort_eq_ofFn {α : Type} {r : α → α → Prop} [DecidableRel r] (l : List α) :
    List.insertionSort r l = List.ofFn (l.get ∘ (insertionSortEquiv r l).symm) := by
  sorry


@[target] lemma insertionSortEquiv_order {α : Type} {r : α → α → Prop} [DecidableRel r] :
    (l : List α) → (i : Fin l.length) → (j : Fin l.length) → (hij : i < j)
    → (hij' : insertionSortEquiv r l j < insertionSortEquiv r l i) →
    ¬ r l[i] l[j]
  | [], i, _, _, _ => Fin.elim0 i
  | a :: as, ⟨0, hi⟩, ⟨j + 1, hj⟩, hij, hij' => by
    sorry


/-- Optional erase of an element in a list. For `none` returns the list, for `some i` returns
  the list with the `i`'th element erased. -/
/-- Optional erase of an element in a list. For `none` returns the list, for `some i` returns
  the list with the `i`'th element erased. -/
def optionErase {I : Type} (l : List I) (i : Option (Fin l.length)) : List I := by sorry


@[target] lemma eraseIdx_length {I : Type} (l : List I) (i : Fin l.length) :
    (List.eraseIdx l i).length + 1 = l.length := by
  sorry


lemma eraseIdx_length {I : Type} (l : List I) (i : Fin l.length) :
    (List.eraseIdx l i).length + 1 = l.length := by
  simp only [List.length_eraseIdx, Fin.is_lt, ↓reduceIte]
  have hi := i.prop
  omega

@[target] lemma eraseIdx_length_succ {I : Type} (l : List I) (i : Fin l.length) :
    (List.eraseIdx l i).length.succ = l.length := by
  sorry


@[target] lemma eraseIdx_cons_length {I : Type} (a : I) (l : List I) (i : Fin (a :: l).length) :
    (List.eraseIdx (a :: l) i).length= l.length := by
  sorry


@[target] lemma eraseIdx_get {I : Type} (l : List I) (i : Fin l.length) :
    (List.eraseIdx l i).get = l.get ∘ (Fin.cast (eraseIdx_length l i)) ∘
    (Fin.cast (eraseIdx_length l i).symm i).succAbove := by
  sorry


@[target] lemma eraseIdx_insertionSort {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    [IsTotal I le1] [IsTrans I le1] :
    (n : ℕ) → (r : List I) → (hn : n < r.length) →
    (List.insertionSort le1 r).eraseIdx ↑((insertionSortEquiv le1 r) ⟨n, hn⟩)
    = List.insertionSort le1 (r.eraseIdx n)
  | 0, [], _ => by sorry


@[target] lemma eraseIdx_insertionSort_fin {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    [IsTotal I le1] [IsTrans I le1] (r : List I) (n : Fin r.length) :
    (List.insertionSort le1 r).eraseIdx ↑((HepLean.List.insertionSortEquiv le1 r) n)
    = List.insertionSort le1 (r.eraseIdx n) := by sorry


/-- Given a list `i :: l` the left-most minimal position `a` of `i :: l` wrt `r`.
  That is the first position
  of `l` such that for every element `(i :: l)[b]` before that position
  `r ((i :: l)[b]) ((i :: l)[a])` is not true. The use of `i :: l` here
  rather then just `l` is to ensure that such a position exists. . -/
/-- Given a list `i :: l` the left-most minimal position `a` of `i :: l` wrt `r`.
  That is the first position
  of `l` such that for every element `(i :: l)[b]` before that position
  `r ((i :: l)[b]) ((i :: l)[a])` is not true. The use of `i :: l` here
  rather then just `l` is to ensure that such a position exists. . -/
def insertionSortMinPos {α : Type} (r : α → α → Prop) [DecidableRel r] (i : α) (l : List α) :
    Fin (i :: l).length := (insertionSortEquiv r (i :: l)).symm ⟨0, by
    sorry


/-- The element of `i :: l` at `insertionSortMinPos`. -/
/-- The element of `i :: l` at `insertionSortMinPos`. -/
def insertionSortMin {α : Type} (r : α → α → Prop) [DecidableRel r] (i : α) (l : List α) :
    α := by sorry


@[target] lemma insertionSortMin_eq_insertionSort_head {α : Type} (r : α → α → Prop) [DecidableRel r]
    (i : α) (l : List α) :
    insertionSortMin r i l = (List.insertionSort r (i :: l)).head (by
    sorry


/-- The list remaining after dropping the element at the position determined by
  `insertionSortMinPos`. -/
/-- The list remaining after dropping the element at the position determined by
  `insertionSortMinPos`. -/
def insertionSortDropMinPos {α : Type} (r : α → α → Prop) [DecidableRel r] (i : α) (l : List α) :
    List α := by sorry


@[target] lemma insertionSort_eq_insertionSortMin_cons {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (i : α) (l : List α) :
    List.insertionSort r (i :: l) =
    (insertionSortMin r i l) :: List.insertionSort r (insertionSortDropMinPos r i l) := by
  sorry


/-- Optional erase of an element in a list, with addition for `none`. For `none` adds `a` to the
  front of the list, for `some i` removes the `i`th element of the list (does not add `a`).
  E.g. `optionEraseZ [0, 1, 2] 4 none = [4, 0, 1, 2]` and
  `optionEraseZ [0, 1, 2] 4 (some 1) = [0, 2]`. -/
/-- Optional erase of an element in a list, with addition for `none`. For `none` adds `a` to the
  front of the list, for `some i` removes the `i`th element of the list (does not add `a`).
  E.g. `optionEraseZ [0, 1, 2] 4 none = [4, 0, 1, 2]` and
  `optionEraseZ [0, 1, 2] 4 (some 1) = [0, 2]`. -/
def optionEraseZ {I : Type} (l : List I) (a : I) (i : Option (Fin l.length)) : List I := by sorry


@[simp]
lemma optionEraseZ_some_length {I : Type} (l : List I) (a : I) (i : (Fin l.length)) :
    (optionEraseZ l a (some i)).length = l.length - 1 := by
  simp [optionEraseZ, List.length_eraseIdx]

@[target] lemma optionEraseZ_ext {I : Type} {l l' : List I} {a a' : I} {i : Option (Fin l.length)}
    {i' : Option (Fin l'.length)} (hl : l = l') (ha : a = a')
    (hi : Option.map (Fin.cast (by sorry


@[target] lemma mem_take_finrange : (n m : ℕ) → (a : Fin n) → a ∈ List.take m (List.finRange n) ↔ a.val < m
  | 0, m, a => Fin.elim0 a
  | n+1, 0, a => by
    sorry


end PhysLean.List
