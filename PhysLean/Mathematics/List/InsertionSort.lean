import VerifiedAgora.tagger
/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.List
/-!
# List lemmas

-/
namespace PhysLean.List

open Fin
open PhysLean
variable {n : Nat}

@[target] lemma insertionSortMin_lt_length_succ {α : Type} (r : α → α → Prop) [DecidableRel r]
    (i : α) (l : List α) :
    insertionSortMinPos r i l < (insertionSortDropMinPos r i l).length.succ := by
  sorry


/-- Given a list `i :: l` the left-most minimal position `a` of `i :: l` wrt `r`
  as an element of `Fin (insertionSortDropMinPos r i l).length.succ`. -/
def insertionSortMinPosFin {α : Type} (r : α → α → Prop) [DecidableRel r] (i : α) (l : List α) :
    Fin (insertionSortDropMinPos r i l).length.succ :=
  ⟨insertionSortMinPos r i l, insertionSortMin_lt_length_succ r i l⟩

lemma insertionSortMin_lt_mem_insertionSortDropMinPos {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a : α) (l : List α)
    (i : Fin (insertionSortDropMinPos r a l).length) :
    r (insertionSortMin r a l) ((insertionSortDropMinPos r a l)[i]) := by
  let l1 := List.insertionSort r (a :: l)
  have hl1 : l1.Pairwise r := List.pairwise_insertionSort r (a :: l)
  simp only [l1] at hl1
  rw [insertionSort_eq_insertionSortMin_cons r a l] at hl1
  simp only [List.pairwise_cons, List.mem_insertionSort] at hl1
  apply hl1.1 ((insertionSortDropMinPos r a l)[i])
  simp

lemma insertionSortMinPos_insertionSortEquiv {α : Type} (r : α → α → Prop) [DecidableRel r]
    (a : α) (l : List α) :
    insertionSortEquiv r (a ::l) (insertionSortMinPos r a l) =
    ⟨0, by simp [List.orderedInsert_length]⟩ := by
  rw [insertionSortMinPos]
  exact Equiv.apply_symm_apply (insertionSortEquiv r (a :: l)) ⟨0, _⟩

@[target] lemma insertionSortEquiv_gt_zero_of_ne_insertionSortMinPos {α : Type} (r : α → α → Prop)
    [DecidableRel r] (a : α) (l : List α) (k : Fin (a :: l).length)
    (hk : k ≠ insertionSortMinPos r a l) :
    ⟨0, by sorry


@[target] lemma insertionSortMin_lt_mem_insertionSortDropMinPos_of_lt {α : Type} (r : α → α → Prop)
    [DecidableRel r] (a : α) (l : List α)
    (i : Fin (insertionSortDropMinPos r a l).length)
    (h : (insertionSortMinPosFin r a l).succAbove i < insertionSortMinPosFin r a l) :
    ¬ r ((insertionSortDropMinPos r a l)[i]) (insertionSortMin r a l) := by
  sorry


@[target] lemma insertionSort_insertionSort {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (l1 : List α) :
    List.insertionSort r (List.insertionSort r l1) = List.insertionSort r l1 := by
  sorry


@[target] lemma orderedInsert_commute {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a b : α) (hr : ¬ r a b) : (l : List α) →
    List.orderedInsert r a (List.orderedInsert r b l) =
      List.orderedInsert r b (List.orderedInsert r a l)
  | [] => by
    sorry


@[target] lemma insertionSort_orderedInsert_append {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a : α) : (l1 l2 : List α) →
    List.insertionSort r (List.orderedInsert r a l1 ++ l2) = List.insertionSort r (a :: l1 ++ l2)
  | [], l2 => by
    sorry


lemma insertionSort_insertionSort_append {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] : (l1 l2 : List α) →
    List.insertionSort r (List.insertionSort r l1 ++ l2) = List.insertionSort r (l1 ++ l2)
  | [], l2 => by
    simp
  | a :: l1, l2 => by
    conv_lhs => simp
    rw [insertionSort_orderedInsert_append]
    simp only [List.cons_append, List.insertionSort_cons]
    rw [insertionSort_insertionSort_append r l1 l2]

@[target] lemma insertionSort_append_insertionSort_append {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] : (l1 l2 l3 : List α) →
    List.insertionSort r (l1 ++ List.insertionSort r l2 ++ l3) =
      List.insertionSort r (l1 ++ l2 ++ l3)
  | [], l2, l3 => by
    sorry


@[target] lemma orderedInsert_length {α : Type} (r : α → α → Prop) [DecidableRel r] (a : α) (l : List α) :
    (List.orderedInsert r a l).length = (a :: l).length := by
  sorry


@[target] lemma takeWhile_orderedInsert {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r]
    (a b : α) (hr : ¬ r a b) : (l : List α) →
    (List.takeWhile (fun c => !decide (r a c)) (List.orderedInsert r b l)).length =
    (List.takeWhile (fun c => !decide (r a c)) l).length + 1
  | [] => by
    sorry


lemma takeWhile_orderedInsert' {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r]
    (a b : α) (hr : ¬ r a b) : (l : List α) →
    (List.takeWhile (fun c => !decide (r b c)) (List.orderedInsert r a l)).length =
    (List.takeWhile (fun c => !decide (r b c)) l).length
  | [] => by
    simp only [List.orderedInsert, List.takeWhile_nil, List.length_nil, List.length_eq_zero_iff,
      List.takeWhile_eq_nil_iff, List.length_singleton, zero_lt_one, Fin.zero_eta, Fin.isValue,
      List.get_eq_getElem, Fin.val_eq_zero, List.getElem_cons_zero, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not, Decidable.not_not, forall_const]
    have ht := IsTotal.total (r := r) a b
    simp_all
  | c :: l => by
    have hrba : r b a:= by
      have ht := IsTotal.total (r := r) a b
      simp_all
    simp only [List.orderedInsert]
    by_cases h : r b c
    · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, not_false_eq_true,
      List.takeWhile_cons_of_neg, List.length_nil, List.length_eq_zero_iff,
      List.takeWhile_eq_nil_iff,
      List.get_eq_getElem, Bool.not_eq_eq_eq_not, decide_eq_false_iff_not, Decidable.not_not]
      by_cases hac : r a c
      · simp [hac, hrba]
      · simp [hac, h]
    · by_cases hac : r a c
      · refine False.elim (h ?_)
        exact IsTrans.trans _ _ _ hrba hac
      · simp only [hac, ↓reduceIte, h, decide_false, Bool.not_false, List.takeWhile_cons_of_pos,
        List.length_cons, add_left_inj]
        exact takeWhile_orderedInsert' r a b hr l

@[target] lemma insertionSortEquiv_commute {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a b : α) (hr : ¬ r a b) (n : ℕ) : (l : List α) →
    (hn : n + 2 < (a :: b :: l).length) →
    insertionSortEquiv r (a :: b :: l) ⟨n + 2, hn⟩ = (finCongr (by sorry


@[target] lemma insertionSortEquiv_orderedInsert_append {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a a2 : α) : (l1 l2 : List α) →
    (insertionSortEquiv r (List.orderedInsert r a l1 ++ a2 :: l2) ⟨l1.length + 1, by
      sorry


@[target] lemma insertionSortEquiv_insertionSort_append {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a : α) : (l1 l2 : List α) →
    (insertionSortEquiv r (List.insertionSort r l1 ++ a :: l2) ⟨l1.length, by sorry


@[target] lemma orderedInsert_filter_of_pos {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTrans α r] (a : α) (p : α → Prop) [DecidablePred p] (h : p a) : (l : List α) →
    (hl : l.Sorted r) →
    List.filter p (List.orderedInsert r a l) = List.orderedInsert r a (List.filter p l)
  | [], hl => by
    sorry


@[target] lemma orderedInsert_filter_of_neg {α : Type} (r : α → α → Prop) [DecidableRel r]
    (a : α) (p : α → Prop) [DecidablePred p] (h : ¬ p a) (l : List α) :
    List.filter p (List.orderedInsert r a l) = (List.filter p l) := by
  sorry


@[target] lemma insertionSort_filter {α : Type} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] (p : α → Prop) [DecidablePred p] : (l : List α) →
    List.insertionSort r (List.filter p l) =
    List.filter p (List.insertionSort r l)
  | [] => by sorry


@[target] lemma takeWhile_sorted_eq_filter {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTrans α r] (a : α) : (l : List α) → (hl : l.Sorted r) →
    List.takeWhile (fun c => ¬ r a c) l = List.filter (fun c => ¬ r a c) l
  | [], _ => by sorry


@[target] lemma dropWhile_sorted_eq_filter {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTrans α r] (a : α) : (l : List α) → (hl : l.Sorted r) →
    List.dropWhile (fun c => ¬ r a c) l = List.filter (fun c => r a c) l
  | [], _ => by sorry


@[target] lemma dropWhile_sorted_eq_filter_filter {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTrans α r] (a : α) :(l : List α) → (hl : l.Sorted r) →
    List.filter (fun c => r a c) l =
    List.filter (fun c => r a c ∧ r c a) l ++ List.filter (fun c => r a c ∧ ¬ r c a) l
  | [], _ => by
    sorry


lemma filter_rel_eq_insertionSort {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a : α) : (l : List α) →
    List.filter (fun c => r a c ∧ r c a) (l.insertionSort r) =
    List.filter (fun c => r a c ∧ r c a) l
  | [] => by simp
  | b :: l => by
    simp only [List.insertionSort]
    by_cases h : r a b ∧ r b a
    · have hl := orderedInsert_filter_of_pos r b (fun c => r a c ∧ r c a) h
        (List.insertionSort r l) (by exact List.pairwise_insertionSort r l)
      simp only [Bool.decide_and] at hl ⊢
      erw [hl]
      rw [List.orderedInsert_eq_take_drop]
      have ht : List.takeWhile (fun b_1 => decide ¬r b b_1)
        (List.filter (fun b => decide (r a b) && decide (r b a))
          (List.insertionSort r l)) = [] := by
        rw [List.takeWhile_eq_nil_iff]
        intro hl
        simp only [List.get_eq_getElem, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
          decide_eq_false_iff_not, Decidable.not_not]
        have hx := List.getElem_mem hl
        simp only [List.mem_filter, List.mem_insertionSort, Bool.and_eq_true,
          decide_eq_true_eq] at hx
        apply IsTrans.trans b a _ h.2
        simp_all
      rw [ht]
      simp only [decide_not, List.nil_append]
      rw [List.filter_cons_of_pos]
      simp only [List.cons.injEq, true_and]
      have ih := filter_rel_eq_insertionSort r a l
      simp only [Bool.decide_and] at ih
      rw [← ih]
      have htd := List.takeWhile_append_dropWhile (p := fun b_1 => decide ¬r b b_1)
        (l := List.filter (fun b => decide (r a b) && decide (r b a)) (List.insertionSort r l))
      simp only [decide_not] at htd
      conv_rhs => rw [← htd]
      simp only [List.self_eq_append_left, List.takeWhile_eq_nil_iff, List.get_eq_getElem,
        Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Decidable.not_not]
      intro hl
      have hx := List.getElem_mem hl
      simp only [List.mem_filter, List.mem_insertionSort, Bool.and_eq_true, decide_eq_true_eq] at hx
      apply IsTrans.trans b a _ h.2
      simp_all only [decide_not, List.takeWhile_eq_nil_iff, List.get_eq_getElem,
        Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Decidable.not_not,
        List.takeWhile_append_dropWhile]
      simp_all
    · have hl := orderedInsert_filter_of_neg r b (fun c => r a c ∧ r c a) h (List.insertionSort r l)
      simp only [Bool.decide_and] at hl ⊢
      erw [hl]
      rw [List.filter_cons_of_neg]
      have ih := filter_rel_eq_insertionSort r a l
      simp_all only [not_and, Bool.decide_and]
      simpa using h

@[target] lemma insertionSort_of_eq_list {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a : α) (l1 l l2 : List α)
    (h : ∀ b ∈ l, r a b ∧ r b a) :
    List.insertionSort r (l1 ++ l ++ l2) =
    (List.takeWhile (fun c => ¬ r a c) ((l1 ++ l2).insertionSort r))
    ++ (List.filter (fun c => r a c ∧ r c a) l1)
    ++ l
    ++ (List.filter (fun c => r a c ∧ r c a) l2)
    ++ (List.filter (fun c => r a c ∧ ¬ r c a) ((l1 ++ l2).insertionSort r)) := by
  sorry


@[target] lemma insertionSort_of_takeWhile_filter {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a : α) (l1 l2 : List α) :
    List.insertionSort r (l1 ++ l2) =
    (List.takeWhile (fun c => ¬ r a c) ((l1 ++ l2).insertionSort r))
    ++ (List.filter (fun c => r a c ∧ r c a) l1)
    ++ (List.filter (fun c => r a c ∧ r c a) l2)
    ++ (List.filter (fun c => r a c ∧ ¬ r c a) ((l1 ++ l2).insertionSort r)) := by
  sorry


end PhysLean.List
