import VerifiedAgora.tagger
/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.List.Sort
import Mathlib.Algebra.Order.Ring.Nat
/-!
# List lemmas

-/
namespace PhysLean.List

open Fin
open PhysLean
variable {n : Nat}

@[target] lemma insertIdx_map {I J : Type} (f : I → J) : (i : ℕ) → (r : List I) → (r0 : I) →
    (List.insertIdx i r0 r).map f = List.insertIdx i (f r0) (r.map f)
  | 0, [], r0 => by sorry


@[target] lemma eraseIdx_sorted {I : Type} (le : I → I → Prop) :
    (r : List I) → (n : ℕ) →
    List.Sorted le r → List.Sorted le (r.eraseIdx n)
  | [], _, _ => by sorry


@[target] lemma mem_eraseIdx_nodup {I : Type} (i : I) :
    (l : List I) → (n : ℕ) → (hn : n < l.length) → (h : List.Nodup l) →
    i ∈ l.eraseIdx n ↔ i ∈ l ∧ i ≠ l[n]
  | [], _, _, _ => by sorry


lemma insertIdx_eq_take_drop {I : Type} (i : I) : (r : List I) → (n : Fin r.length.succ) →
    List.insertIdx r n i = List.take n r ++ i :: r.drop n
  | [], 0 => by simp
  | a :: as, 0 => by
    simp
  | a :: as, ⟨n + 1, h⟩ => by
    simp only [List.insertIdx_succ_cons, List.take_succ_cons, List.drop_succ_cons, List.cons_append,
      List.cons.injEq, true_and]
    exact insertIdx_eq_take_drop i as ⟨n, Nat.succ_lt_succ_iff.mp h⟩

@[target] lemma insertIdx_length_fin {I : Type} (i : I) :
    (r : List I) → (n : Fin r.length.succ) →
    (List.insertIdx n i r).length = r.length.succ
  | [], 0 => by sorry


@[target] lemma insertIdx_getElem_fin {I : Type} (i : I) :
    (r : List I) → (k : Fin r.length.succ) → (m : Fin r.length) →
    (List.insertIdx k i r)[(k.succAbove m).val] = r[m.val]
  | [], 0, m => by sorry


@[target] lemma insertIdx_eraseIdx_fin {I : Type} :
    (r : List I) → (k : Fin r.length) →
    (List.eraseIdx r k).insertIdx k r[k] = r
  | [], k => by sorry


@[target] lemma insertIdx_length_fst_append {I : Type} (φ : I) : (φs φs' : List I) →
    List.insertIdx φs.length φ (φs ++ φs') = (φs ++ φ :: φs')
  | [], φs' => by sorry


lemma get_eq_insertIdx_succAbove {I : Type} (i : I) (r : List I) (k : Fin r.length.succ) :
    r.get = (List.insertIdx r k i).get ∘
    (finCongr (insertIdx_length_fin i r k).symm) ∘ k.succAbove := by
  funext i
  simp

@[target] lemma take_insert_same {I : Type} (i : I) :
    (n : ℕ) → (r : List I) →
    List.take n (List.insertIdx n i r) = List.take n r
  | 0, _ => by sorry


@[target] lemma take_eraseIdx_same {I : Type} :
    (n : ℕ) → (r : List I) →
    List.take n (List.eraseIdx r n) = List.take n r
  | 0, _ => by sorry


@[target] lemma drop_eraseIdx_succ {I : Type} :
    (n : ℕ) → (r : List I) → (hn : n < r.length) →
    r[n] :: List.drop n (List.eraseIdx r n) = List.drop n r
  | 0, _, _=> by
    sorry


@[target] lemma take_insert_gt {I : Type} (i : I) :
    (n m : ℕ) → (h : n < m) → (r : List I) →
    List.take n (List.insertIdx m i r) = List.take n r
  | 0, 0, _, _ => by sorry


@[target] lemma take_insert_let {I : Type} (i : I) :
    (n m : ℕ) → (h : m ≤ n) → (r : List I) → (hm : m ≤ r.length) →
    (List.take (n + 1) (List.insertIdx m i r)).Perm (i :: List.take n r)
  | 0, 0, h, _, _ => by sorry


end PhysLean.List
