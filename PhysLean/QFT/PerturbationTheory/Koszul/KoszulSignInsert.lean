import VerifiedAgora.tagger
/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.PerturbationTheory.FieldStatistics.ExchangeSign
import PhysLean.Mathematics.List
/-!

# Koszul sign insert

-/

namespace Wick

open PhysLean.List
open FieldStatistic

variable {𝓕 : Type} (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le]

/-- Gives a factor of `-1` when inserting `a` into a list `List I` in the ordered position
  for each fermion-fermion cross. -/
def koszulSignInsert {𝓕 : Type} (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop)
    [DecidableRel le] (φ : 𝓕) : List 𝓕 → ℂ
  | [] => 1
  | φ' :: φs => if le φ φ' then koszulSignInsert q le φ φs else
    if q φ = fermionic ∧ q φ' = fermionic then - koszulSignInsert q le φ φs else
      koszulSignInsert q le φ φs

/-- When inserting a boson the `koszulSignInsert` is always `1`. -/
/-- When inserting a boson the `koszulSignInsert` is always `1`. -/
@[target] lemma koszulSignInsert_boson (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le]
    (φ : 𝓕) (ha : q φ = bosonic) : (φs : List 𝓕) → koszulSignInsert q le φ φs = 1
  | [] => by
    sorry


@[simp]
lemma koszulSignInsert_mul_self (φ : 𝓕) :
    (φs : List 𝓕) → koszulSignInsert q le φ φs * koszulSignInsert q le φ φs = 1
  | [] => by
    simp [koszulSignInsert]
  | φ' :: φs => by
    simp only [koszulSignInsert, mul_ite, ite_mul, neg_mul, mul_neg]
    by_cases hr : le φ φ'
    · simp only [hr, ↓reduceIte]
      rw [koszulSignInsert_mul_self]
    · simp only [hr, ↓reduceIte]
      by_cases hq : q φ = fermionic ∧ q φ' = fermionic
      · simp only [hq, and_self, ↓reduceIte, neg_neg]
        rw [koszulSignInsert_mul_self]
      · simp only [hq, ↓reduceIte]
        rw [koszulSignInsert_mul_self]

@[target] lemma koszulSignInsert_le_forall (φ : 𝓕) (φs : List 𝓕) (hi : ∀ φ', le φ φ') :
    koszulSignInsert q le φ φs = 1 := by
  sorry


@[target] lemma koszulSignInsert_ge_forall_append (φs : List 𝓕) (φ' φ : 𝓕) (hi : ∀ φ'', le φ'' φ) :
    koszulSignInsert q le φ' φs = koszulSignInsert q le φ' (φs ++ [φ]) := by
  sorry


@[target] lemma koszulSignInsert_eq_filter (φ : 𝓕) : (φs : List 𝓕) →
    koszulSignInsert q le φ φs =
    koszulSignInsert q le φ (List.filter (fun i => decide (¬ le φ i)) φs)
  | [] => by
    sorry


@[target] lemma koszulSignInsert_eq_cons [IsTotal 𝓕 le] (φ : 𝓕) (φs : List 𝓕) :
    koszulSignInsert q le φ φs = koszulSignInsert q le φ (φ :: φs) := by
  sorry


@[target] lemma koszulSignInsert_eq_grade (φ : 𝓕) (φs : List 𝓕) :
    koszulSignInsert q le φ φs = if ofList q [φ] = fermionic ∧
    ofList q (List.filter (fun i => decide (¬ le φ i)) φs) = fermionic then -1 else 1 := by
  sorry


@[target] lemma koszulSignInsert_eq_perm (φs φs' : List 𝓕) (φ : 𝓕) (h : φs.Perm φs') :
    koszulSignInsert q le φ φs = koszulSignInsert q le φ φs' := by
  sorry


@[target] lemma koszulSignInsert_eq_sort (φs : List 𝓕) (φ : 𝓕) :
    koszulSignInsert q le φ φs = koszulSignInsert q le φ (List.insertionSort le φs) := by
  sorry


lemma koszulSignInsert_eq_exchangeSign_take [IsTotal 𝓕 le] [IsTrans 𝓕 le] (φ : 𝓕) (φs : List 𝓕) :
    koszulSignInsert q le φ φs = 𝓢(q φ, ofList q
    ((List.insertionSort le φs).take (orderedInsertPos le (List.insertionSort le φs) φ))) := by
  rw [koszulSignInsert_eq_cons, koszulSignInsert_eq_sort, koszulSignInsert_eq_filter,
    koszulSignInsert_eq_grade]
  have hx : (exchangeSign (q φ))
      (ofList q (List.take (↑(orderedInsertPos le (List.insertionSort le φs) φ))
      (List.insertionSort le φs))) = if FieldStatistic.ofList q [φ] = fermionic ∧
      FieldStatistic.ofList q (List.take (↑(orderedInsertPos le (List.insertionSort le φs) φ))
      (List.insertionSort le φs)) = fermionic then - 1 else 1 := by
    rw [exchangeSign_eq_if]
    simp
  rw [hx]
  congr
  simp only [List.filter_filter, Bool.and_self]
  rw [List.insertionSort_cons]
  nth_rewrite 1 [List.orderedInsert_eq_take_drop]
  rw [List.filter_append]
  have h1 : List.filter (fun a => decide ¬le φ a)
    (List.takeWhile (fun b => decide ¬le φ b) (List.insertionSort le φs))
    = (List.takeWhile (fun b => decide ¬le φ b) (List.insertionSort le φs)) := by
    induction φs with
    | nil => simp
    | cons r1 r ih =>
      simp only [decide_not, List.insertionSort, List.filter_eq_self, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_false_iff_not]
      intro a ha
      have ha' := List.mem_takeWhile_imp ha
      simp_all
  rw [h1]
  rw [List.filter_cons]
  simp only [decide_not, (IsTotal.to_isRefl le).refl φ, not_true_eq_false, decide_false,
    Bool.false_eq_true, ↓reduceIte]
  rw [orderedInsertPos_take]
  simp only [decide_not, List.append_right_eq_self, List.filter_eq_nil_iff, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not, Decidable.not_not]
  intro a ha
  refine List.Pairwise.rel_of_mem_take_of_mem_drop
    (i := (orderedInsertPos le (List.insertionSort le φs) φ).1 + 1)
    (List.pairwise_insertionSort le (φ :: φs)) ?_ ?_
  · simp only [List.insertionSort, List.foldr_cons, List.orderedInsert_eq_take_drop, decide_not]
    rw [List.take_append]
    rw [List.take_of_length_le]
    · simp [orderedInsertPos]
    · simp [orderedInsertPos]
  · simp only [List.insertionSort_cons, List.orderedInsert_eq_take_drop, decide_not]
    rw [List.drop_append, List.drop_of_length_le]
    · simpa [orderedInsertPos] using ha
    · simp [orderedInsertPos]

@[target] lemma koszulSignInsert_insertIdx (i j : 𝓕) (r : List 𝓕) (n : ℕ) (hn : n ≤ r.length) :
    koszulSignInsert q le j (List.insertIdx n i r) = koszulSignInsert q le j (i :: r) := by
  sorry


/-- The difference in `koszulSignInsert` on inserting `r0` into `r` compared to
  into `r1 :: r` for any `r`. -/
/-- The difference in `koszulSignInsert` on inserting `r0` into `r` compared to
  into `r1 :: r` for any `r`. -/
def koszulSignCons (φ0 φ1 : 𝓕) : ℂ := by sorry


@[target] lemma koszulSignCons_eq_exchangeSign (φ0 φ1 : 𝓕) : koszulSignCons q le φ0 φ1 =
    if le φ0 φ1 then 1 else 𝓢(q φ0, q φ1) := by
  sorry


@[target] lemma koszulSignInsert_cons (r0 r1 : 𝓕) (r : List 𝓕) :
    koszulSignInsert q le r0 (r1 :: r) = (koszulSignCons q le r0 r1) *
    koszulSignInsert q le r0 r := by
  sorry


@[target] lemma koszulSignInsert_of_le_mem (φ0 : 𝓕) : (φs : List 𝓕) → (h : ∀ b ∈ φs, le φ0 b) →
    koszulSignInsert q le φ0 φs = 1
  | [], _ => by
    sorry


@[target] lemma koszulSignInsert_eq_rel_eq_stat {ψ φ : 𝓕} [IsTrans 𝓕 le]
    (h1 : le φ ψ) (h2 : le ψ φ) (hq : q ψ = q φ) : (φs : List 𝓕) →
    koszulSignInsert q le φ φs = koszulSignInsert q le ψ φs
  | [] => by
    sorry


lemma koszulSignInsert_eq_remove_same_stat_append {ψ φ φ' : 𝓕} [IsTrans 𝓕 le]
    (h1 : le φ ψ) (h2 : le ψ φ) (hq : q ψ = q φ) : (φs : List 𝓕) →
    koszulSignInsert q le φ' (φ :: ψ :: φs) = koszulSignInsert q le φ' φs := by
  intro φs
  simp_all only [koszulSignInsert, and_self, ite_true, ite_false, ite_self]
  by_cases hφ'φ : le φ' φ
  · have hφ'ψ : le φ' ψ := by
      apply IsTrans.trans φ' φ ψ hφ'φ h1
    simp [hφ'φ, hφ'ψ]
  · have hφ'ψ : ¬ le φ' ψ := by
      intro hφ'ψ
      apply hφ'φ
      apply IsTrans.trans φ' ψ φ hφ'ψ h2
    simp_all

end Wick
