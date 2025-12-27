import VerifiedAgora.tagger
/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.PerturbationTheory.Koszul.KoszulSignInsert
import PhysLean.Mathematics.List.InsertionSort
/-!

# Koszul sign

-/

namespace Wick

open PhysLean.List
open FieldStatistic

variable {𝓕 : Type} (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le]

/-- Gives a factor of `- 1` for every fermion-fermion (`q` is `1`) crossing that occurs when sorting
  a list of based on `r`. -/
def koszulSign (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le] :
    List 𝓕 → ℂ
  | [] => 1
  | a :: l => koszulSignInsert q le a l * koszulSign q le l

@[target] lemma koszulSign_singleton (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le] (φ : 𝓕) :
    koszulSign q le [φ] = 1 := by
  sorry


lemma koszulSign_mul_self (l : List 𝓕) : koszulSign q le l * koszulSign q le l = 1 := by
  induction l with
  | nil => simp [koszulSign]
  | cons a l ih =>
    simp only [koszulSign]
    trans (koszulSignInsert q le a l * koszulSignInsert q le a l) *
      (koszulSign q le l * koszulSign q le l)
    · ring
    · rw [ih, koszulSignInsert_mul_self, mul_one]

@[target] lemma koszulSign_freeMonoid_of (φ : 𝓕) : koszulSign q le (FreeMonoid.of φ) = 1 := by
  sorry


@[target] lemma koszulSignInsert_erase_boson {𝓕 : Type} (q : 𝓕 → FieldStatistic)
    (le : 𝓕 → 𝓕 → Prop) [DecidableRel le] (φ : 𝓕) :
    (φs : List 𝓕) → (n : Fin φs.length) → (heq : q (φs.get n) = bosonic) →
    koszulSignInsert q le φ (φs.eraseIdx n) = koszulSignInsert q le φ φs
  | [], _, _ => by
    sorry


@[target] lemma koszulSign_erase_boson {𝓕 : Type} (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop)
    [DecidableRel le] :
    (φs : List 𝓕) → (n : Fin φs.length) → (heq : q (φs.get n) = bosonic) →
    koszulSign q le (φs.eraseIdx n) = koszulSign q le φs
  | [], _ => by
    sorry


lemma koszulSign_insertIdx [IsTotal 𝓕 le] [IsTrans 𝓕 le] (φ : 𝓕) :
    (φs : List 𝓕) → (n : ℕ) → (hn : n ≤ φs.length) →
    koszulSign q le (List.insertIdx φs n φ) = 𝓢(q φ, ofList q (φs.take n)) * koszulSign q le φs *
      𝓢(q φ, ofList q ((List.insertionSort le (List.insertIdx φs n φ)).take
      (insertionSortEquiv le (List.insertIdx φs n φ) ⟨n, by
        rw [List.length_insertIdx]
        simp only [hn, ↓reduceIte]
        omega⟩)))
  | [], 0, h => by
    simp [koszulSign]
  | [], n + 1, h => by
    simp at h
  | φ1 :: φs, 0, h => by
    simp only [List.insertIdx_zero, List.insertionSort_cons, List.length_cons, Fin.zero_eta]
    rw [koszulSign]
    trans koszulSign q le (φ1 :: φs) * koszulSignInsert q le φ (φ1 :: φs)
    · ring
    simp only [insertionSortEquiv, List.length_cons, Nat.succ_eq_add_one, orderedInsertEquiv,
      PhysLean.Fin.equivCons_trans, Equiv.trans_apply, PhysLean.Fin.equivCons_zero]
    conv_rhs =>
      enter [2,2, 2, 2]
      rw [orderedInsert_eq_insertIdx_orderedInsertPos]
    conv_rhs =>
      rhs
      erw [← ofList_take_insert]
      change 𝓢(q φ, ofList q ((List.insertionSort le (φ1 :: φs)).take
        (↑(orderedInsertPos le ((List.insertionSort le (φ1 :: φs))) φ))))
      rw [← koszulSignInsert_eq_exchangeSign_take q le]
    rw [ofList_take_zero]
    simp
  | φ1 :: φs, n + 1, h => by
    conv_lhs =>
      rw [List.insertIdx_succ_cons]
      rw [koszulSign]
    rw [koszulSign_insertIdx _ _ _ (Nat.le_of_lt_succ h)]
    conv_rhs =>
      rhs
      simp only [List.insertIdx_succ_cons]
      simp only [List.insertionSort_cons, List.length_cons, insertionSortEquiv, Nat.succ_eq_add_one,
        Equiv.trans_apply, PhysLean.Fin.equivCons_succ]
      erw [orderedInsertEquiv_fin_succ]
      simp only [Fin.eta, Fin.coe_cast]
      rhs
      simp [orderedInsert_eq_insertIdx_orderedInsertPos]
    conv_rhs =>
      lhs
      rw [ofList_take_succ_cons, map_mul, koszulSign]
    ring_nf
    conv_lhs =>
      lhs
      rw [mul_assoc, mul_comm]
    rw [mul_assoc]
    conv_rhs =>
      rw [mul_assoc, mul_assoc]
    congr 1
    let rs := (List.insertionSort le (List.insertIdx φs n φ))
    have hnsL : n < (List.insertIdx φs n φ).length := by
      rw [List.length_insertIdx]
      simp only [List.length_cons, add_le_add_iff_right] at h
      simp only [h, ↓reduceIte]
      omega
    let ni : Fin rs.length := (insertionSortEquiv le (List.insertIdx φs n φ))
      ⟨n, hnsL⟩
    let nro : Fin (rs.length + 1) :=
      ⟨↑(orderedInsertPos le rs φ1), orderedInsertPos_lt_length le rs φ1⟩
    rw [koszulSignInsert_insertIdx _ _ _ _ _ _ (Nat.le_of_lt_succ h), koszulSignInsert_cons]
    trans koszulSignInsert q le φ1 φs * (koszulSignCons q le φ1 φ *
      𝓢(q φ, ofList q (rs.take ni)))
    · simp only [rs, ni]
      ring
    trans koszulSignInsert q le φ1 φs * (𝓢(q φ, q φ1) *
          𝓢(q φ, ofList q ((List.insertIdx rs nro φ1).take (nro.succAbove ni))))
    swap
    · simp only [rs, nro, ni]
      ring
    congr 1
    simp only [Fin.succAbove]
    have hns : rs.get ni = φ := by
      simp only [rs]
      rw [← insertionSortEquiv_get]
      simp only [Function.comp_apply, Equiv.symm_apply_apply, List.get_eq_getElem, ni]
      simp_all only [List.length_cons, add_le_add_iff_right, List.getElem_insertIdx_self]
    have hc1 (hninro : ni.castSucc < nro) : ¬ le φ1 φ := by
      rw [← hns]
      exact lt_orderedInsertPos_rel le φ1 rs ni hninro
    have hc2 (hninro : ¬ ni.castSucc < nro) : le φ1 φ := by
      rw [← hns]
      refine gt_orderedInsertPos_rel le φ1 rs ?_ ni hninro
      exact List.pairwise_insertionSort le (List.insertIdx φs n φ)
    by_cases hn : ni.castSucc < nro
    · simp only [hn, ↓reduceIte, Fin.coe_castSucc]
      rw [ofList_take_insertIdx_gt]
      swap
      · exact hn
      congr 1
      rw [koszulSignCons_eq_exchangeSign]
      simp only [hc1 hn, ↓reduceIte]
      rw [exchangeSign_symm]
    · simp only [hn, ↓reduceIte, Fin.val_succ]
      rw [ofList_take_insertIdx_le, map_mul, ← mul_assoc]
      · congr 1
        rw [exchangeSign_mul_self, koszulSignCons]
        simp only [hc2 hn, ↓reduceIte]
      · exact Nat.le_of_not_lt hn
      · exact Nat.le_of_lt_succ (orderedInsertPos_lt_length le rs φ1)

@[target] lemma insertIdx_eraseIdx {I : Type} : (n : ℕ) → (r : List I) → (hn : n < r.length) →
    List.insertIdx n (r.get ⟨n, hn⟩) (r.eraseIdx n) = r
  | n, [], hn => by
    sorry


@[target] lemma koszulSign_eraseIdx [IsTotal 𝓕 le] [IsTrans 𝓕 le] (φs : List 𝓕) (n : Fin φs.length) :
    koszulSign q le (φs.eraseIdx n) = koszulSign q le φs * 𝓢(q (φs.get n), ofList q (φs.take n)) *
    𝓢(q (φs.get n), ofList q (List.take (↑(insertionSortEquiv le φs n))
    (List.insertionSort le φs))) := by
  sorry


@[target] lemma koszulSign_eraseIdx_insertionSortMinPos [IsTotal 𝓕 le] [IsTrans 𝓕 le] (φ : 𝓕) (φs : List 𝓕) :
    koszulSign q le ((φ :: φs).eraseIdx (insertionSortMinPos le φ φs)) = koszulSign q le (φ :: φs)
    * 𝓢(q (insertionSortMin le φ φs), ofList q ((φ :: φs).take (insertionSortMinPos le φ φs))) := by
  sorry


@[target] lemma koszulSign_swap_eq_rel_cons {ψ φ : 𝓕}
    (h1 : le φ ψ) (h2 : le ψ φ) (φs' : List 𝓕) :
    koszulSign q le (φ :: ψ :: φs') = koszulSign q le (ψ :: φ :: φs') := by
  sorry


@[target] lemma koszulSign_swap_eq_rel {ψ φ : 𝓕} (h1 : le φ ψ) (h2 : le ψ φ) : (φs φs' : List 𝓕) →
    koszulSign q le (φs ++ φ :: ψ :: φs') = koszulSign q le (φs ++ ψ :: φ :: φs')
  | [], φs' => by
    sorry


@[target] lemma koszulSign_eq_rel_eq_stat_append {ψ φ : 𝓕} [IsTrans 𝓕 le]
    (h1 : le φ ψ) (h2 : le ψ φ) (hq : q ψ = q φ) : (φs : List 𝓕) →
    koszulSign q le (φ :: ψ :: φs) = koszulSign q le φs := by
  sorry


@[target] lemma koszulSign_eq_rel_eq_stat {ψ φ : 𝓕} [IsTrans 𝓕 le]
    (h1 : le φ ψ) (h2 : le ψ φ) (hq : q ψ = q φ) : (φs' φs : List 𝓕) →
    koszulSign q le (φs' ++ φ :: ψ :: φs) = koszulSign q le (φs' ++ φs)
  | [], φs => by
    sorry


@[target] lemma koszulSign_of_sorted : (φs : List 𝓕)
    → (hs : List.Sorted le φs) → koszulSign q le φs = 1
  | [], _ => by
    sorry


@[target] lemma koszulSign_of_insertionSort [IsTotal 𝓕 le] [IsTrans 𝓕 le] (φs : List 𝓕) :
    koszulSign q le (List.insertionSort le φs) = 1 := by
  sorry


@[target] lemma koszulSign_of_append_eq_insertionSort_left [IsTotal 𝓕 le] [IsTrans 𝓕 le] :
    (φs φs' : List 𝓕) → koszulSign q le (φs ++ φs') =
    koszulSign q le (List.insertionSort le φs ++ φs') * koszulSign q le φs
  | φs, [] => by
    sorry


@[target] lemma koszulSign_of_append_eq_insertionSort [IsTotal 𝓕 le] [IsTrans 𝓕 le] : (φs'' φs φs' : List 𝓕) →
    koszulSign q le (φs'' ++ φs ++ φs') =
    koszulSign q le (φs'' ++ List.insertionSort le φs ++ φs') * koszulSign q le φs
  | [], φs, φs'=> by
    sorry


@[target] lemma koszulSign_perm_eq_append [IsTrans 𝓕 le] (φ : 𝓕) (φs φs' φs2 : List 𝓕)
    (hp : φs.Perm φs') : (h : ∀ φ' ∈ φs, le φ φ' ∧ le φ' φ) →
    koszulSign q le (φs ++ φs2) = koszulSign q le (φs' ++ φs2) := by
  sorry


@[target] lemma koszulSign_perm_eq [IsTrans 𝓕 le] (φ : 𝓕) : (φs1 φs φs' φs2 : List 𝓕) →
    (h : ∀ φ' ∈ φs, le φ φ' ∧ le φ' φ) → (hp : φs.Perm φs') →
    koszulSign q le (φs1 ++ φs ++ φs2) = koszulSign q le (φs1 ++ φs' ++ φs2)
  | [], φs, φs', φs2, h, hp => by
    sorry


end Wick
