import VerifiedAgora.tagger
/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.PerturbationTheory.FieldSpecification.Basic
/-!

# Wick contractions

-/
open FieldSpecification

variable {𝓕 : FieldSpecification}

/--
Given a natural number `n`, which will correspond to the number of fields needing
contracting, a Wick contraction
is a finite set of pairs of `Fin n` (numbers `0`, ..., `n-1`), such that no
element of `Fin n` occurs in more than one pair. The pairs are the positions of fields we
'contract' together.
-/
/--
Given a natural number `n`, which will correspond to the number of fields needing
contracting, a Wick contraction
is a finite set of pairs of `Fin n` (numbers `0`, …, `n-1`), such that no
element of `Fin n` occurs in more then one pair. The pairs are the positions of fields we
'contract' together.
-/
def WickContraction (n : ℕ) : Type := by sorry


namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open PhysLean.List

/-- Wick contractions are decidable. -/
instance : DecidableEq (WickContraction n) := Subtype.instDecidableEq

/-- The contraction consisting of no contracted pairs. -/
/-- The contraction consisting of no contracted pairs. -/
def empty : WickContraction n := ⟨∅, by sorry


@[target] lemma card_zero_iff_empty (c : WickContraction n) : c.1.card = 0 ↔ c = empty := by
  sorry


@[target] lemma exists_pair_of_not_eq_empty (c : WickContraction n) (h : c ≠ empty) :
    ∃ i j, {i, j} ∈ c.1 := by
  sorry


/-- The equivalence between `WickContraction n` and `WickContraction m`
  derived from a propositional equality of `n` and `m`. -/
def congr : {n m : ℕ} → (h : n = m) → WickContraction n ≃ WickContraction m
  | n, .(n), rfl => Equiv.refl _

@[target] lemma congr_refl : c.congr rfl = c := by
  sorry


@[target] lemma card_congr {n m : ℕ} (h : n = m) (c : WickContraction n) :
    (congr h c).1.card = c.1.card := by
  sorry


lemma congr_contractions {n m : ℕ} (h : n = m) (c : WickContraction n) :
    ((congr h) c).1 = Finset.map (Finset.mapEmbedding (finCongr h)).toEmbedding c.1 := by
  subst h
  simp only [congr_refl, Finset.le_eq_subset, finCongr_refl, Equiv.refl_toEmbedding]
  ext a
  apply Iff.intro <;> intro ha
  · simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding]
    use a
    simp only [ha, true_and]
    rw [Finset.mapEmbedding_apply, Finset.map_refl]
  · simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding] at ha
    obtain ⟨b, hb, hab⟩ := ha
    rw [Finset.mapEmbedding_apply, Finset.map_refl] at hab
    subst hab
    exact hb

@[target] lemma congr_trans {n m o : ℕ} (h1 : n = m) (h2 : m = o) :
    (congr h1).trans (congr h2) = congr (h1.trans h2) := by
  sorry


@[simp]
lemma congr_trans_apply {n m o : ℕ} (h1 : n = m) (h2 : m = o) (c : WickContraction n) :
    (congr h2) ((congr h1) c) = congr (h1.trans h2) c := by
  subst h1 h2
  simp

@[target] lemma mem_congr_iff {n m : ℕ} (h : n = m) {c : WickContraction n } {a : Finset (Fin m)} :
    a ∈ (congr h c).1 ↔ Finset.map (finCongr h.symm).toEmbedding a ∈ c.1 := by
  sorry


/-- Given a contracted pair in `c : WickContraction n` the contracted pair
  in `congr h c`. -/
/-- Given a contracted pair in `c : WickContraction n` the contracted pair
  in `congr h c`. -/
def congrLift {n m : ℕ} (h : n = m) {c : WickContraction n} (a : c.1) : (congr h c).1 :=
  ⟨a.1.map (finCongr h).toEmbedding, by
    sorry


@[simp]
lemma congrLift_rfl {n : ℕ} {c : WickContraction n} :
    c.congrLift rfl = id := by
  funext a
  simp [congrLift]

lemma congrLift_injective {n m : ℕ} {c : WickContraction n} (h : n = m) :
    Function.Injective (c.congrLift h) := by
  subst h
  simp only [congrLift_rfl]
  exact fun ⦃a₁ a₂⦄ a => a

@[target] lemma congrLift_surjective {n m : ℕ} {c : WickContraction n} (h : n = m) :
    Function.Surjective (c.congrLift h) := by
  sorry


@[target] lemma congrLift_bijective {n m : ℕ} {c : WickContraction n} (h : n = m) :
    Function.Bijective (c.congrLift h) := by
  sorry


/-- Given a contracted pair in `c : WickContraction n` the contracted pair
  in `congr h c`. -/
/-- Given a contracted pair in `c : WickContraction n` the contracted pair
  in `congr h c`. -/
def congrLiftInv {n m : ℕ} (h : n = m) {c : WickContraction n} (a : (congr h c).1) : c.1 :=
  ⟨a.1.map (finCongr h.symm).toEmbedding, by
    sorry


lemma congrLiftInv_rfl {n : ℕ} {c : WickContraction n} :
    c.congrLiftInv rfl = id := by
  funext a
  simp [congrLiftInv]

@[target] lemma eq_filter_mem_self : c.1 = Finset.filter (fun x => x ∈ c.1) Finset.univ := by
  sorry


/-- For a contraction `c : WickContraction n` and `i : Fin n` the `j` such that
  `{i, j}` is a contracted pair in `c`. If such an `j` does not exist, this returns `none`. -/
def getDual? (i : Fin n) : Option (Fin n) := Fin.find? (fun j => {i, j} ∈ c.1)

lemma getDual?_congr {n m : ℕ} (h : n = m) (c : WickContraction n) (i : Fin m) :
    (congr h c).getDual? i = Option.map (finCongr h) (c.getDual? (finCongr h.symm i)) := by
  subst h
  simp

lemma getDual?_congr_get {n m : ℕ} (h : n = m) (c : WickContraction n) (i : Fin m)
    (hg : ((congr h c).getDual? i).isSome) :
    ((congr h c).getDual? i).get hg =
    (finCongr h ((c.getDual? (finCongr h.symm i)).get (by simpa [getDual?_congr] using hg))) := by
  simp only [getDual?_congr, finCongr_apply]
  exact Option.get_map

lemma getDual?_eq_some_iff_mem (i j : Fin n) :
    c.getDual? i = some j ↔ {i, j} ∈ c.1 := by
  simp only [getDual?]
  rw [Fin.find?_eq_some_iff]
  apply Iff.intro <;> intro h
  · simpa using h.1
  · simp [h, true_and]
    intro k hkj hk
    have hc := c.2.2 _ h _ hk
    simp only [Finset.disjoint_insert_right, Finset.mem_insert, Finset.mem_singleton, true_or,
      not_true_eq_false, Finset.disjoint_singleton_right, not_or, false_and, or_false] at hc
    have hj : k ∈ ({i, j} : Finset (Fin n)) := by simp [hc]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with hj | hj
    · subst hj
      simp only [Finset.mem_singleton, Finset.insert_eq_of_mem] at hk
      have hc := c.2.1 _ hk
      simp at hc
    · subst hj
      simp at hkj

@[simp]
lemma getDual?_one_eq_none (c : WickContraction 1) (i : Fin 1) : c.getDual? i = none := by
  by_contra h
  have hn : (c.getDual? i).isSome := by
    rw [← Option.not_isSome_iff_eq_none] at h
    simpa [- Option.not_isSome, -Option.isNone_iff_eq_none] using h
  rw [@Option.isSome_iff_exists] at hn
  obtain ⟨a, hn⟩ := hn
  rw [getDual?_eq_some_iff_mem] at hn
  have hc := c.2.1 {i, a} hn
  fin_cases i
  fin_cases a
  simp at hc

@[simp]
lemma getDual?_get_self_mem (i : Fin n) (h : (c.getDual? i).isSome) :
    {(c.getDual? i).get h, i} ∈ c.1 := by
  rw [@Finset.pair_comm, ← getDual?_eq_some_iff_mem, Option.some_get]

@[simp]
lemma self_getDual?_get_mem (i : Fin n) (h : (c.getDual? i).isSome) :
    {i, (c.getDual? i).get h} ∈ c.1 := by
  rw [← getDual?_eq_some_iff_mem, Option.some_get]

lemma getDual?_eq_some_neq (i j : Fin n) (h : c.getDual? i = some j) :
    ¬ i = j := by
  rw [getDual?_eq_some_iff_mem] at h
  by_contra hn
  subst hn
  have hc := c.2.1 _ h
  simp at hc

@[simp]
lemma self_neq_getDual?_get (i : Fin n) (h : (c.getDual? i).isSome) :
    ¬ i = (c.getDual? i).get h := by
  by_contra hn
  have hx : {i, (c.getDual? i).get h} ∈ c.1 := by simp
  have hc := c.2.1 _ hx
  nth_rewrite 1 [hn] at hc
  simp at hc

@[simp]
lemma getDual?_get_self_neq (i : Fin n) (h : (c.getDual? i).isSome) :
    ¬ (c.getDual? i).get h = i := by
  by_contra hn
  have hx : {i, (c.getDual? i).get h} ∈ c.1 := by simp
  have hc := c.2.1 _ hx
  nth_rewrite 1 [hn] at hc
  simp at hc

lemma getDual?_isSome_iff (i : Fin n) : (c.getDual? i).isSome ↔ ∃ (a : c.1), i ∈ a.1 := by
  apply Iff.intro <;> intro h
  · rw [getDual?, Fin.isSome_find?_iff] at h
    obtain ⟨a, ha⟩ := h
    use ⟨{i, a}, by simpa using ha⟩
    simp
  · obtain ⟨a, ha⟩ := h
    have ha := c.2.1 a a.2
    rw [@Finset.card_eq_two] at ha
    obtain ⟨x, y, hx, hy⟩ := ha
    rw [hy] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    match ha with
    | Or.inl ha =>
      subst ha
      rw [getDual?, Fin.isSome_find?_iff]
      exact ⟨y, by simpa using hy ▸ a.2⟩
    | Or.inr ha =>
      subst ha
      rw [getDual?, Fin.isSome_find?_iff]
      use x
      rw [Finset.pair_comm]
      simpa using hy ▸ a.2

lemma getDual?_isSome_of_mem (a : c.1) (i : a.1) : (c.getDual? i).isSome := by
  rw [getDual?_isSome_iff]
  exact ⟨⟨a.1, a.2⟩, Finset.coe_mem ..⟩

@[simp]
lemma getDual?_getDual?_get_get (i : Fin n) (h : (c.getDual? i).isSome) :
    c.getDual? ((c.getDual? i).get h) = some i := by
  simp [getDual?_eq_some_iff_mem]

lemma getDual?_getDual?_get_isSome (i : Fin n) (h : (c.getDual? i).isSome) :
    (c.getDual? ((c.getDual? i).get h)).isSome := by
  simp

lemma getDual?_getDual?_get_not_none (i : Fin n) (h : (c.getDual? i).isSome) :
    ¬ (c.getDual? ((c.getDual? i).get h)) = none := by
  simp

/-!

## Extracting parts from a contraction.

-/

/-- The smallest of the two positions in a contracted pair given a Wick contraction. -/
/-- The smallest of the two positions in a contracted pair given a Wick contraction. -/
def fstFieldOfContract (c : WickContraction n) (a : c.1) : Fin n :=
  (a.1.sort (· ≤ ·)).head (by
    sorry


@[target] lemma fstFieldOfContract_congr {n m : ℕ} (h : n = m) (c : WickContraction n) (a : c.1) :
    (congr h c).fstFieldOfContract (c.congrLift h a) = (finCongr h) (c.fstFieldOfContract a) := by
  sorry


/-- The largest of the two positions in a contracted pair given a Wick contraction. -/
/-- The largest of the two positions in a contracted pair given a Wick contraction. -/
def sndFieldOfContract (c : WickContraction n) (a : c.1) : Fin n :=
  (a.1.sort (· ≤ ·)).tail.head (by
    sorry


@[target] lemma sndFieldOfContract_congr {n m : ℕ} (h : n = m) (c : WickContraction n) (a : c.1) :
    (congr h c).sndFieldOfContract (c.congrLift h a) = (finCongr h) (c.sndFieldOfContract a) := by
  sorry


@[target] lemma finset_eq_fstFieldOfContract_sndFieldOfContract (c : WickContraction n) (a : c.1) :
    a.1 = {c.fstFieldOfContract a, c.sndFieldOfContract a} := by
  sorry


@[target] lemma fstFieldOfContract_neq_sndFieldOfContract (c : WickContraction n) (a : c.1) :
    c.fstFieldOfContract a ≠ c.sndFieldOfContract a := by
  sorry


@[target] lemma fstFieldOfContract_le_sndFieldOfContract (c : WickContraction n) (a : c.1) :
    c.fstFieldOfContract a ≤ c.sndFieldOfContract a := by
  sorry


lemma fstFieldOfContract_lt_sndFieldOfContract (c : WickContraction n) (a : c.1) :
    c.fstFieldOfContract a < c.sndFieldOfContract a :=
  lt_of_le_of_ne (c.fstFieldOfContract_le_sndFieldOfContract a)
    (c.fstFieldOfContract_neq_sndFieldOfContract a)

@[target] lemma fstFieldOfContract_mem (c : WickContraction n) (a : c.1) :
    c.fstFieldOfContract a ∈ a.1 := by
  sorry


lemma fstFieldOfContract_getDual?_isSome (c : WickContraction n) (a : c.1) :
    (c.getDual? (c.fstFieldOfContract a)).isSome := by
  rw [getDual?_isSome_iff]
  exact ⟨a, fstFieldOfContract_mem ..⟩

@[simp]
lemma fstFieldOfContract_getDual? (c : WickContraction n) (a : c.1) :
    c.getDual? (c.fstFieldOfContract a) = some (c.sndFieldOfContract a) := by
  simp [getDual?_eq_some_iff_mem, ← finset_eq_fstFieldOfContract_sndFieldOfContract]

@[simp]
lemma sndFieldOfContract_mem (c : WickContraction n) (a : c.1) :
    c.sndFieldOfContract a ∈ a.1 := by
  simp [finset_eq_fstFieldOfContract_sndFieldOfContract]

lemma sndFieldOfContract_getDual?_isSome (c : WickContraction n) (a : c.1) :
    (c.getDual? (c.sndFieldOfContract a)).isSome := by
  rw [getDual?_isSome_iff]
  exact ⟨a, sndFieldOfContract_mem ..⟩

@[simp]
lemma sndFieldOfContract_getDual? (c : WickContraction n) (a : c.1) :
    c.getDual? (c.sndFieldOfContract a) = some (c.fstFieldOfContract a) := by
  rw [getDual?_eq_some_iff_mem, Finset.pair_comm, ← finset_eq_fstFieldOfContract_sndFieldOfContract]
  exact a.2

@[target] lemma eq_fstFieldOfContract_of_mem (c : WickContraction n) (a : c.1) (i j : Fin n)
    (hi : i ∈ a.1) (hj : j ∈ a.1) (hij : i < j) :
    c.fstFieldOfContract a = i := by
  sorry


@[target] lemma eq_sndFieldOfContract_of_mem (c : WickContraction n) (a : c.1) (i j : Fin n)
    (hi : i ∈ a.1) (hj : j ∈ a.1) (hij : i < j) :
    c.sndFieldOfContract a = j := by
  sorry


/-- As a type, any pair of contractions is equivalent to `Fin 2`
  with `0` being associated with `c.fstFieldOfContract a` and `1` being associated with
  `c.sndFieldOfContract`. -/
/-- As a type, any pair of contractions is equivalent to `Fin 2`
  with `0` being associated with `c.fstFieldOfContract a` and `1` being associated with
  `c.sndFieldOfContract`. -/
def contractEquivFinTwo (c : WickContraction n) (a : c.1) :
    a ≃ Fin 2 where
  toFun i := if i = c.fstFieldOfContract a then 0 else 1
  invFun i :=
    match i with
    | 0 => ⟨c.fstFieldOfContract a, fstFieldOfContract_mem c a⟩
    | 1 => ⟨c.sndFieldOfContract a, sndFieldOfContract_mem c a⟩
  left_inv i := by
    sorry


@[target] lemma prod_finset_eq_mul_fst_snd (c : WickContraction n) (a : c.1)
    (f : a.1 → M) [CommMonoid M] :
    ∏ (x : a), f x = f (⟨c.fstFieldOfContract a, fstFieldOfContract_mem c a⟩)
    * f (⟨c.sndFieldOfContract a, sndFieldOfContract_mem c a⟩) := by
  sorry


/-- For a field specification `𝓕`, `φs` a list of `𝓕.FieldOp` and a Wick contraction
  `φsΛ` of `φs`, the Wick contraction `φsΛ` is said to be `GradingCompliant` if
  for every pair in `φsΛ` the contracted fields are either both `fermionic` or both `bosonic`.
  In other words, in a `GradingCompliant` Wick contraction if
  no contracted pairs occur between `fermionic` and `bosonic` fields. -/
/-- For a field specification `𝓕`, `φs` a list of `𝓕.FieldOp` and a Wick contraction
  `φsΛ` of `φs`, the Wick contraction `φsΛ` is said to be `GradingCompliant` if
  for every pair in `φsΛ` the contracted fields are either both `fermionic` or both `bosonic`.
  In other words, in a `GradingCompliant` Wick contraction no contractions occur between
  `fermionic` and `bosonic` fields. -/
def GradingCompliant (φs : List 𝓕.FieldOp) (φsΛ : WickContraction φs.length) := by sorry


lemma gradingCompliant_congr {φs φs' : List 𝓕.FieldOp} (h : φs = φs')
    (φsΛ : WickContraction φs.length) :
    GradingCompliant φs φsΛ ↔ GradingCompliant φs' (congr (by simp [h]) φsΛ) := by
  subst h
  rfl

/-- An equivalence from the sigma type `(a : c.1) × a` to the subtype of `Fin n` consisting of
  those positions which are contracted. -/
/-- An equivalence from the sigma type `(a : c.1) × a` to the subtype of `Fin n` consisting of
  those positions which are contracted. -/
def sigmaContractedEquiv : (a : c.1) × a ≃ {x : Fin n // (c.getDual? x).isSome} where
  toFun := fun x => ⟨x.2, getDual?_isSome_of_mem c x.fst x.snd⟩
  invFun := fun x => ⟨
    ⟨{x.1, (c.getDual? x.1).get x.2}, self_getDual?_get_mem c (↑x) x.prop⟩,
    ⟨x.1, by sorry


end WickContraction
