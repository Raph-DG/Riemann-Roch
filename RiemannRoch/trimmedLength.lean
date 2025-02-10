/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.Order.KrullDimension
import Mathlib.Order.JordanHolder
import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.FiniteLength
import Mathlib.Order.ConditionallyCompleteLattice.Group
import Mathlib.Order.Defs.Unbundled

/-!
# Trimmed Length

Given a relseries rs : RelSeries (· ≤ ·), we define the trimmed length of rs to be the cardinality
of the underlying function rs.toFun of rs minus 1. This models the number of `<` relations occuring
in rs.

## Notation

1. rs.trimmedLength denoted the trimmed length of rs as described above


## Theorems

The main theorem is given a short exact sequece

-/

open AlgebraicGeometry
open CategoryTheory
open Opposite.op
open Module
open Order
open Ring


variable {R : Type*}
          [Ring R]
          {M M' : Type*}
          [AddCommGroup M]
          [AddCommGroup M']
          [Module R M]
          [Module R M']


variable (R M) in
open Classical in
/--
The length of a module M is defined to be the supremum of lengths of chains of submodules of M. We
define this using the existing krull dimension api, and as a result this takes values in
WithBot ℕ∞ in spite of the fact that there is no module with length equal to ⊥.
-/
noncomputable
def Module.length : WithBot ℕ∞ := krullDim (α := Submodule R M)


variable {α : Type*} [PartialOrder α] [DecidableEq α]
  [DecidableRel (α := α) (· ≤ ·)] (rs : RelSeries (α := α) (· ≤ ·))

/--
Given (rs : RelSeries (α := α) (· ≤ ·)), rs.trimmedLength measures the number of `<`s appearing
in rs defined as the image of the underlying function of rs, rs.toFun.
-/
def RelSeries.trimmedLength (rs : RelSeries (α := α) (· ≤ ·)) : ℕ :=
  (Finset.image rs.toFun Finset.univ).card - 1


omit [DecidableEq α] [DecidableRel (α := α) (· ≤ ·)] [PartialOrder α] in
/--
Given a relseries rs : RelSeries (α := α) r with transitive and reflixive r, i ≤ j implies
r (rs i) (rs j)
-/
theorem RelSeries.map_le {r : Rel α α} [IsTrans α r] [IsRefl α r] (rs : RelSeries (α := α) r)
  {i j : Fin (rs.length + 1)}
  (hij : i ≤ j) : r (rs i) (rs j) := by
    have := rel_or_eq_of_le rs hij
    cases this
    · assumption
    · rename_i h
      rw[h]
      apply refl (r := r)

instance (rs : RelSeries (α := α) (· ≤ ·)) :
  LinearOrder { x // x ∈ Finset.image rs.toFun Finset.univ } where
    __ := Subtype.partialOrder _
    le_total := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      simp at ha hb
      obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      simp only [Subtype.mk_le_mk]
      apply (le_total i j).imp
      all_goals intro lt; exact RelSeries.map_le rs lt
    decidableLE := inferInstance

/--
Constructs LTSeries associated to a given RelSeries (α := α) (· ≤ ·) constructed by
taking only those places where the relation is not equality.
-/
def RelSeries.trim (rs : RelSeries (α := α) (· ≤ ·)) :
 RelSeries (α := α) (· < ·) where
   length := rs.trimmedLength
   toFun := by
    refine Subtype.val ∘ monoEquivOfFin (Finset.image rs.toFun Finset.univ) ?_
    simp[RelSeries.trimmedLength]
   step := by
    intro i
    simp

/--
The length of the rs.trim is equal to the trimmed length of rs.
-/
lemma RelSeries.length_trim (rs : RelSeries (α := α) (· ≤ ·)) :
  rs.trim.length = rs.trimmedLength := by
    simp[trim]

open Classical in
/--
The length of a module is greater than or equal to the trimmedLength of any
rs : RelSeries (α := Submodule R M) (· ≤ ·).
-/
theorem RelSeries.moduleLength_ge_trimmedLength
(rs : RelSeries (α := Submodule R M) (· ≤ ·))
  : RelSeries.trimmedLength rs ≤ Module.length R M := by
  rw[← rs.length_trim]
  rw[Module.length, krullDim]
  exact le_iSup_iff.mpr fun b a ↦ a rs.trim



lemma pairwiseToFull {α ι : Type*} [LinearOrder ι](tf : ι → α) : ∀ (i : ι),
  tf i = tf i := sorry

/-
This should almost certainly be rs i.castSucc = rs.succ, but it's more annoying to change
than I thought it would be and as it turns out this lemma is never used anywhere (it's good
to have for symmetry's sake though)
-/

variable {rs} in
omit [DecidableRel (α := α) (· ≤ ·)] in
theorem RelSeries.trimmedLength_exists_eq
(hrs : rs.length > rs.trimmedLength) : ∃ i, rs i = rs (i+1) := by
  contrapose! hrs
  suffices rs.toFun.Injective by
    have := Finset.card_le_card_of_injOn (s := .univ) (t := Finset.image rs.toFun Finset.univ)
      rs.toFun (by simp) this.injOn
    simp only [Finset.card_univ, Fintype.card_fin] at this
    simp only [trimmedLength, ge_iff_le]
    omega
  intro i j hij
  obtain hij'|rfl|hij' := lt_trichotomy i j
  · have h₁ : i + 1 ≤ j := Fin.add_one_le_of_lt hij'
    contrapose! hij
    apply ne_of_lt
    apply lt_of_lt_of_le _ (RelSeries.map_le rs h₁)
    apply lt_of_le_of_ne
    · apply RelSeries.map_le
      by_contra! h
      exact Fin.ne_last_of_lt hij' (Fin.add_one_le_iff.mp h.le)
    · apply hrs
  · rfl
  · have h₁ : j + 1 ≤ i := by exact Fin.add_one_le_of_lt hij'
    contrapose! hij
    apply ne_of_gt
    apply lt_of_lt_of_le _ (RelSeries.map_le rs h₁)
    apply lt_of_le_of_ne
    · apply RelSeries.map_le
      by_contra! h
      exact Fin.ne_last_of_lt hij' (Fin.add_one_le_iff.mp h.le)
    · apply hrs


omit [DecidableRel (α := α) (· ≤ ·)] in
variable {rs} in
/--
If rs has length greater than 0, there must be some index i such that rs i.castSucc < rs i.succ
-/
theorem RelSeries.trimmedLength_exists_le
(hrs : rs.trimmedLength > 0) : ∃ (i : Fin rs.length), rs i.castSucc < rs i.succ := by
  contrapose! hrs
  suffices ∀ i, rs i = rs 0 by
    unfold RelSeries.trimmedLength
    suffices Finset.image rs.toFun Finset.univ = {rs.toFun 0} by simp[this]
    suffices rs.toFun = fun i ↦ rs.toFun 0 by
      rw[this, Finset.image_const]
      use 0
      simp
    ext:1
    apply this
  intro i
  have hrs' : ∀ (i : Fin rs.length), rs.toFun i.castSucc = rs.toFun i.succ := by
   intro j
   apply eq_of_le_of_not_lt
   · exact rs.step j
   · exact hrs j
  /-
  This should be its own lemma, but to me its unclear what the lemma should be.
  Potentially just what it says there
  -/
  induction' o : i.val with n ih generalizing i
  · congr
    exact Eq.symm (Fin.eq_of_val_eq (id (Eq.symm o)))
  · specialize ih (i-1)
    have o' : Fin.val (i-1) = n := by
      have : n = ↑i - 1 := by omega
      rw[this]
      rw[Fin.coe_sub_one]
      simp only [ite_eq_right_iff]
      aesop
    specialize ih o'
    rw[← ih]
    let ipred := Fin.pred i (by aesop)
    specialize hrs' ipred
    simp only at hrs'
    convert hrs'.symm
    subst o'
    simp_all only [Fin.succ_pred, ipred]
    · apply Fin.eq_of_val_eq
      simp only [Fin.coe_castSucc, ipred, Fin.coe_pred]
      aesop


lemma Finset.univ_eq (n : ℕ) :
  (Finset.univ : Finset (Fin (n + 1))) = {i : Fin (n + 1) | ↑i < n} ∪ {Fin.last n} := by
  ext a
  simp
  by_cases ha : a = Fin.last n
  · exact Or.inl ha
  · exact Or.inr <| Fin.val_lt_last ha

lemma Finset.baz (n : ℕ) :(Finset.univ : Finset (Fin (n + 1))) =
    Finset.image (Fin.castLE (n := n - 1 + 1)
    (by omega)) Finset.univ ∪ {Fin.last _} := by
  suffices m : (Finset.univ : Finset (Fin (n + 1))) =
               {i : Fin (n + 1) | ↑i < n} ∪ {Fin.last n} by
    simp_all only [Finset.coe_univ, Set.union_singleton]
    ext a
    simp[Finset.eq_univ_iff_forall]
    by_cases ha : a = Fin.last n
    · exact Or.inr ha
    · apply Or.inl
      have ha2 : a.val < n - 1 + 1 := by
        have ha3 : a.val < n + 1 := a.2
        have : a.val ≠ n := by
          rw[← Fin.val_eq_val] at ha
          exact ha
        omega

      let a' : Fin (n - 1 + 1) := ⟨a, ha2⟩
      use a'
      apply Fin.eq_of_val_eq
      simp
  exact Finset.univ_eq n



omit [DecidableRel (α := α) (· ≤ ·)] in
variable {rs} in
/--
If the last two elements of rs are equal, then rs.trimmedLength = rs.eraseLast.trimmedLength. Note
that if rs only has one element, the "last two elements" are both just the unique element of rs.
-/
theorem RelSeries.trimmedLength_eraseLast_of_eq
  (lasteq : ∃ i : Fin (rs.length), rs.toFun i.castSucc = rs.toFun i.succ ∧ (i + 1:ℕ) = rs.length)
  : rs.trimmedLength = rs.eraseLast.trimmedLength := by
    simp only [trimmedLength, eraseLast_length]
    congr 2
    rw[Finset.baz, Finset.image_union, Finset.image_singleton,
     Finset.image_image, Finset.union_eq_left.mpr]
    · rfl
    · simp only [Finset.singleton_subset_iff, Finset.mem_image, Finset.mem_univ,
      Function.comp_apply, true_and]
      obtain ⟨i, hi⟩ := lasteq
      use i
      have : (Fin.castLE (n := rs.length - 1 + 1) (by omega) ↑↑i) = i.castSucc := by
        apply Fin.eq_of_val_eq
        simp only [Fin.coe_castLE, Fin.val_natCast, Fin.coe_castSucc, Nat.mod_succ_eq_iff_lt,
          Nat.succ_eq_add_one]
        omega
      rw[this]
      have : Fin.last rs.length = i.succ := by aesop
      rw[this]
      exact hi.1

omit [DecidableRel (α := α) (· ≤ ·)] in
variable {rs} in
/--
If the last two elements a, b of rs satisfy a < b, then
rs.trimmedLength = rs.eraseLast.trimmedLength. Note that if rs only has one element,
the "last two elements" are both just the unique element of rs.
In this case the condition is vacuous.
-/
theorem RelSeries.trimmedLength_eraseLast_of_lt
    (lastlt : ∃ i : Fin (rs.length), rs i.castSucc < rs i.succ ∧ (i + 1:ℕ) = rs.length)
    : rs.trimmedLength = rs.eraseLast.trimmedLength + 1 := by
      simp only [trimmedLength, eraseLast_length, Finset.one_le_card, Finset.image_nonempty,
        Finset.univ_nonempty, Nat.sub_add_cancel]
      rw[Finset.baz, Finset.image_union, Finset.image_singleton,
        Finset.image_image, Finset.card_union_of_disjoint, Finset.card_singleton]
      · rfl
      · simp
        intro i
        apply ne_of_lt
        obtain ⟨j, hj⟩ := lastlt
        have h₂ : rs (@Fin.castLE (rs.length - 1 + 1) (rs.length + 1) (by omega) i) ≤
                  rs j.castSucc := by
          apply RelSeries.map_le
          have := i.2
          apply Fin.mk_le_of_le_val
          have : i.val ≤ rs.length - 1  := by omega
          apply le_trans (b := rs.length - 1)
          exact this

          have : ↑(j.castSucc) = rs.length - 1 := by
            have := hj.2
            have fact : j.val = j.castSucc.val := by exact rfl
            rw[← fact]
            omega
          rw[this]

        apply lt_of_le_of_lt (b := rs j.castSucc)
        exact h₂
        have : j.succ = Fin.last rs.length := by aesop
        rw[← this]
        exact hj.1


omit [DecidableRel (α := α) (· ≤ ·)] in
/--
The trimmed length of rs.eraseLast is less than or equal to the trimmed length of rs
-/
theorem RelSeries.trimmedLength_eraseLast_le :
  rs.eraseLast.trimmedLength ≤ rs.trimmedLength := by
    by_cases h : ∃ i : Fin rs.length, rs.toFun i.castSucc = rs.toFun i.succ ∧ ↑i + 1 = rs.length
    · exact Nat.le_of_eq (id (Eq.symm (rs.trimmedLength_eraseLast_of_eq h)))
    · by_cases nontriv : rs.length = 0
      · simp_all only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, exists_false,
        not_false_eq_true]
        have : rs.eraseLast = rs := by aesop
        exact Nat.le_of_eq (congrArg trimmedLength this)
      have : ∃ i : Fin rs.length, rs.toFun i.castSucc < rs.toFun i.succ ∧ ↑i + 1 = rs.length := by
        simp_all only [not_exists, not_and]
        let secondlast : Fin rs.length := ⟨rs.length - 1, by omega⟩
        use secondlast
        specialize h secondlast
        have neq : rs secondlast.succ ≠ rs secondlast.castSucc := by
          contrapose h
          simp_all only [ne_eq, Decidable.not_not, forall_const]
          omega
        have := rs.step secondlast
        constructor
        · apply lt_of_le_of_ne
          · exact this
          · exact id (Ne.symm neq)
        · exact Nat.succ_pred_eq_of_ne_zero nontriv
      have := rs.trimmedLength_eraseLast_of_lt this
      omega
