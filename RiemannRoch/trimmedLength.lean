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
theorem Module.length_ge_trimmedLength
(rs : RelSeries (α := Submodule R M) (· ≤ ·))
  : RelSeries.trimmedLength rs ≤ Module.length R M := by
  rw[← rs.length_trim]
  rw[Module.length, krullDim]
  exact le_iSup_iff.mpr fun b a ↦ a rs.trim



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
  · have h₁ : i + 1 ≤ j := by exact Fin.add_one_le_of_lt hij'
    contrapose! hij
    apply ne_of_lt
    apply lt_of_lt_of_le _ (RelSeries.map_le rs h₁)
    apply lt_of_le_of_ne
    · apply RelSeries.map_le
      by_contra! h
      have h' : i+1 ≤ i := h.le

      have h'' : i = Fin.last rs.length := (Fin.add_one_le_iff.mp h')
      exact Fin.ne_last_of_lt hij' h''

    · apply hrs
  · rfl
  · have h₁ : j + 1 ≤ i := by exact Fin.add_one_le_of_lt hij'
    contrapose! hij
    apply ne_of_gt
    apply lt_of_lt_of_le _ (RelSeries.map_le rs h₁)
    apply lt_of_le_of_ne
    · apply RelSeries.map_le
      by_contra! h
      have h' : j+1 ≤ j := h.le
      have h'' : j = Fin.last rs.length := (Fin.add_one_le_iff.mp h')
      exact Fin.ne_last_of_lt hij' h''
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
    simp[RelSeries.trimmedLength]
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
   · by_cases h : j = rs.length
     · exact rs.step j
     · have : j.val < rs.length := by exact j.isLt
       let j' : Fin rs.length := ⟨j, this⟩
       have pf := rs.step j'
       simp_all
   · exact hrs j
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
    simp at hrs'
    convert hrs'.symm
    exact?
    · apply Fin.eq_of_val_eq
      simp only [Fin.coe_castSucc, ipred, Fin.coe_pred]
      aesop



omit [DecidableRel (α := α) (· ≤ ·)] in
variable {rs} in
/--
If the last two elements of rs are equal, then rs.trimmedLength = rs.eraseLast.trimmedLength. Note
that if rs only has one element, the "last two elements" are both just the unique element of rs.
-/
theorem RelSeries.trimmedLength_eraseLast_of_eq
  (lasteq : ∃ i : Fin (rs.length), rs.toFun (i.succ) = rs.toFun i.castSucc ∧ (i + 1:ℕ) = rs.length)
  : rs.trimmedLength = rs.eraseLast.trimmedLength := by
    simp[RelSeries.trimmedLength]
    congr 2
    have foo : (Finset.univ : Finset (Fin (rs.length + 1))) =
               Finset.image (Fin.castLE (n := rs.length - 1 + 1)
               (by omega)) Finset.univ ∪ {Fin.last _} := by

      have finrange := Fin.range_castLE (n := rs.length - 1 + 1) (k := rs.length + 1) (by omega)
      suffices m : (Finset.univ : Finset (Fin (rs.length + 1))) =
               {i : Fin (rs.length + 1) | ↑i < rs.length} ∪ {Fin.last rs.length} by
        simp_all
        ext a
        simp[Finset.eq_univ_iff_forall]
        by_cases ha : a = Fin.last rs.length
        · exact Or.inr ha
        · apply Or.inl
          have ha2 : a.val < rs.length - 1 + 1 := by
            have ha3 : a.val < rs.length + 1 := a.2
            have : a.val ≠ rs.length := by
              rw[← Fin.val_eq_val] at ha
              exact ha
            omega

          let a' : Fin (rs.length - 1 + 1) := ⟨a, ha2⟩
          use a'
          apply Fin.eq_of_val_eq
          simp
      simp only [Finset.coe_univ, Set.union_singleton]
      unfold Set.univ
      ext a
      constructor
      · intro
        refine Set.mem_insert_iff.mpr ?h.mp.a
        by_cases h : a = Fin.last rs.length
        · exact Or.inl h
        · simp_all only [Fin.range_castLE, Finset.coe_image, Finset.coe_univ, Set.image_univ,
            Set.setOf_true, Set.mem_univ, Set.mem_setOf_eq, false_or]
          exact Fin.val_lt_last h
      · aesop

    rw[foo, Finset.image_union, Finset.image_singleton, Finset.image_image, Finset.union_eq_left.mpr]
    · rfl
    · simp
      obtain ⟨i, hi⟩ := lasteq
      let i' : Fin (rs.length - 1 + 1) := ⟨i, by omega⟩

      use i
      have : (Fin.castLE (n := rs.length - 1 + 1) (by omega) ↑↑i) = i.castSucc := by
        apply Fin.eq_of_val_eq
        simp only [Fin.coe_castLE, Fin.val_natCast, Fin.coe_castSucc, Nat.mod_succ_eq_iff_lt,
          Nat.succ_eq_add_one]
        omega
      rw[this]
      have : Fin.last rs.length = i.succ := by aesop

      rw[this]
      exact hi.1.symm

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
      have foo : (Finset.univ : Finset (Fin (rs.length + 1))) =
               Finset.image (Fin.castLE (n := rs.length - 1 + 1) (by omega))
               Finset.univ ∪ {Fin.last _} := by
        suffices m : (Finset.univ : Finset (Fin (rs.length + 1))) =
               {i : Fin (rs.length + 1) | ↑i < rs.length} ∪ {Fin.last rs.length} by
          simp_all only [Finset.coe_univ, Set.union_singleton]
          ext a
          simp[Finset.eq_univ_iff_forall]
          by_cases ha : a = Fin.last rs.length
          · exact Or.inr ha
          · apply Or.inl
            have ha2 : a.val < rs.length - 1 + 1 := by
              have ha3 : a.val < rs.length + 1 := a.2
              have : a.val ≠ rs.length := by
                rw[← Fin.val_eq_val] at ha
                exact ha
              omega

            let a' : Fin (rs.length - 1 + 1) := ⟨a, ha2⟩
            use a'
            apply Fin.eq_of_val_eq
            simp
        simp only [Finset.coe_univ, Set.union_singleton]
        unfold Set.univ
        ext a
        constructor
        · intro
          refine Set.mem_insert_iff.mpr ?h.mp.a
          by_cases h : a = Fin.last rs.length
          · exact Or.inl h
          · simp_all only [Fin.range_castLE, Finset.coe_image, Finset.coe_univ, Set.image_univ,
            Set.setOf_true, Set.mem_univ, Set.mem_setOf_eq, false_or]
            exact Fin.val_lt_last h
        · aesop
      rw[foo, Finset.image_union, Finset.image_singleton, Finset.image_image]
      clear foo
      rw[Finset.card_union_of_disjoint, Finset.card_singleton]
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
    by_cases h : ∃ i : Fin rs.length, rs.toFun i.succ = rs.toFun i.castSucc ∧ ↑i + 1 = rs.length
    · have := rs.trimmedLength_eraseLast_of_eq h
      exact Nat.le_of_eq (id (Eq.symm this))
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
