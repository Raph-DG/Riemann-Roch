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
noncomputable
def Module.length := krullDim (α := Submodule R M)



-- Helper function for trimmed length which computes the number of <'s occuring in a leseries
open Classical in
private noncomputable
def go (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b)) (n : ℕ) : ℕ :=
  match n with
    | 0     => 0
    | (m+1) => if rs.toFun n = rs.toFun m then go rs m else 1 + go rs m

-- Length of an le series only counting steps which are not equality
--noncomputable
/-
def RelSeries.trimmed_length (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b)) : ℕ :=
  go rs rs.length
-/


--section trimmedLength
variable {α : Type*} [PartialOrder α] [DecidableEq α]
  [DecidableRel (α := α) (· ≤ ·)] (rs : RelSeries (α := α) (· ≤ ·))


def RelSeries.trimmed_length (rs : RelSeries (α := α) (· ≤ ·)) : ℕ :=
  (Finset.image rs.toFun Finset.univ).card - 1


omit [DecidableEq α] [DecidableRel (α := α) (· ≤ ·)] in
theorem RelSeries.map_le (rs : RelSeries (α := α) (· ≤ ·)) {i j : Fin (rs.length + 1)}
  (hij : i ≤ j) : rs i ≤ rs j := by
    have := rel_or_eq_of_le rs hij
    cases this
    · assumption
    · simp_all

instance (rs : RelSeries (α := α) (· ≤ ·)) :
  LinearOrder { x // x ∈ Finset.image rs.toFun Finset.univ } where
    __ := Subtype.partialOrder _
    le_total := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      simp at ha hb
      obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      simp
      apply (le_total i j).imp
      all_goals intro lt; exact RelSeries.map_le rs lt
    decidableLE := inferInstance


def RelSeries.trim (rs : RelSeries (α := α) (· ≤ ·)) :
 RelSeries (α := α) (· < ·) where
   length := rs.trimmed_length
   toFun := by
    refine Subtype.val ∘ monoEquivOfFin (Finset.image rs.toFun Finset.univ) ?_
    simp[RelSeries.trimmed_length]
   step := by
    intro i
    simp

lemma RelSeries.length_trim (rs : RelSeries (α := α) (· ≤ ·)) :
  rs.trim.length = rs.trimmed_length := by
    simp[trim]

open Classical in
theorem Module.length_ge_trimmed_length
(rs : RelSeries fun (a : Submodule R M) (b : Submodule R M) => a ≤ b)
  : RelSeries.trimmed_length rs ≤ Module.length R M := by
  rw[← rs.length_trim]
  rw[Module.length, krullDim]
  exact le_iSup_iff.mpr fun b a ↦ a rs.trim


open Classical in
theorem RelSeries.trimmed_length_exists_eq
{rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b)}
(hrs : rs.length > rs.trimmed_length) : ∃ i, rs.toFun i = rs.toFun (i+1) := by
  contrapose! hrs
  suffices rs.toFun.Injective by
    have := Finset.card_le_card_of_injOn (s := .univ) (t := Finset.image rs.toFun Finset.univ)
      rs.toFun (by simp) this.injOn
    simp at this
    simp[RelSeries.trimmed_length]
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

open Classical in
theorem RelSeries.trimmed_length_exists_le
{rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b)}
(hrs : rs.trimmed_length > 0) : ∃ (i : Fin rs.length), rs.toFun i.castSucc < rs.toFun i.succ := by
  contrapose! hrs
  suffices ∀ i, rs i = rs 0 by
    simp[RelSeries.trimmed_length]
    suffices Finset.image rs.toFun Finset.univ = {rs.toFun 0} by simp[this]
    suffices rs.toFun = fun i ↦ rs.toFun 0 by
      rw[this, Finset.image_const]
      use 0
      simp
    ext:1
    apply this
  intro i
  have hrs' : ∀ (i : Fin rs.length), rs.toFun i.castSucc = rs.toFun i.succ := by
   /-
   This ought to just be a rephrasing of hrs,
   -/
   intro j
   apply eq_of_le_of_not_lt
   · /-
      We again have this annoying wrap around problem, the point being that in here there's
      nothing stopping j from being rs.length. So, we want to split into two caes, when j is
      equal to rs.length and when it is not. It might
     -/
     by_cases h : j = rs.length
     · exact rs.step j

       /-specialize hrs j
       have : rs.toFun j = rs.toFun (j + 1) := by
        have : j+1 = 0 := by aesop
        rw[this] at hrs
        have : rs.toFun 0 ≤ rs.toFun j := by sorry

        have := rs.step
        sorry
       exact le_of_eq_of_le this fun ⦃x⦄ a ↦ a-/
     · have : j.val < rs.length := by exact j.isLt
       let j' : Fin rs.length := ⟨j, this⟩
       have pf := rs.step j'
       simp_all
   · exact hrs j
  induction' o : i.val with n ih generalizing i
  · congr
    exact Eq.symm (Fin.eq_of_val_eq (id (Eq.symm o)))
  · specialize ih (i-1)

    /-
    This I suspect will be a pain in the neck, but we'll see
    -/
    have o' : Fin.val (i-1) = n := by
      have : n = ↑i - 1 := by omega
      rw[this]
      rw[Fin.coe_sub_one]
      simp
      aesop

    specialize ih o'
    rw[← ih]
    let ipred := Fin.pred i (by aesop)
    specialize hrs' ipred
    simp at hrs'
    convert hrs'.symm
    exact?
    --exact Eq.symm (Fin.succ_pred i (sorryAx (i ≠ 0)))
    · apply Fin.eq_of_val_eq
      simp
      unfold ipred
      simp
      aesop
    --rw[hrs']
    --have : ((i - 1).castPred ).succ
    --exact hrs'.symm



/-
Note: the statements of these lemmas has some impact on how easily they'll be able to be proven.

These next two lemmas will at some point have compatible statements (I think whichever one I solve
first will win)
-/



open Classical in
theorem RelSeries.trimmed_length_eraseLast_of_eq
  {rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b)}
  (nontriv : rs.length > 0)
  (lasteq : ∃ i : Fin (rs.length), rs.toFun (i.succ) = rs.toFun i.castSucc ∧ (i + 1:ℕ) = rs.length) --i = Fin.last (rs.length - 1))--Fin.last (rs.length - 1))--i = Fin.castLE (n := rs.length - 1 + 1) (by omega) (Fin.last (rs.length - 1))) --(i + 1:ℕ) = rs.length)
  : rs.trimmed_length = rs.eraseLast.trimmed_length := by
    simp[RelSeries.trimmed_length]
    congr 2
    have foo : (Finset.univ : Finset (Fin (rs.length + 1))) =
               Finset.image (Fin.castLE (n := rs.length - 1 + 1) (by omega)) Finset.univ ∪ {Fin.last _} := by

      have finrange := Fin.range_castLE (n := rs.length - 1 + 1) (k := rs.length + 1) (by omega)
      have imeq : Finset.image (Fin.castLE (n := rs.length - 1 + 1) (m := rs.length + 1) (by omega)) Finset.univ
             = Set.range (Fin.castLE (n := rs.length - 1 + 1) (m := rs.length + 1) (by omega)) := by exact
               Fintype.coe_image_univ
      suffices m : (Finset.univ : Finset (Fin (rs.length + 1))) =
               {i : Fin (rs.length + 1) | ↑i < rs.length} ∪ {Fin.last rs.length} by
        simp_all
        ext a
        simp[Finset.eq_univ_iff_forall]
        by_cases ha : a = Fin.last rs.length
        · exact Or.inr ha
        · apply Or.inl
          have ha2 : a.val < rs.length - 1 + 1 := by
            simp_all
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
        · simp_all only [Fin.range_castLE, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.setOf_true,
            Set.mem_univ, Set.mem_setOf_eq, false_or]
          simp_all only [gt_iff_lt]
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
        simp
        omega
      rw[this]
      have : Fin.last rs.length = i.succ := by aesop

      rw[this]
      exact hi.1.symm



/-
Hmm, so I'm a little confused here. We've here used the simple minded approach for lastlt and it worked
So the question is, which one do we change?
-/
open Classical in
theorem RelSeries.trimmed_length_eraseLast_of_lt'
    {rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b)}
    (nontriv : rs.length > 0)
    (lastlt : rs.toFun (rs.length - 1) < rs.toFun (rs.length))
    : rs.trimmed_length = rs.eraseLast.trimmed_length + 1 := by
      simp[RelSeries.trimmed_length]
      have foo : (Finset.univ : Finset (Fin (rs.length + 1))) =
               Finset.image (Fin.castLE (n := rs.length - 1 + 1) (by omega)) Finset.univ ∪ {Fin.last _} := by
        suffices m : (Finset.univ : Finset (Fin (rs.length + 1))) =
               {i : Fin (rs.length + 1) | ↑i < rs.length} ∪ {Fin.last rs.length} by
          simp_all
          ext a
          simp[Finset.eq_univ_iff_forall]
          by_cases ha : a = Fin.last rs.length
          · exact Or.inr ha
          · apply Or.inl
            have ha2 : a.val < rs.length - 1 + 1 := by
              simp_all
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
          · simp_all only [Fin.range_castLE, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.setOf_true,
            Set.mem_univ, Set.mem_setOf_eq, false_or]
            simp_all only [gt_iff_lt]
            --obtain ⟨w, h_1⟩ := lasteq
            --obtain ⟨left, right⟩ := h_1
            exact Fin.val_lt_last h
        · aesop



      rw[foo, Finset.image_union, Finset.image_singleton, Finset.image_image]--, Finset.union_eq_left.mpr]
      clear foo
      rw[Finset.card_union_of_disjoint, Finset.card_singleton]
      · rfl
      · simp
        intro i
        apply ne_of_lt
        simp_all
        --#check @Fin.castLE (rs.length - 1 + 1) (rs.length + 1) (by omega) i
        have h₂ : rs (@Fin.castLE (rs.length - 1 + 1) (rs.length + 1) (by omega) i) ≤
                  rs (Fin.last rs.length - 1) := by
          apply RelSeries.map_le
          have := i.2
          apply Fin.mk_le_of_le_val
          have : i.val ≤ rs.length - 1  := by omega
          apply le_trans (b := rs.length - 1)
          exact this

          have : ↑(Fin.last rs.length - 1) = rs.length - 1 := by
            rw[Fin.coe_sub_one]
            aesop

          rw[this]

          -- Know i < rs.length, so we should know that
          --apply le_of_lt_succ
        --have h : @Fin.castLE (rs.length - 1 + 1) (rs.length + 1) =  :=
        apply lt_of_le_of_lt (b := rs.toFun (Fin.last rs.length - 1))
        exact h₂
        exact lastlt


open Classical in
theorem RelSeries.trimmed_length_eraseLast_of_lt
    {rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b)}
    (nontriv : rs.length > 0)
    (lastlt : ∃ i : Fin (rs.length), rs.toFun (i.castSucc) < rs.toFun i.succ ∧ (i + 1:ℕ) = rs.length)
    : rs.trimmed_length = rs.eraseLast.trimmed_length + 1 := by
      simp[RelSeries.trimmed_length]
      have foo : (Finset.univ : Finset (Fin (rs.length + 1))) =
               Finset.image (Fin.castLE (n := rs.length - 1 + 1) (by omega)) Finset.univ ∪ {Fin.last _} := by
        suffices m : (Finset.univ : Finset (Fin (rs.length + 1))) =
               {i : Fin (rs.length + 1) | ↑i < rs.length} ∪ {Fin.last rs.length} by
          simp_all
          ext a
          simp[Finset.eq_univ_iff_forall]
          by_cases ha : a = Fin.last rs.length
          · exact Or.inr ha
          · apply Or.inl
            have ha2 : a.val < rs.length - 1 + 1 := by
              simp_all
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
          · simp_all only [Fin.range_castLE, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.setOf_true,
            Set.mem_univ, Set.mem_setOf_eq, false_or]
            simp_all only [gt_iff_lt]
            --obtain ⟨w, h_1⟩ := lasteq
            --obtain ⟨left, right⟩ := h_1
            exact Fin.val_lt_last h
        · aesop
      rw[foo, Finset.image_union, Finset.image_singleton, Finset.image_image]--, Finset.union_eq_left.mpr]
      clear foo
      rw[Finset.card_union_of_disjoint, Finset.card_singleton]
      · rfl
      · simp
        intro i
        apply ne_of_lt

        --simp_all
        --#check @Fin.castLE (rs.length - 1 + 1) (rs.length + 1) (by omega) i
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
            --rw[Fin.coe_sub_one]
            --aesop
            have := hj.2
            --rw[Fin.val_eq_of_eq] at this
            have fact : j.val = j.castSucc.val := by exact rfl
            rw[← fact]
            omega


          rw[this]

          -- Know i < rs.length, so we should know that
          --apply le_of_lt_succ
        --have h : @Fin.castLE (rs.length - 1 + 1) (rs.length + 1) =  :=

        apply lt_of_le_of_lt (b := rs j.castSucc) --rs.toFun (Fin.last rs.length - 1))
        exact h₂
        have : j.succ = Fin.last rs.length := by aesop
        rw[← this]
        exact hj.1
        /-

        obtain ⟨j, hj⟩ := lastlt
        --let i' : Fin rs.length := ⟨i, by omega⟩

        have : (Fin.castLE (n := rs.length - 1 + 1) (m := rs.length + 1) (by omega) ↑↑i) = i'.castSucc := by
          apply Fin.eq_of_val_eq
          simp
        rw[this]
        have : Fin.last rs.length = i'.succ := by sorry

        rw[this]
        exact hj

        --exact hi.1.symm
        sorry
        -/


/-
This really ought to be implied by the previous lemmas, but the precise way it
is is kinda annoying
-/
open Classical in
theorem RelSeries.trimmed_length_eraseLast_le
  (rs : RelSeries (α := Submodule R M) (· ≤ ·)) (nontriv : rs.length > 0) :
  rs.eraseLast.trimmed_length ≤ rs.trimmed_length := by
    by_cases h : rs (rs.length - 1) = rs rs.length
    · have : ∃ i : Fin rs.length, rs.toFun i.succ = rs.toFun i.castSucc ∧ ↑i + 1 = rs.length := by
        let secondlast : Fin rs.length := ⟨rs.length - 1, by omega⟩
        use secondlast
        constructor
        · simp_all
          convert h.symm
          · apply Fin.eq_of_val_eq
            simp
            omega
          · apply Fin.eq_of_val_eq
            rw[Fin.coe_sub_one]
            simp
            split_ifs
            · next h1 =>
              exact Eq.symm ((fun {n} ↦ Nat.eq_self_sub_one.mpr) h1)
            · rfl
        simp
        omega
      --#check rs.trimmed_length_eraseLast_of_eq
      have := rs.trimmed_length_eraseLast_of_eq nontriv this
      exact Nat.le_of_eq (id (Eq.symm this))
    · have h' : rs.toFun (↑rs.length - 1) < rs.toFun ↑rs.length := by
        let sl : Fin rs.length := ⟨rs.length - 1, by omega⟩
        apply lt_of_le_not_le
        · convert rs.step sl
          · apply Fin.eq_of_val_eq
            simp
            rw[Fin.coe_sub_one]
            split
            · next h1 =>
              have h1' : rs.length = 0 := by aesop
              exact Nat.eq_self_sub_one.mpr h1'
            . rfl
          · apply Fin.eq_of_val_eq
            simp
            omega
        · suffices rs (↑rs.length - 1) < rs ↑rs.length by
            exact not_le_of_lt this
          apply lt_of_le_of_ne
          · apply RelSeries.map_le
            exact Fin.le_val_last (↑rs.length - 1)
          · exact h


      have : ∃ i : Fin rs.length, rs.toFun i.castSucc < rs.toFun i.succ ∧ ↑i + 1 = rs.length := by
        let secondlast : Fin rs.length := ⟨rs.length - 1, by omega⟩
        use secondlast
        constructor
        · simp_all
          convert h'
          · apply Fin.eq_of_val_eq
            simp
            rw[Fin.coe_sub_one]
            split_ifs
            · next h1 =>
              have h1' : rs.length = 0 := by aesop
              exact Eq.symm ((fun {n} ↦ Nat.eq_self_sub_one.mpr) h1')
            · rfl
          · apply Fin.eq_of_val_eq
            --rw[Fin.coe_sub_one]
            simp
            omega
        simp
        omega
      --#check rs.trimmed_length_eraseLast_of_eq
      have := rs.trimmed_length_eraseLast_of_lt nontriv this
      omega




/-

private lemma go_lemma (i : ℕ) (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b))
: go rs i = 1 + (go rs (i-1)) ∨ go rs i = go rs (i-1) := by
  cases i with
      | zero => simp
      | succ m =>
        simp[go]
        exact ne_or_eq (rs.toFun (m + 1)) (rs.toFun m)

/-
Note that n is just a natural number, which means we're doing stupid casting in this lemma.
It's probably more reasonable to have n be bounded by the lesser of the two Fin types.

Unfortunately, doing pattern matching with Fin types directly turned out to be hellish so I think
this way is preferable, but that means we have to interface with Nat.cast and keep in mind that
we're proving something slightly more general than intended
-/

--theorem val_
private lemma go_equiv (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b))
(rs' : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b))
(n : ℕ) (ltrs : n < rs.length + 1) (ltrs' : n < rs'.length + 1)
(eqs : ∀ i ≤ n, rs.toFun i = rs'.toFun i) : go rs n = go rs' n := by
  induction' o : n with m ih generalizing n
  · aesop
  · simp_all only [Nat.cast_add, Nat.cast_one, ↓reduceIte]
    let eqs' : ∀ i ≤ m, rs.toFun ↑i = rs'.toFun ↑i := by
          intro i hi
          let h' : i ≤ m+1 := Nat.le_add_right_of_le hi
          exact eqs i h'
    obtain h | h := em (rs.toFun (m + 1) = rs.toFun m)
    · simp[go, h]

      split
      next h_1 =>
        simp_all only [Nat.cast_add, Nat.cast_one]

        exact ih m (Nat.lt_of_succ_lt ltrs) (Nat.lt_of_succ_lt ltrs') eqs' rfl
      next h_1 =>
        simp_all only [Nat.cast_add, Nat.cast_one]
        have cont := eqs (m+1) (Nat.le_refl (m + 1))
        have cont' := eqs m (Nat.le_add_right m 1)
        rw[cont'] at h
        simp at cont
        rw[cont] at h
        exact False.elim (h_1 h)
    · let h' : ¬rs'.toFun (↑m + 1) = rs'.toFun ↑m := by
        have eqssm := eqs (m+1) (Nat.le_of_eq (id (Eq.symm rfl)))
        have eqsm := eqs m (by aesop)
        simp at eqssm
        rw[eqssm] at h
        rw[eqsm] at h
        exact h
      simp[go, h, h']

      exact ih m (Nat.lt_of_succ_lt ltrs) (Nat.lt_of_succ_lt ltrs') eqs' rfl


theorem RelSeries.trimmed_length_exists_eq {rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b)}
(hrs : rs.length > RelSeries.trimmed_length rs) : ∃ i, rs.toFun i = rs.toFun (i+1) := by
  apply by_contradiction
  intro notex
  simp at notex
  simp[RelSeries.trimmed_length] at hrs
  let gofact (i : ℕ) : go rs i = i := by
    induction i with
    | zero => aesop
    | succ n ih =>
      simp[go]
      simp_all only [Nat.cast_add, Nat.cast_one]
      split
      next h =>
        simp_all only [Nat.cast_add, Nat.cast_one, self_eq_add_right, one_ne_zero]
        exact ((notex n) h.symm)
      next h =>
        simp_all only [Nat.cast_add, Nat.cast_one]
        exact Nat.add_comm 1 n
  rw[gofact (rs.length)] at hrs
  obtain h | _ := em (rs.length = 0)

  · rw[h] at hrs

    contradiction

  · apply (lt_self_iff_false rs.length).mp
    exact hrs


theorem RelSeries.trimmed_length_exists_le {rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b)}
(hrs : rs.trimmed_length > 0) : ∃ i, rs.toFun i < rs.toFun (i+1) := by
  apply by_contradiction
  intro notex
  simp at notex
  simp[RelSeries.trimmed_length] at hrs
  have gofact (i : ℕ) : go rs i = 0 := by
    induction' o : i with n ih generalizing i
    · aesop
    · simp[go]
      --simp_all only [Nat.cast_add, Nat.cast_one]
      simp_all
      specialize notex n
      apply (eq_of_le_of_not_lt _ notex).symm
      --apply rs.step

      -- Should be a rewriting of notex (albeit an awful one)
      sorry

  rw[gofact (rs.length)] at hrs
  contradiction






  theorem RelSeries.trimmed_length_eraseLast_of_eq
    {rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b)}
    (nontriv : rs.length > 0)
    (lasteq : rs.toFun (rs.length) = rs.toFun (rs.length - 1))
    : rs.trimmed_length = rs.eraseLast.trimmed_length := by
      --let mas : ¬ rs.length = 0 := by aesop
      simp[RelSeries.trimmed_length]
      cases p : rs.length with
      | zero => aesop
      | succ n =>
        simp[go]

        simp[p] at lasteq

        simp[lasteq]

        apply go_equiv
        · rw[p]
          omega
        · simp
          omega
        · intro i ltn
          rw[RelSeries.eraseLast]
          simp only [Fin.val_cast_of_lt]
          apply congr_arg
          apply Fin.eq_of_val_eq
          simp
          let aux : i % (rs.length + 1) = i := by
            apply Nat.mod_eq_of_lt
            rw[p]
            omega
          let aux' : i % (rs.length - 1 + 1) = i := by
            apply Nat.mod_eq_of_lt
            rw[p]
            omega
          rw[aux, aux']


  theorem RelSeries.trimmed_length_eraseLast_of_lt
    {rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b)}
    (nontriv : rs.length > 0)
    (lastlt : rs.toFun (rs.length - 1) < rs.toFun (rs.length))
    : rs.trimmed_length = rs.eraseLast.trimmed_length + 1 := by
    simp[RelSeries.trimmed_length]

    cases p : rs.length with
      | zero => aesop
      | succ n =>
        simp[go]

        simp[p] at lastlt

        let mas : ¬ rs.toFun (n + 1) = rs.toFun n := ne_of_gt lastlt
        simp[mas]
        rw[Nat.add_comm]
        simp
        apply go_equiv
        · rw[p]
          omega
        · simp
          rw[p]
          omega
        · intro i ltn
          rw[RelSeries.eraseLast]
          simp only [Fin.val_cast_of_lt]
          apply congr_arg
          apply Fin.eq_of_val_eq
          simp
          let aux : i % (rs.length + 1) = i := by
            apply Nat.mod_eq_of_lt
            rw[p]
            omega
          let aux' : i % (rs.length - 1 + 1) = i := by
            apply Nat.mod_eq_of_lt
            rw[p]
            omega
          rw[aux, aux']





theorem RelSeries.trimmed_length_eraseLast_le
  (rs : RelSeries (α := Submodule R M) (· ≤ ·)) (nontriv : rs.length > 0) :
  rs.eraseLast.trimmed_length ≤ rs.trimmed_length := by
  rw[le_iff_eq_or_lt]
  obtain h | h := em <| rs (rs.length - 1) < rs (rs.length)
  · have proof := RelSeries.trimmed_length_eraseLast_of_lt nontriv h
    omega
  · have h' : rs (rs.length - 1) ≤ rs (rs.length) := by
      simp_all
      let m : Fin rs.length := {val := rs.length - 1, isLt := by aesop}
      convert rs.step m using 1
      · apply congr_arg
        apply Fin.eq_of_val_eq
        simp
        have h₂ : Fin.last rs.length = rs.length :=
          by exact Eq.symm (Fin.natCast_eq_last rs.length)
        rw[h₂]
        rw [@Fin.coe_sub_one]
        simp
        intro ez
        omega
      · apply congr_arg
        apply Fin.eq_of_val_eq
        simp only [Fin.val_last, Fin.val_succ]
        omega
    have h'' : rs.toFun (↑rs.length - 1) = rs.toFun ↑rs.length := by
      convert h
      exact LE.le.eq_iff_not_lt h'
    have proof := RelSeries.trimmed_length_eraseLast_of_eq nontriv h''.symm
    omega






/-
Not an api lemma, just set to private to maintin some of the proofs as they were
-/
private def concat {α : Type*} {r : Rel α α} (p q : RelSeries r) (connect : r p.last q.head) : RelSeries r where
length := p.length + q.length + 1
toFun i :=
  if H : i.1 < p.length + 1
  then p ⟨i.1, H⟩
  else q ⟨i.1 - (p.length + 1),
          Nat.sub_lt_left_of_lt_add (by rwa [not_lt] at H)
          (by rw [← add_assoc]; ring_nf at i; omega)⟩
step i := by
  dsimp only
  by_cases h₂ : i.1 + 1 < p.length + 1
  · have h₁ : i.1 < p.length + 1 := by omega
    have h₁' : i.1 < p.length := by omega
    simp only [Fin.coe_castSucc, h₁, ↓reduceDIte, Fin.val_succ, add_lt_add_iff_right, h₁']
    exact p.step ⟨i, h₁'⟩
  · simp only [Fin.coe_castSucc, Fin.val_succ, h₂, ↓reduceDIte, Nat.reduceSubDiff]
    split_ifs with h₁
    · have h₃ : p.length = i.1 := by omega
      convert connect
      · simp_all
        have check : p.last = p.toFun (p.length) := by simp[RelSeries.last]
        rw[check]
        apply congr_arg
        apply Fin.eq_of_val_eq
        simpa using h₃.symm
      · simp_all
        exact rfl

    · convert q.step ⟨i.1 - (p.length + 1), _⟩ using 1
      · congr
        omega
      · have imas : ↑i < p.length + 1 + q.length := by omega
        refine Nat.sub_lt_left_of_lt_add ?_ imas
        rwa [not_lt] at h₁


private lemma exists_relseries_with_trimmed_length (rs : RelSeries (α := Submodule R M) (· ≤ ·)) :
  ∃ (rs' : RelSeries (α := Submodule R M) (· < ·)),
  rs'.length = rs.trimmed_length ∧ ∀ i : Fin (rs.length + 1), ∃ j : Fin (rs'.length + 1), rs i = rs' j := by
  induction' o : rs.trimmed_length with n ih generalizing rs
  · use RelSeries.singleton (α := Submodule R M) (· < ·) (rs.head)
    constructor
    · exact rfl
    · intro i
      use 0
      /-
      We probably need some lemma here saying that if the trimmed length is 0 then everything
      is equal, which should just be a relatively straightforward induction argument
      -/

      sorry
  · have : rs.trimmed_length > 0 := by aesop


    /-
    Find an index i where rs i < rs (i+1). The idea here is we want to remove i (or, I suppose, i+1),
    then we should reduce the trimmed length by 1, and yield an ltseries of length n by the ih.
    Note that rs (i-1) may be either equal or less than rs i.

    The argument should then be that we place rs i back into the lt series to get our final thing
    of length n+1. I think for this we need to prove a slightly stronger statement, because as
    it is we don't know anything about the form of this ltseries we're producing.

    We want to say that all the terms of rs' are terms of rs and that all terms in rs appear in rs'
    In other words, we want to say that ∀ i : Fin (rs.length), ∃ j : Fin (rs'.length), rs i = rs' j.
    To use this, we just need to find the index j which is equal to rs (i+1), then we insert our rs i
    before it (we do this by case matching on whether rs' (j-1) is equal to rs i or not, either way
    we win).

    -/
    obtain ⟨i, hi⟩ := RelSeries.trimmed_length_exists_le this

    /-
    takes first i-1 elements of rs
    -/
    let left := rs.take (i-1)

    /-
    drops all elements before index i+1
    -/
    let right := rs.drop i
    have connect : left.last ≤ right.head := by sorry
    let iremoved := concat left right connect
    have h₁ : iremoved.trimmed_length = n := by sorry

    obtain ⟨lts, hlts₁, hlts₂⟩ := ih iremoved h₁

    /-
    iremoved is just rs with i removed, and so the element rs (i+1) will be iremoved i, hence we
    specialize at i
    -/
    --specialize hlts₂ i
    obtain ⟨j, hj⟩ := hlts₂ i

    have h₂ : iremoved i = rs (i+1) := by sorry
    --rw[h₂] at hj
    --rw[hj] at hi
    by_cases h₃ : lts (j-1) = rs i
    · /-
      In this case where lts j-1 = rs i, we can't use insertNth because of course
      lts (j - 1) < lts (j - 1) is not true.

      This should be fine though since we have concat, we can just take the first j-1 and concat
      that with cons (rs i) (drop (j-1) lts) or something like this. Indeed, we can also use
      cons, snoc and smash if we find that the lemmas for concat are too lacking for this
      -/
      sorry
    · have h₃' : lts (j-1) < rs i := sorry
      rw[h₂] at hj
      rw[hj] at hi

      /-
      We want this, but annoyingly j is of the wrong type. Potentially just need to change around
      the types in the theorem statement

      use (lts.insertNth j (rs i) h₃' hi)
      -/


      sorry


theorem Module.length_ge_trimmed_length
(rs : RelSeries fun (a : Submodule R M) (b : Submodule R M) => a ≤ b)
  : RelSeries.trimmed_length rs ≤ Module.length R M := by
  obtain ⟨rs', hrs'⟩ := exists_relseries_with_trimmed_length rs
  rw[← hrs'.1]
  rw[Module.length, krullDim]
  exact le_iSup_iff.mpr fun b a ↦ a rs'



/-
Non used lemmas about trimmed_length:

private theorem RelSeries.trimmed_length_leq_length (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b))
  : rs.length ≥ RelSeries.trimmed_length rs := by
    simp[RelSeries.trimmed_length]
    induction rs.length with
    | zero => aesop
    | succ n ih =>
      let test (i : ℕ) : go rs i = 1 + (go rs (i-1)) ∨ go rs i = go rs (i-1) := by
        cases i with
        | zero => simp
        | succ m =>
          simp only [go, Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, ite_eq_right_iff,
            self_eq_add_left, one_ne_zero, imp_false, ite_eq_left_iff, add_left_eq_self, not_not]
          exact ne_or_eq (rs.toFun (↑m + 1)) (rs.toFun ↑m)
      simp_all
      obtain h' | h' := test (n+1)
      · simp only [add_tsub_cancel_right] at h'
        rw[h']
        refine Nat.one_add_le_iff.mpr ?succ.inl.a
        exact lt_add_one_iff.mpr ih

      · simp only [add_tsub_cancel_right] at h'
        rw[h']
        exact Nat.le_add_right_of_le ih


-/
-/
