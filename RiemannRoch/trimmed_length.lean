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
--import Plausible

open AlgebraicGeometry
open CategoryTheory
open Opposite.op
open Module
open Order
open Ring




section FL

  variable {R : Type*}
           [Ring R]
           {M M' : Type*}
           [AddCommGroup M]
           [AddCommGroup M']
           [Module R M]
           [Module R M']
           --(fl : IsFiniteLength R M)


  variable (R M) in
  open Classical in
  noncomputable
  def Module.length := krullDim (α := Submodule R M)



  -- Helper function for trimmed length which computes the number of <'s occuring in a leseries
  open Classical in
  noncomputable
  def go (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b)) (n : ℕ) : ℕ :=
    match n with
      | 0     => 0
      | (m+1) => if rs.toFun n = rs.toFun m then go rs m else 1 + go rs m

  -- Length of an le series only counting steps which are not equality
  noncomputable
  def RelSeries.trimmed_length (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b)) : ℕ :=
    go rs rs.length


  lemma go_lemma (i : ℕ) (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b))
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
  lemma go_equiv (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b))
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





  theorem iSup_le_add {ι ι': Sort*} [Nonempty ι] [Nonempty ι']
   {f : ι → WithBot ℕ∞} {g : ι' → WithBot ℕ∞} {a : WithBot ℕ∞} :
  iSup f + iSup g ≤ a ↔ ∀ (i: ι) (j : ι'), f i + g j ≤ a := by
    apply Iff.intro
    · intro a_1 i j

      sorry
    · intro a_1

      sorry






  /-
  Note: this is just a rewriting of the definition of smash which yields a more general notion
  of concatenation. In principal I think smash should be defined in terms of concat but it might
  be annoying to do this replacement in practice.
  -/
  def concat {α : Type*} {r : Rel α α} (p q : RelSeries r) (connect : r p.last q.head) : RelSeries r where
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


  lemma exists_relseries_with_trimmed_length (rs : RelSeries (α := Submodule R M) (· ≤ ·)) :
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




end FL
