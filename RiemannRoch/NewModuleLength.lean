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

  /-
  def Module.length' : ℕ :=
    sSup {n : ℕ | (∃ rs : RelSeries (α := Submodule R M) (· < ·), rs.head = ⊥ ∧ rs.last = ⊤ ∧ rs.length = n)}

  #check Order.krullDim

  variable (M) in
  open Classical in
  noncomputable
  def Module.length'' : ℕ :=
  ⨆ (rs : RelSeries (α := Submodule R M) (· < ·)), rs.length

  #check Module.length' M = Module.length'' M

  -/


  --theorem sanitycheck : length' M = 2 := sorry
  /-
  open Classical in
  theorem Module.length_witness (s : CompositionSeries (Submodule R M))
    (cs : RelSeries.head s = ⊥ ∧ RelSeries.last s = ⊤) : Module.length fl = s.length := by
      simp[Module.length]
      rw[Nat.find_eq_iff]
      simp
      constructor
      use s
      aesop
      intro n bound other hdother lastother len
      have p : RelSeries.head s = RelSeries.head other := by
        rw[cs.1]
        exact id (Eq.symm hdother)
      have q : RelSeries.last s = RelSeries.last other := by
        rw[cs.2]
        exact id (Eq.symm lastother)
      let contr := CompositionSeries.jordan_holder s other p q
      unfold CompositionSeries.Equivalent at contr
      obtain ⟨g, _⟩ := contr
      apply Nat.card_eq_of_equiv_fin at g
      simp at g
      aesop
  -/

  /-
  def CompositionSeries.compositionSeries_of_injective {f : M →ₗ[R] M'} (hf : Function.Injective f)
      (s : CompositionSeries (Submodule R M)) :
      CompositionSeries (Submodule R M') := {
        length := s.length
        toFun := fun n => Submodule.map f (s.toFun n)
        step := by {
          let proof := Submodule.map_strictMono_of_injective hf
          intro i
          simp[JordanHolderModule.instJordanHolderLattice]
          --rw[covBy_iff_quot_is_simple]
          sorry
          --apply proof
          --exact CompositionSeries.lt_succ s i
        }
      }
    -/
  def RelSeries.submoduleMap_injective {f : M →ₗ[R] M'} (hf : Function.Injective f)
      (s : RelSeries (α := Submodule R M) (· < ·)) :
      RelSeries (α := Submodule R M') (· < ·) := {
        length := s.length
        toFun := fun n => Submodule.map f (s.toFun n)
        step := by {
          let proof := Submodule.map_strictMono_of_injective hf
          intro i
          apply proof
          exact s.step i
        }
      }

  def RelSeries.submoduleComap_surjective {f : M →ₗ[R] M'} (hf : Function.Surjective f)
      (s : RelSeries (α := Submodule R M') (· < ·)) :
      RelSeries (α := Submodule R M) (· < ·) := {
        length := s.length
        toFun := fun n => Submodule.comap f (s.toFun n)
        step := by {
          let proof := Submodule.comap_strictMono_of_surjective hf
          intro i
          apply proof
          exact s.step i
        }
      }


def RelSeries.IsCompositionSeries
(rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b)) : Prop :=
  rs.head = ⊥ ∧ rs.last = ⊤ ∧ ∀ (i : Fin rs.length),
  JordanHolderLattice.IsMaximal (rs.toFun i.castSucc) (rs.toFun i.succ)


def RelSeries.composition_series_of
  {rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b)}
  (cs : RelSeries.IsCompositionSeries rs) : CompositionSeries (Submodule R M) :=
  { length := rs.length
    toFun := rs.toFun
    step := cs.2.2 }

  def CompositionSeries.lt_series (cs : CompositionSeries (Submodule R M))
  : @RelSeries (Submodule R M) (· < ·) := by
  let inst : Lattice (Submodule R M) := by infer_instance
  let inst' : JordanHolderLattice (Submodule R M) := by infer_instance
  let p : @JordanHolderLattice.IsMaximal (Submodule R M) inst inst' ≤ fun a b ↦ a < b := by
    apply JordanHolderLattice.lt_of_isMaximal
  exact RelSeries.ofLE cs p

  /-
  A filtration of a module which is not a composition series must have some pair of consecutive
  elements whose quotient is not simple
  -/

  /-
  theorem RelSeries.exists_nonMaximal
    {rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b)}
    (h : rs.length ≠ Module.length fl)
    (hm : rs.head = ⊥ ∧ rs.last = ⊤)
    : ∃ n : Fin (rs.length), ¬ (JordanHolderLattice.IsMaximal (rs.toFun n) (rs.toFun (n+1))) := by
    apply by_contradiction
    intro assum
    simp at assum
    let cs : CompositionSeries (Submodule R M) := {
      length := rs.length
      toFun := rs.toFun
      step := assum
    }
    exact h (id (Eq.symm (Module.length_witness fl cs hm)))
    -/

  /-
  Not directly relevant, but doesn't break I supppose
  -/
  theorem RelSeries.max_chain_head_tail
  {rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b)}
  (maximal : ∀ xs : RelSeries (fun (a : Submodule R M)
  (b : Submodule R M) => a < b), rs.length ≥ xs.length)
  : rs.head = ⊥ ∧ rs.last = ⊤ := by
  by_contra absurdity
  obtain h | h : rs.head ≠ ⊥ ∨ rs.last ≠ ⊤ := by tauto
  · let cont := rs.cons ⊥ (Ne.bot_lt' (id (Ne.symm h)))
    specialize maximal cont
    let mm : cont.length = rs.length.succ := cons_length rs ⊥ (Ne.bot_lt' (id (Ne.symm h)))
    rw[mm] at maximal
    omega
  · let cont := rs.snoc ⊤ (Ne.lt_top' (id (Ne.symm h)))
    specialize maximal cont
    let mm : cont.length = rs.length.succ := rfl
    rw[mm] at maximal
    omega

  theorem RelSeries.chain_le_bot_top
  (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b))
  : ∃ xs : RelSeries (α := Submodule R M) (· < ·),
    xs.length ≥ rs.length ∧ xs.head = ⊥ ∧ xs.last = ⊤ := by
    obtain h | h := em (rs.head = ⊥)
    · obtain q | q := em (rs.last = ⊤)
      · use rs
      · have : rs.last < ⊤ := by exact Ne.lt_top' fun a ↦ q (id (Eq.symm a))
        use rs.snoc ⊤ this
        aesop
    · have : ⊥ < rs.head := by exact Ne.bot_lt' fun a ↦ h (id (Eq.symm a))
      obtain q | q := em (rs.last = ⊤)
      · use rs.cons ⊥ this
        aesop
      · let this' : (rs.cons ⊥ this).last < ⊤ := by
          simp
          exact Ne.lt_top' fun a ↦ q (id (Eq.symm a))
        use (rs.cons ⊥ this).snoc ⊤ this'
        simp only [snoc_length, cons_length, ge_iff_le, head_snoc, head_cons, last_snoc, and_self,
          and_true]
        omega



  /-
  by_contra absurdity
  obtain h | h : rs.head ≠ ⊥ ∨ rs.last ≠ ⊤ := by tauto
  · let cont := rs.cons ⊥ (Ne.bot_lt' (id (Ne.symm h)))
    specialize maximal cont
    let mm : cont.length = rs.length.succ := cons_length rs ⊥ (Ne.bot_lt' (id (Ne.symm h)))
    rw[mm] at maximal
    omega
  · let cont := rs.snoc ⊤ (Ne.lt_top' (id (Ne.symm h)))
    specialize maximal cont
    let mm : cont.length = rs.length.succ := rfl
    rw[mm] at maximal
    omega

    -/



  /-
  theorem Module.length_sup_is_max
  (fl : IsFiniteLength R M) :
  ∃ (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b)),
  rs.length = ⨆ (xs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b)), xs.length
  := by
    let fl' := fl
    rw[isFiniteLength_iff_exists_compositionSeries] at fl

    choose s hs using fl

    apply by_contradiction

    intro assum
    simp at assum
    rw[isFiniteLength_iff_isNoetherian_isArtinian] at fl'
    rw[←monotone_stabilizes_iff_noetherian] at fl'

    /-
    So, this proof is maybe a bit weird. We want to say suppose there is no maximal relseries.
    Then, we should be able to show that there is some infinite chain
    -/
    simp[iSup, sSup] at assum
    split at assum
    next h_1 =>
      obtain ⟨left, right⟩ := fl'
      obtain ⟨left_1, right_1⟩ := hs
      obtain ⟨w, h⟩ := h_1

      sorry
    --use s.lt_series

    --rw[Module.length_witness fl s hs]

    sorry
    -/
  /-
  theorem Module.length_is_maximal : length fl
    = ⨆ (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b)), rs.length := by
      rw [Nat.le_antisymm_iff]
      rw[isFiniteLength_iff_exists_compositionSeries] at fl

      choose s hs using fl

      rw[Module.length_witness fl s hs]
      constructor
      · -- This really ought to be just by definition
        simp[iSup, sSup]
        split
        next h_1 =>
          simp
          intro m mle
          use s.lt_series
          exact mle
        next h_1 =>
          simp at h_1
          obtain ⟨rs, hrs⟩ := h_1 s.length
          simp_all only [nonpos_iff_eq_zero]
          obtain ⟨left, right⟩ := hs
          -- This is more annoying than expected, but should still be doable
          sorry

      · simp[iSup, sSup]
        split
        next h_1 =>
          --obtain ⟨rs, hrs⟩ := h_1
          simp
          use s.length
          constructor
          exact Nat.le_refl s.length
          intro rs
          apply by_contradiction
          intro contr
          -- It would be useful at this point to have something which says that if something has
          -- length which is not equal to a composition series, it must have some position where
          -- it's non-maximal
          let contr' : rs.length > s.length := by aesop
          /-
          Here there are no assumptions on rs, we're just saying given an arbitrary rs, suppposing
          it has a length larger than s.length should give a contradiction.

          We're going to need to use the Noetherian-ness of our ring, because we're going to extend
          rs until it's maximal length

          Alternatively, it would be really nice to have a proof which looks like "suppose rs were
          maximal length without being a composition series, then we could make something bigger
          so contradiction". We possibly need another lemma saying that this sup really is a max,
          then we could change to this proof strategy.
          -/


          sorry
          --use s.lt_series
          --exact rfl
        next h_1 =>
          aesop
    -/

  /-
  I think the idea here should be you case match on whether rs is a composition series or not.
  If it is one, then you're done by Jordan Holder.

  If it's not, then there must be some place where the quotient is non simple, so this part of
  the series factors into more maps, increasing the length and giving a contradiction.
  -/

def RelSeries.is_maximal_length {α : Type*} {r : Rel α α} (rs : RelSeries r) :=
  ∀ xs : RelSeries r, rs.length ≥ xs.length

/-
(maximal : ∀ xs : RelSeries (fun (a : Submodule R M)
  (b : Submodule R M) => a < b), rs.length ≥ xs.length)
-/
/-
open CompositionSeries in
theorem Module.length_maximal
  {rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b)}
  (maximal : rs.is_maximal_length)
  : rs.length = length fl := by
  let ht := RelSeries.max_chain_head_tail maximal
  obtain h | h := em (RelSeries.IsCompositionSeries rs)
  · let cs := RelSeries.composition_series_of h
    rw[Module.length_witness fl cs ht]
    rfl
  · simp[RelSeries.IsCompositionSeries] at h
    obtain ⟨i, hi⟩ := h ht.1 ht.2
    simp[JordanHolderModule.instJordanHolderLattice, CovBy] at hi
    obtain ⟨x, hx⟩ := hi (rs.step i)

    let contrs := RelSeries.insertNth rs i x hx.1 hx.2
    let cont : contrs.length = rs.length + 1 := rfl
    specialize maximal contrs
    rw[cont] at maximal
    omega
-/
--def FiniteLength.exists_maximal_chain : sorry := sorry

/-
∀ rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b),
 mrs.length ≥ rs.length
-/

/-
THIS HAS NO REASON TO BE TRUE AS STATED, SINCE WE CAN POSTPONE < INSTANCES FOR AS LONG AS WE LIKE
THROUGH OUR MONOTONE FUNCTION.

WE NEED TO REPHRASE
theorem finiteLength_exists_maximal_chain (fl : IsFiniteLength R M) :
  ∃ n : ℕ, ∀ f : ℕ →o Submodule R M, ∀ (m : ℕ), n ≤ m → f n = f m := by
  rw[isFiniteLength_iff_isNoetherian_isArtinian] at fl
  rw[←monotone_stabilizes_iff_noetherian] at fl
  rw[← monotone_stabilizes_iff_artinian] at fl
  obtain ⟨achain, dchain⟩ := fl
  --by_contra assum
  --simp only [not_exists, not_forall, Classical.not_imp] at assum
  by_contra assum
  simp at assum
  -- This should just be a rewriting of assum
  let bigchain : ∃ (f : ℕ →o Submodule R M), ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ f n ≠ f m := by
    let f : ℕ →o Submodule R M := {
      toFun := fun i ↦ by
        specialize assum i
        choose f x hx using assum
        exact f x
      monotone' := by
        simp
        intro l k p j hj
        simp_all

        sorry
    }


    sorry
  obtain ⟨f, hf⟩ := bigchain
  obtain ⟨a, ha⟩ := achain f
  obtain ⟨m, hm⟩ := hf a
  specialize ha m
  simp_all
-/
/-
theorem Module.finite_length_exists_maximal_relseries
 (fl : IsFiniteLength R M) :
 ∃ mrs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b),
 mrs.is_maximal_length := by
 by_contra assum
 simp at assum
 rw[isFiniteLength_iff_isNoetherian_isArtinian] at fl
 rw[←monotone_stabilizes_iff_noetherian] at fl
 rw[← monotone_stabilizes_iff_artinian] at fl
 --obtain h | h := em <| ∃ f : ℕ →o Submodule R M, ∃ n, ∀ (m : ℕ), n ≤ m → f n = f m

 -- Here we split into cases whether or not there exists a global maximum on chain length
 obtain h | h := em <| ∃ n : ℕ, ∀ f : ℕ →o Submodule R M, ∀ (m : ℕ), n ≤ m → f n = f m
 · --obtain ⟨f, ⟨n, hn⟩⟩ := h
   obtain ⟨max, hmax⟩ := h
   let cont : ∃ (f : ℕ →o Submodule R M) (m : ℕ), max ≤ m ∧ f max ≠ f m := by
    -- do some schenanigans, should just be an application of fl
    sorry
   obtain ⟨fcont, ⟨m, hn⟩⟩ := cont
   specialize hmax fcont m
   exact hn.2 (hmax hn.1)


 · -- Here we're trying to prove that there is indeed a maximal chain in a finite length module
   --simp only [not_exists, not_forall, Classical.not_imp] at h

   simp only [not_exists, not_forall] at h



   -- Suppose there were no max length.
   sorry
  --simp_all only [exists_const, not_true_eq_false]
-/


/--/
open CompositionSeries in
  theorem Module.length_ge_relSeries
    (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b))
    : length fl ≥ rs.length := by
      rw[isFiniteLength_iff_isNoetherian_isArtinian] at fl
      rw[←monotone_stabilizes_iff_noetherian] at fl

      --apply Module.length_maximal
      sorry

-/

  example : 1 = 1 := by
    let h : 1 = 1 := rfl
    exact h

  def RelSeries.submoduleMap (rs : RelSeries (α := Submodule R M) (· < ·))
    (f : M →ₗ[R] M') : RelSeries (α := Submodule R M') (· ≤ ·) :=
      RelSeries.map rs {toFun := Submodule.map f, map_rel' := fun a ↦ Submodule.map_mono (a.le)}

  def RelSeries.submoduleComap (rs : RelSeries (α := Submodule R M') (· < ·))
    (f : M →ₗ[R] M') : RelSeries (α := Submodule R M) (· ≤ ·) :=
      RelSeries.map rs {toFun := Submodule.comap f, map_rel' := fun a ↦ Submodule.comap_mono (a.le)}



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

  -- a < b < c has length 2
  -- a0 < a1 < a2, elements of Fin 3
  -- i.e. going down from length to 0
  -- Fin n = {0, 1, 2, ..., n-1}
  -- a0 has length 1, indexed by elems of Fin 1

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
        --simp_all only [Nat.cast_add, Nat.cast_one, ↓reduceIte]
        split
        next h_1 =>
          simp_all only [Nat.cast_add, Nat.cast_one]
          /-
          let eqs' : ∀ (i : Fin (m+1)), rs.toFun i = rs'.toFun i := by
            intro i
            specialize eqs i
            --rw[Fin.cast_val_eq_self i]
            sorry
            --simp only [Fin.coe_eq_castSucc, Fin.coe_castSucc] at eqs
            --exact eqs
          -/
          exact ih m (Nat.lt_of_succ_lt ltrs) (Nat.lt_of_succ_lt ltrs') eqs' rfl
        next h_1 =>
          simp_all only [Nat.cast_add, Nat.cast_one]
          have cont := eqs (m+1) (Nat.le_refl (m + 1))
          have cont' := eqs m (Nat.le_add_right m 1)
          rw[cont'] at h
          simp at cont
          rw[cont] at h
          exact False.elim (h_1 h)


          /-
          let castlem : (Nat.cast m + 1) = Nat.cast (m + 1) := by exact rfl
          let dumb : rs.toFun (Nat.cast m + 1) = rs.toFun (Nat.cast (m + 1)) :=
            congr_arg rs.toFun castlem

          -/


          --rw[eqs (m)] at h
          --let ih' := ih m (Nat.lt_of_succ_lt ltrs) (Nat.lt_of_succ_lt ltrs') eqs' rfl
          /-
          let shouldberw : rs'.toFun (m + 1) = rs'.toFun m := by

            let some : m < rs.length + 1 := sorry
            sorry
          exact False.elim (h_1 shouldberw)
        simp[go, h]
        simp_all only [Nat.cast_add, Nat.cast_one, ↓reduceIte]
        split
        next h_1 =>
          sorry
        next h_1 =>
          sorry
        -/
      · let h' : ¬rs'.toFun (↑m + 1) = rs'.toFun ↑m := by
          have eqssm := eqs (m+1) (Nat.le_of_eq (id (Eq.symm rfl)))
          have eqsm := eqs m (by aesop)
          simp at eqssm
          rw[eqssm] at h
          rw[eqsm] at h
          exact h
        simp[go, h, h']
        --let ltsmas : m.succ < rs.length + 1 := by exact lt_of_eq_of_lt (id (Eq.symm o)) ltrs
        exact ih m (Nat.lt_of_succ_lt ltrs) (Nat.lt_of_succ_lt ltrs') eqs' rfl


  theorem RelSeries.trimmed_length_leq_length (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b))
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



  theorem Set.preimage_mono_of_range_intersection {A B : Type*} {f : A → B} {S S' : Set B}
    (ltint : Set.range f ⊓ S < Set.range f ⊓ S') (lt : S ≤ S') : f ⁻¹' S < f ⁻¹' S' := by
      simp_all
      rw[Set.ssubset_def]
      rw[Set.ssubset_def] at ltint

      constructor
      apply Set.monotone_preimage
      exact lt
      intro opp
      let k : f ⁻¹' S ⊆ f ⁻¹' S' := by
        apply Set.monotone_preimage
        exact lt
      let jint : Set.range f ⊓ S = Set.range f ⊓ S' := by aesop
      let obv : ¬ (Set.range f ∩ S = Set.range f ∩ S') := by aesop
      exact obv jint


  theorem kernel_intersection {A B : Submodule R M} {f :  M →ₗ[R] M'} (hab : A < B)
    (q : Submodule.map f A = Submodule.map f B) : LinearMap.ker f ⊓ A < LinearMap.ker f ⊓ B := by
      rw[lt_iff_le_and_ne]
      constructor
      · exact inf_le_inf le_rfl hab.le
      · intro H
        apply hab.ne
        apply le_antisymm hab.le
        intro x hx
        let y := f x
        have hy : y ∈ Submodule.map f B := by use x, hx
        rw[←q] at hy
        obtain ⟨z, hz, hzy⟩ := hy
        suffices x - z ∈ LinearMap.ker f ⊓ A by
          simpa using add_mem this.2 hz
        rw[H]
        constructor
        · simp[hzy]
        · apply sub_mem hx (hab.le hz)

  -- Since this is almost exactly the same proof this could probably be given a bit of a refactor,
  -- but that's alright
  theorem kernel_intersection' {A B : Submodule R M} {f :  M →ₗ[R] M'} (hab : A < B)
    (q : LinearMap.ker f ⊓ A = LinearMap.ker f ⊓ B) : Submodule.map f A < Submodule.map f B := by
      rw[lt_iff_le_and_ne]
      constructor
      · exact Set.image_mono hab.le
      · intro H
        apply hab.ne
        apply le_antisymm hab.le
        intro x hx
        let y := f x
        have hy : y ∈ Submodule.map f B := by use x, hx
        rw[←H] at hy
        obtain ⟨z, hz, hzy⟩ := hy
        suffices x - z ∈ LinearMap.ker f ⊓ A by
          simpa using add_mem this.2 hz
        rw[q]
        constructor
        · simp[hzy]
        · apply sub_mem hx (hab.le hz)

 theorem image_intersection {A : Submodule R M'} {f :  M →ₗ[R] M'} :
   Submodule.map f (Submodule.comap f A) = (LinearMap.range f) ⊓ A := by
    aesop


  theorem RelSeries.submodule_comap_lt_of_map_eq_exact
    {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS : S.ShortExact)
    (rs : RelSeries (α := Submodule R S.X₂) (· < ·)) (i : Fin rs.length)
    (p : (rs.submoduleMap S.g).toFun i = (rs.submoduleMap S.g).toFun (i+1))
    : (rs.submoduleComap S.f).toFun i < (rs.submoduleComap S.f).toFun (i+1) := by

      have kernelInt : LinearMap.ker S.g ⊓ (rs.toFun i) < LinearMap.ker S.g ⊓ (rs.toFun (i+1)) := by
       have p' : Submodule.map S.g (rs.toFun i.castSucc) = Submodule.map S.g (rs.toFun i.succ) :=
        by aesop
       have ans := kernel_intersection (rs.step i) p'
       aesop

      have exactness : LinearMap.ker S.g = LinearMap.range S.f := by
        have proof := CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hS.exact
        exact id (Eq.symm proof)

      rw[exactness] at kernelInt

      simp_all

      have intLem (k : Fin (rs.length + 1)) :
       (rs.submoduleComap S.f).toFun k = Submodule.comap S.f (LinearMap.range S.f ⊓ rs.toFun k) :=
         by aesop
      rw[intLem i.castSucc, intLem i.succ]

      have lem := Set.preimage_mono_of_range_intersection kernelInt (le_of_lt (rs.step i))
      simp
      have comap_range : Submodule.comap S.f (LinearMap.range S.f) = ⊤ := by aesop
      rw[comap_range]
      simp
      exact lem


    theorem RelSeries.submodule_map_lt_of_comap_eq_exact {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS : S.ShortExact)
    (rs : RelSeries (α := Submodule R S.X₂) (· < ·)) (i : Fin rs.length)
    (p : (rs.submoduleComap S.f).toFun i = (rs.submoduleComap S.f).toFun (i+1))
    : (rs.submoduleMap S.g).toFun i < (rs.submoduleMap S.g).toFun (i+1) := by

      let exactness : LinearMap.range S.f = LinearMap.ker S.g :=
        CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hS.exact

      let imInt : LinearMap.range S.f ⊓ (rs.toFun i) = LinearMap.range S.f ⊓ (rs.toFun (i+1)) := by
        rw[←image_intersection, ←image_intersection]
        exact congrArg (Submodule.map S.f) p


      rw[exactness] at imInt

      simp_all

      let intLem (k : Fin (rs.length + 1)) :
        (rs.submoduleMap S.g).toFun k = Submodule.map S.g (rs.toFun k) := by aesop
      rw[intLem i.castSucc, intLem i.succ]

      exact kernel_intersection' (rs.step i) imInt




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
          --let imod : i % (rs.length - 1 + 1) = i := by sorry


          --rw [← imod]





          -- Now it's basically nothing to prove this



          --let lesconf := ih p


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
            --let imod : i % (rs.length - 1 + 1) = i := by sorry





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


  theorem trimmed_length_additive
    {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS : S.ShortExact)
      (rs : RelSeries (α := Submodule R S.X₂) (· < ·)) :
      rs.length ≤ RelSeries.trimmed_length (rs.submoduleMap S.g) + RelSeries.trimmed_length (rs.submoduleComap S.f) := by

        induction' o : rs.length with n ih generalizing rs
        · aesop
        · -- Case match on the last ineqality in the seires on the right. If it's equality, then
          -- the guy on the left is < and we use our lemmas about trimmed length on eraseLast to
          -- get the job done. If instead we have < on the right, it's even easier because we get
          -- our lemma just by looking at the right series.
          let n' : Fin (rs.length) := {val := n, isLt := by aesop}
          obtain q | q := em ((rs.submoduleMap S.g).toFun n = (rs.submoduleMap S.g).toFun (n + 1))
          · let n' : Fin (rs.length) := {val := n, isLt := by rw[o] ; exact lt_add_one n}

            let leleft := RelSeries.submodule_comap_lt_of_map_eq_exact hS rs n' q
            simp at leleft

            -- This is just a rephrasing of q

            let qcoe : (rs.submoduleMap S.g).toFun ((rs.submoduleMap S.g).length) =
                       (rs.submoduleMap S.g).toFun ((rs.submoduleMap S.g).length - 1) := by
                       let mas : (rs.submoduleMap S.g).length = rs.length := rfl
                       rw[o] at mas
                       aesop

            let obv : (rs.submoduleMap S.g).length > 0 := by exact Fin.pos n' --by exact Nat.zero_lt_of_lt h
            rw[RelSeries.trimmed_length_eraseLast_of_eq obv qcoe]

            let rserasedLen : rs.eraseLast.length = n := by aesop

            let iherased := ih rs.eraseLast rserasedLen


            --let q' : (rs.submoduleMap S.g).toFun n' = (rs.submoduleMap S.g).toFun (n' + 1) := q
            --let leftlt' := RelSeries.submodule_comap_lt_of_map_eq_exact hS rs n' q

            let leftlt : (rs.submoduleComap S.f).toFun ((rs.submoduleComap S.f).length - 1)
            < (rs.submoduleComap S.f).toFun (rs.submoduleComap S.f).length := by
              let leftlen : (rs.submoduleComap S.f).length = rs.length := rfl
              simp_all[leftlen]



            let leftlength : (rs.submoduleComap S.f).length = n+1 := by aesop

            let nonempt : (rs.submoduleComap S.f).length > 0 := by aesop

            --#check RelSeries.trimmed_length_eraseLast_le
            rw[RelSeries.trimmed_length_eraseLast_of_lt nonempt leftlt]
            exact Nat.add_le_add_right iherased 1


          · have q' : (rs.submoduleMap S.g).toFun n < (rs.submoduleMap S.g).toFun (n + 1) := by
              let leq := (rs.submoduleMap S.g).step n'
              rw [@le_iff_eq_or_lt] at leq
              simp
              let qdif : ¬(rs.submoduleMap S.g).toFun n' = (rs.submoduleMap S.g).toFun (n' + 1) := q

              simp at qdif
              obtain h | h := leq

              · have hdif : (rs.submoduleMap S.g).toFun n' = (rs.submoduleMap S.g).toFun (n' + 1) := by
                  simp
                  have ncast : (rs.submoduleMap S.g).toFun n =
                              (rs.submoduleMap S.g).toFun n'.castSucc := by
                    --let neqiv : n = n'.castSucc := rfl
                    apply congr_arg
                    apply Fin.eq_of_val_eq
                    simp only [Fin.val_natCast, Fin.coe_castSucc, Nat.mod_succ_eq_iff_lt,
                      Nat.succ_eq_add_one]
                    let rightlen : (rs.submoduleMap S.g).length  = rs.length := rfl
                    rw[rightlen]
                    omega


                  have n'cast : (rs.submoduleMap S.g).toFun (n+1) =
                               (rs.submoduleMap S.g).toFun n'.succ := by
                    apply congr_arg
                    apply Fin.eq_of_val_eq


                    have rightlen : (rs.submoduleMap S.g).length  = rs.length := rfl
                    simp[rightlen]

                    unfold Nat.cast
                    unfold NatCast.natCast
                    unfold Fin.instNatCast
                    unfold Fin.ofNat''
                    simp

                    have mas' : n < (rs.submoduleMap S.g).length + 1 := by
                      rw[rightlen]
                      rw[o]
                      omega


                    let need := Nat.mod_eq_of_lt mas'

                    simp[need]
                    have mas'' : n + 1 < (rs.submoduleMap S.g).length + 1 := by
                      rw[rightlen]
                      rw[o]
                      omega
                      --rw[rightlen]
                    --let need' := Nat.mod_eq_of_lt mas''
                    simp[Fin.add_def]
                    rw[rightlen]
                    exact Nat.succ_lt_succ_iff.mp mas''

                    --simp[HAdd.hAdd, Fin.val]





                    --rw[need]
                    --ring_nf

                    /-
                    apply Fin.eq_mk_iff_val_eq.mp ?h.a.a
                    rw[rightlen]
                    omega

                    apply Fin.eq_of_val_eq
                    simp
                    -/

                  rw[ncast]
                  rw[n'cast]
                  exact h


                  /-
                  ring_nf
                  --ring_nf at h
                  unfold Fin.castSucc at h
                  unfold Fin.succ at h
                  unfold Fin.castAdd at h
                  simp at h
                  -/

                exact False.elim (q hdif)
              · have hdif : (rs.submoduleMap S.g).toFun n' < (rs.submoduleMap S.g).toFun (n' + 1) := by
                  simp
                  have ncast : (rs.submoduleMap S.g).toFun n =
                              (rs.submoduleMap S.g).toFun n'.castSucc := by
                    --let neqiv : n = n'.castSucc := rfl
                    apply congr_arg
                    apply Fin.eq_of_val_eq
                    simp only [Fin.val_natCast, Fin.coe_castSucc, Nat.mod_succ_eq_iff_lt,
                      Nat.succ_eq_add_one]
                    let rightlen : (rs.submoduleMap S.g).length  = rs.length := rfl
                    rw[rightlen]
                    omega


                  have n'cast : (rs.submoduleMap S.g).toFun (n+1) =
                               (rs.submoduleMap S.g).toFun n'.succ := by
                    apply congr_arg
                    apply Fin.eq_of_val_eq


                    have rightlen : (rs.submoduleMap S.g).length  = rs.length := rfl
                    simp[rightlen]

                    unfold Nat.cast
                    unfold NatCast.natCast
                    unfold Fin.instNatCast
                    unfold Fin.ofNat''
                    simp


                    have mas' : n < (rs.submoduleMap S.g).length + 1 := by
                      rw[rightlen]
                      rw[o]
                      omega


                    let need := Nat.mod_eq_of_lt mas'

                    simp[need]
                    have mas'' : n + 1 < (rs.submoduleMap S.g).length + 1 := by
                      rw[rightlen]
                      rw[o]
                      omega

                    simp[Fin.add_def]
                    rw[rightlen]
                    exact Nat.succ_lt_succ_iff.mp mas''



                  rw[ncast]
                  rw[n'cast]
                  exact h
                exact hdif


            have q'' : (rs.submoduleMap S.g).toFun ((rs.submoduleMap S.g).length - 1) <
                      (rs.submoduleMap S.g).toFun ((rs.submoduleMap S.g).length) := by
              have leneq : (rs.submoduleMap S.g).length = rs.length := rfl
              simp_all



              --let something := (Ne.le_iff_lt q).1 stepo
              --let rightlen : (rs.submoduleMap S.g).length  = rs.length := rfl

            /-
            have qleft : (rs.submoduleComap S.f).toFun ((rs.submoduleComap S.f).length - 1) =
                      (rs.submoduleComap S.f).toFun ((rs.submoduleComap S.f).length) := by
              have leneq : (rs.submoduleComap S.f).length = rs.length := rfl

              simp_all

              sorry -/

            have nonempt : (rs.submoduleMap S.g).length > 0 := by exact Fin.pos n'
            rw[RelSeries.trimmed_length_eraseLast_of_lt nonempt q'']

            let rserasedLen : rs.eraseLast.length = n := by aesop

            let iherased := ih rs.eraseLast rserasedLen

            have makeIntoLemma : (rs.submoduleComap S.f).eraseLast.trimmed_length ≤
                                (rs.submoduleComap S.f).trimmed_length :=
            RelSeries.trimmed_length_eraseLast_le (rs.submoduleComap S.f) (by aesop)


            suffices n + 1 ≤ (rs.submoduleMap S.g).eraseLast.trimmed_length +
                             1 + (rs.submoduleComap S.f).eraseLast.trimmed_length by
              exact le_add_of_le_add_left this makeIntoLemma

            ring_nf

            let shouldProve := Nat.add_le_add_left iherased 1
            ring_nf at shouldProve
            exact shouldProve






  -- Not completed because it's not clear if this is necessary. Could be useful for the trimmed
  -- length api though

  /-
  lemma trimed_length_existence (rs : RelSeries (α := Submodule R M) (· ≤ ·)) {m : ℕ}
    (hm : m < rs.trimmed_length) : ∃ n : ℕ, rs.toFun n ≠ rs.toFun m := sorry


  open Classical in
  noncomputable
  def helper
    (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b)) (n : ℕ)
    (acc : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b))
    (inv1 : acc.head = rs n) (inv2 : n ≤ rs.length)
    : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b) :=
    match p : n with
    | 0   => acc
    | m+1 => if h : (rs m < rs n)
             then by
              have : rs m < acc.head := by aesop
              exact helper rs m (acc.cons (rs m) this) (by aesop) (Nat.le_of_succ_le inv2)

             else by
              have h' : rs m = rs n := by
                --let stepo := rs.step {val := m, isLt := inv2}
                have inv2' : m < rs.length := by aesop
                have : m % (rs.length + 1) = m := by
                  apply Nat.mod_eq_of_lt
                  exact Nat.lt_add_right 1 inv2
                simp_all

                let m' : Fin rs.length := {val := m, isLt := inv2'}
                let stepo := rs.step m'

                let mas : rs m ≤ rs n := by
                  have : rs m = rs m' := sorry
                  subst p
                  simp_all only [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one, ge_iff_le]

                  sorry


                  --Nat.mod_eq_of_lt
                  --sorry





                obtain q | q := le_iff_eq_or_lt.mp mas
                all_goals simp_all

              exact helper rs m acc (by aesop) (Nat.le_of_succ_le inv2)




  open Classical in
  noncomputable
  def RelSeries.induced_lt_relSeries_of_le_relSeries
    (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b))
    : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b) :=
    helper rs rs.length (RelSeries.singleton (· < ·) rs.last) (by aesop) (by aesop) -/




  /-
  lemma length_of_induced_relseries (rs : RelSeries (α := Submodule R M) (· ≤ ·)) :
   rs.induced_lt_relSeries_of_le_relSeries.length = rs.trimmed_length := by sorry -/
   /-simp[RelSeries.induced_lt_relSeries_of_le_relSeries, RelSeries.trimmed_length]--, go, RelSeries.cons_length]

   induction' o : rs.length with n ih generalizing rs
   · simp[go, helper]
   · simp[go, helper]
     split
     next h =>
      split
      next q =>
        /-
        This case shouldn't be possible, here we're essentially saying that we've just hit an element
        which is not equal to the last one. Potentially should change the definition to make that
        more transparent for proofs like this
        -/

      next q =>
      sorry
     next h =>
      sorry
    -/



  /-
  open Classical in
  noncomputable
  def induced_lt_relSeries_of_le_relSeries
    (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b))
    : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b) := by

    let ret : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b) :=  {
      length := RelSeries.trimmed_length rs
      toFun := fun n ↦ match n.val with
                | 0     => rs.toFun 0
                | (m+1) => by
                  -- Should follow from the definition of trimmed length
                  let existance : (∃ n : ℕ, rs.toFun ↑n ≠ rs.toFun ↑m) := sorry
                  let input := (Nat.find (p := fun (k : ℕ) ↦ rs.toFun k ≠ rs.toFun m)) existance
                  exact rs.toFun input
      step := by
        intro i
        simp
        split
        next k hi =>
          #check trimed_length_existence rs
          simp[hi, Nat.find_spec]


          sorry

        sorry
    }
    exact ret
  -/

  --#check ciSup_add_le


  /-
  So this is not true (or at least not obviously),
  -/
  /-
  synth SupSet ℕ
  theorem iSup_le_add {α : Type*} {ι ι': Sort*} [Nonempty ι] [Nonempty ι']
   [ConditionallyCompleteLattice α] [AddMonoid α] {f : ι → α} --[HAdd α α α] {f : ι → α}
   {g : ι' → α} {a : α} :
  iSup f + iSup g ≤ a ↔ ∀ (i: ι) (j : ι'), f i + g j ≤ a := by
  -/


    --simp_rw [iSup_add, add_iSup]
   --rw [iSup_congr (congrFun rfl)]
   --#check iSup_le_iff
   --#check iSup_add
   /-
   constructor
   ·
     sorry
   · intro fa

     sorry
    -/
    --sorry

  --#synth SupSet <| ℕ
  --#eval (⊥ : WithBot ℕ∞)

  /-
  There is a very similar result about ENNReal which would be potentially useful to generalize,
  I think I could port their proof over without too much difficutly, but finding an appropriate
  geberalization for them both is proving to be kind of annoying.

  There is of course also the conditional lattice business which has similar lemmas assuming the
  addition is in a group and that the order has a kind of reverse cancellative property wrt to the
  addition, but it's unclear how to generalise this to the case we want, especially considering
  that in our application, we're not actually working with a monoid which embeds into it's
  "groupification", since a monoid needs to be cancellative for this to be the case which gets
  messed around by adding infinities
  -/
  theorem iSup_le_add {ι ι': Sort*} [Nonempty ι] [Nonempty ι']
   {f : ι → WithBot ℕ∞} {g : ι' → WithBot ℕ∞} {a : WithBot ℕ∞} :
  iSup f + iSup g ≤ a ↔ ∀ (i: ι) (j : ι'), f i + g j ≤ a := by
    apply Iff.intro
    · intro a_1 i j

      sorry
    · intro a_1

      sorry
    --simp[WithBot.instSupSet, ConditionallyCompleteLattice.toSupSet]


  /-
  lemma exists_series_with_trimmed_length (rs : RelSeries (α := Submodule R M) (· ≤ ·))
    {m : ℕ} (hrs : rs.trimmed_length = m.succ) :
    ∃ rs' : RelSeries (α := Submodule R M) (· ≤ ·), rs'.trimmed_length = m := by
    induction' o : rs.trimmed_length with n ih generalizing rs
    · aesop
    · simp_all only [Nat.succ_eq_add_one, add_left_inj, add_right_eq_self, one_ne_zero, not_isEmpty_of_nonempty,
        IsEmpty.exists_iff, false_implies, implies_true]
      subst hrs

      sorry
  -/


  -- This might be doable with induction and snoc, then we don't need to explicitly define our helper
  -- function with all of its annoying index gymnastics

  /-

  Whilst I think such a lemma is a good idea to develop, I think it's more promising to try to
  work through other means

  #check RelSeries
  def RelSeries.normal_form {α : Type*} {r : Rel α α} (rs : RelSeries r) :
    (∃ a : α, rs = RelSeries.singleton r a) ∨
    (∃ rs' : RelSeries r, ∃ a : α, ∃ ha : r a rs'.head, rs = rs'.cons a ha)
    := by
    let rslist : List α := rs.toList
    let rslistchain := rs.toList_chain'

    #check RelSeries.fromListChain'
    sorry

    -/

      /-
      match o : rs.length with
      | 0 =>
        --have : rs = RelSeries.singleton r rs.head := by sorry
        apply Or.inl
        use rs.head
        unfold RelSeries.singleton

        sorry
      | m+1 =>
        apply Or.inr
        --have rs.length ≠
        use rs.tail (by aesop)
        use rs.head
        let z : Fin rs.length := {val := 0, isLt := by aesop}
        use rs.step z

        -/



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
  /-
  def RelSeries.concat {α : Type*} {r : Rel α α} (rs : RelSeries r) (rs' : RelSeries r)
    (headtail : r rs.last rs'.head) : RelSeries r := {
      length := rs.length + rs'.length
      toFun := fun i ↦ if i ≤ rs.length then rs i else rs' (i - rs.length)
      step := by
        intro i
        simp_all
        split
        sorry
        sorry
    }
  -/
  /-
  #check RelSeries.fromListChain'
  def RelSeries.fromList_cons {α : Type*} {r : Rel α α} (xs : List α) (x_ne_nil : xs ≠ [])
    (cx : List.Chain' r xs) {hdx : α} {ys : List α} (hxs : xs = List.cons hdx ys) : RelSeries.fromListChain' xs x_ne_nil cx = RelSeries.cons hdx
  -/

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




  theorem checking (a : Submodule R M) (l : ¬ a = ⊥) : ⊥ < a := Ne.bot_lt' fun a_1 ↦
    l (id (Eq.symm a_1))

  /-

  It would be good to have a less stupid definition here

  open Classical in
  noncomputable
  def RelSeries.topbot --{α : Type*} [Preorder α] [Bot α] [Top α]
                       (rs : RelSeries (α := Submodule R M) (· < ·)) : RelSeries (α := Submodule R M) (· < ·) :=
  if hh : rs.head = ⊥
  then (if th : rs.last = ⊤ then rs else rs.snoc ⊤ (Ne.lt_top' (id (Ne.symm th))))
  else (if th : rs.last = ⊤ then rs.cons ⊥ (Ne.bot_lt' fun a_1 ↦ hh (id (Eq.symm a_1))) else rs)
-/




    theorem Module.length_additive
    {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
      Module.length R S.X₂ = Module.length R S.X₁ + Module.length R S.X₃ := by


    simp only [length, krullDim, le_antisymm_iff, iSup_le_iff]

    constructor
    · intro rs

      let trimmedProof := trimmed_length_additive hS rs


      let trimleft := Module.length_ge_trimmed_length (RelSeries.submoduleComap rs S.f)
      let trimright := Module.length_ge_trimmed_length (RelSeries.submoduleMap rs S.g)

      let inbet : (RelSeries.submoduleComap rs S.f).trimmed_length +
        (RelSeries.submoduleMap rs S.g).trimmed_length
        ≤ Module.length R S.X₁ + Module.length R S.X₃ := by exact add_le_add trimleft trimright


      apply le_trans (b := ↑((RelSeries.submoduleComap rs S.f).trimmed_length + (RelSeries.submoduleMap rs S.g).trimmed_length))

      apply Nat.mono_cast
      rw[Nat.add_comm] at trimmedProof
      exact trimmedProof
      exact inbet



    · rw[iSup_le_add]
      --#check ciSup_add_ciSup_le
      --apply (ciSup_add_ciSup_le )
      intro rstemp rstemp'
      obtain ⟨rs, hrs⟩ := RelSeries.chain_le_bot_top rstemp
      obtain ⟨rs', hrs'⟩ := RelSeries.chain_le_bot_top rstemp'


      let gInv : RelSeries (fun (a : Submodule R S.X₂) (b : Submodule R S.X₂) => a < b) :=
        RelSeries.submoduleComap_surjective hS.moduleCat_surjective_g rs'


      let fIm : RelSeries (fun (a : Submodule R S.X₂) (b : Submodule R S.X₂) => a < b) :=
        RelSeries.submoduleMap_injective hS.moduleCat_injective_f rs


      have connect : fIm.last = gInv.head := by
        let gInvheadker : gInv.head = LinearMap.ker S.g := by
          simp[gInv, RelSeries.submoduleComap_surjective, RelSeries.head]
          let obv : rs'.toFun 0 = ⊥ := by aesop
          rw[obv]
          exact rfl
        let fImLastRange : fIm.last = LinearMap.range S.f := by
          simp[fIm, RelSeries.submoduleMap_injective, RelSeries.last]
          let obv : (rs.toFun (Fin.last rs.length)) = ⊤ := by aesop
          rw[obv]
          exact Submodule.map_top S.f


        simp_all only [fIm, fImLastRange, gInv, gInvheadker]
        exact CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hS.exact
      · let smashfg := RelSeries.smash fIm gInv connect
        have : smashfg.length ≤ (@iSup (WithBot ℕ∞) (LTSeries (Submodule R ↑S.X₂)) WithBot.instSupSet fun p ↦ ↑p.length) := by
          exact le_iSup_iff.mpr fun b a ↦ a smashfg

        let this' : smashfg.length = rs.length + rs'.length := by aesop
        let step1 : rstemp.length + rstemp'.length ≤ @Nat.cast (WithBot ℕ∞) Semiring.toNatCast smashfg.length := by
          rw[this']
          simp
          refine add_le_add ?h₁ ?h₂
          simp[hrs.1]
          simp[hrs'.1]
        exact le_trans step1 this

end FL
