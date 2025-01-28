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
           (fl : IsFiniteLength R M)

  open Classical in
  noncomputable
  def Module.length'' : ℕ :=
    Nat.find (p := fun (n : ℕ) ↦
      ∃ s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤ ∧ s.length = n) <| by
    rw[isFiniteLength_iff_exists_compositionSeries] at fl
    obtain ⟨s, hs⟩ := fl
    use s.length
    aesop


  #check krullDim
  variable (R M) in
  open Classical in
  noncomputable
  def Module.length' := krullDim (α := Submodule R M)

  noncomputable
  def Module.length : ℕ :=
    sSup {n : ℕ | (∃ rs : RelSeries (α := Submodule R M) (· < ·),
          rs.head = ⊥ ∧ rs.last = ⊤ ∧ rs.length = n)}

  #check Order.krullDim

  variable (M) in
  open Classical in
  noncomputable
  def Module.length'' : ℕ :=
  ⨆ (rs : RelSeries (α := Submodule R M) (· < ·)), rs.length

  #check Module.length' M = Module.length'' M

  -/


  --theorem sanitycheck : length' M = 2 := sorry

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

  def CompositionSeries.relSeries_of_injective {f : M →ₗ[R] M'} (hf : Function.Injective f)
      (s : CompositionSeries (Submodule R M)) :
      RelSeries (fun (a : Submodule R M') (b : Submodule R M') => a < b) := {
        length := s.length
        toFun := fun n => Submodule.map f (s.toFun n)
        step := by {
          let proof := Submodule.map_strictMono_of_injective hf
          intro i
          apply proof
          exact CompositionSeries.lt_succ s i
        }
      }

  def CompositionSeries.relSeries_of_surjective {f : M →ₗ[R] M'} (hf : Function.Surjective f)
      (s : CompositionSeries (Submodule R M')) :
      RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b) := {
        length := s.length
        toFun := fun n => Submodule.comap f (s.toFun n)
        step := by {
          let proof := Submodule.comap_strictMono_of_surjective hf
          intro i
          apply proof
          exact CompositionSeries.lt_succ s i
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




open CompositionSeries in
  theorem Module.length_ge_relSeries
    (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b))
    : length fl ≥ rs.length := by
      rw[isFiniteLength_iff_isNoetherian_isArtinian] at fl
      rw[←monotone_stabilizes_iff_noetherian] at fl

      --apply Module.length_maximal
      sorry



  def RelSeries.submoduleMap (rs : RelSeries (α := Submodule R M) (· < ·))
    (f : M →ₗ[R] M') : RelSeries (α := Submodule R M') (· ≤ ·) :=
      RelSeries.map rs {toFun := Submodule.map f, map_rel' := fun a ↦ Submodule.map_mono (a.le)}

  def RelSeries.submoduleComap (rs : RelSeries (α := Submodule R M') (· < ·))
    (f : M →ₗ[R] M') : RelSeries (α := Submodule R M) (· ≤ ·) :=
      RelSeries.map rs {toFun := Submodule.comap f, map_rel' := fun a ↦ Submodule.comap_mono (a.le)}



  -- Helper function for trimmed length which computes the number of <'s occuring in a leseries
  open Classical in
  noncomputable
  def go (rs : RelSeries (α := Submodule R M) (· ≤ ·)) (n : ℕ) : ℕ :=
    match n with
      | 0     => 0
      | (m+1) => if rs.toFun n = rs.toFun m then go rs m else 1 + go rs m

  noncomputable
  def RelSeries.trimmed_length (rs : RelSeries (α := Submodule R M) (· ≤ ·)) : ℕ :=
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
          let cont := eqs (m+1) (Nat.le_refl (m + 1))
          let cont' := eqs m (Nat.le_add_right m 1)
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
          let eqssm := eqs (m+1) (Nat.le_of_eq (id (Eq.symm rfl)))
          let eqsm := eqs m (by aesop)
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


  theorem RelSeries.trimmed_length_exists_ne {rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b)}
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
      let j : f ⁻¹' S = f ⁻¹' S' := by aesop
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


  theorem RelSeries.submodule_comap_lt_of_map_eq_exact {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS : S.ShortExact)
    (rs : RelSeries (α := Submodule R S.X₂) (· < ·)) (i : Fin rs.length)
    (p : (rs.submoduleMap S.g).toFun i = (rs.submoduleMap S.g).toFun (i+1))
    : (rs.submoduleComap S.f).toFun i < (rs.submoduleComap S.f).toFun (i+1) := by

      let kernelInt : LinearMap.ker S.g ⊓ (rs.toFun i) < LinearMap.ker S.g ⊓ (rs.toFun (i+1)) := by
       let p' : Submodule.map S.g (rs.toFun i.castSucc) = Submodule.map S.g (rs.toFun i.succ) := by aesop
       let ans := kernel_intersection (rs.step i) p'
       aesop

      let exactness : LinearMap.ker S.g = LinearMap.range S.f := by
        let proof := CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hS.exact
        exact id (Eq.symm proof)

      rw[exactness] at kernelInt

      simp_all

      let intLem (k : Fin (rs.length + 1)) : (rs.submoduleComap S.f).toFun k = Submodule.comap S.f (LinearMap.range S.f ⊓ rs.toFun k) := by aesop
      rw[intLem i.castSucc, intLem i.succ]

      let lem := Set.preimage_mono_of_range_intersection kernelInt (le_of_lt (rs.step i))
      simp
      let comap_range : Submodule.comap S.f (LinearMap.range S.f) = ⊤ := by aesop
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

      let intLem (k : Fin (rs.length + 1)) : (rs.submoduleMap S.g).toFun k = Submodule.map S.g (rs.toFun k) := by aesop
      rw[intLem i.castSucc, intLem i.succ]

      exact kernel_intersection' (rs.step i) imInt




    theorem RelSeries.trimmed_length_eraseLast_eq
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


    theorem RelSeries.trimmed_length_eraseLast_le
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
            rw[RelSeries.trimmed_length_eraseLast_eq obv qcoe]

            let rserasedLen : rs.eraseLast.length = n := by aesop

            let iherased := ih rs.eraseLast rserasedLen


            --let q' : (rs.submoduleMap S.g).toFun n' = (rs.submoduleMap S.g).toFun (n' + 1) := q
            let leftlt' := RelSeries.submodule_comap_lt_of_map_eq_exact hS rs n' q

            let leftlt : (rs.submoduleComap S.f).toFun ((rs.submoduleComap S.f).length - 1)
            < (rs.submoduleComap S.f).toFun (rs.submoduleComap S.f).length := by
              let leftlen : (rs.submoduleComap S.f).length = rs.length := rfl
              simp_all[leftlen]



            let leftlength : (rs.submoduleComap S.f).length = n+1 := by aesop

            let nonempt : (rs.submoduleComap S.f).length > 0 := by aesop

            --#check RelSeries.trimmed_length_eraseLast_le
            rw[RelSeries.trimmed_length_eraseLast_le nonempt leftlt]
            exact Nat.add_le_add_right iherased 1


          · let q' : (rs.submoduleMap S.g).toFun n < (rs.submoduleMap S.g).toFun (n + 1) := by
              let leq := (rs.submoduleMap S.g).step n'
              rw [@le_iff_eq_or_lt] at leq
              simp
              let qdif : ¬(rs.submoduleMap S.g).toFun n' = (rs.submoduleMap S.g).toFun (n' + 1) := q

              simp at qdif
              obtain h | h := leq

              · let hdif : (rs.submoduleMap S.g).toFun n' = (rs.submoduleMap S.g).toFun (n' + 1) := by
                  simp
                  let ncast : (rs.submoduleMap S.g).toFun n =
                              (rs.submoduleMap S.g).toFun n'.castSucc := by
                    --let neqiv : n = n'.castSucc := rfl
                    apply congr_arg
                    apply Fin.eq_of_val_eq
                    simp only [Fin.val_natCast, Fin.coe_castSucc, Nat.mod_succ_eq_iff_lt,
                      Nat.succ_eq_add_one]
                    let rightlen : (rs.submoduleMap S.g).length  = rs.length := rfl
                    rw[rightlen]
                    omega


                  let n'cast : (rs.submoduleMap S.g).toFun (n+1) =
                               (rs.submoduleMap S.g).toFun n'.succ := by
                    apply congr_arg
                    apply Fin.eq_of_val_eq


                    let rightlen : (rs.submoduleMap S.g).length  = rs.length := rfl
                    simp[rightlen]

                    unfold Nat.cast
                    unfold NatCast.natCast
                    unfold Fin.instNatCast
                    unfold Fin.ofNat''
                    simp


                    let mas' : n < (rs.submoduleMap S.g).length + 1 := by
                      rw[rightlen]
                      rw[o]
                      omega


                    let need := Nat.mod_eq_of_lt mas'

                    simp[need]
                    let mas'' : n + 1 < (rs.submoduleMap S.g).length + 1 := by
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
              · let hdif : (rs.submoduleMap S.g).toFun n' < (rs.submoduleMap S.g).toFun (n' + 1) := by
                  simp
                  let ncast : (rs.submoduleMap S.g).toFun n =
                              (rs.submoduleMap S.g).toFun n'.castSucc := by
                    --let neqiv : n = n'.castSucc := rfl
                    apply congr_arg
                    apply Fin.eq_of_val_eq
                    simp only [Fin.val_natCast, Fin.coe_castSucc, Nat.mod_succ_eq_iff_lt,
                      Nat.succ_eq_add_one]
                    let rightlen : (rs.submoduleMap S.g).length  = rs.length := rfl
                    rw[rightlen]
                    omega


                  let n'cast : (rs.submoduleMap S.g).toFun (n+1) =
                               (rs.submoduleMap S.g).toFun n'.succ := by
                    apply congr_arg
                    apply Fin.eq_of_val_eq


                    let rightlen : (rs.submoduleMap S.g).length  = rs.length := rfl
                    simp[rightlen]

                    unfold Nat.cast
                    unfold NatCast.natCast
                    unfold Fin.instNatCast
                    unfold Fin.ofNat''
                    simp


                    let mas' : n < (rs.submoduleMap S.g).length + 1 := by
                      rw[rightlen]
                      rw[o]
                      omega


                    let need := Nat.mod_eq_of_lt mas'

                    simp[need]
                    let mas'' : n + 1 < (rs.submoduleMap S.g).length + 1 := by
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
                exact hdif


            let q'' : (rs.submoduleMap S.g).toFun ((rs.submoduleMap S.g).length - 1) <
                      (rs.submoduleMap S.g).toFun ((rs.submoduleMap S.g).length) := by
              let stepo := (rs.submoduleMap S.g).step n'
              --let something := (Ne.le_iff_lt q).1 stepo
              --let rightlen : (rs.submoduleMap S.g).length  = rs.length := rfl

              sorry

            let qright : (rs.submoduleComap S.f).toFun ((rs.submoduleComap S.f).length - 1) <
                      (rs.submoduleComap S.f).toFun ((rs.submoduleComap S.f).length) := sorry

            let nonempt : (rs.submoduleMap S.g).length > 0 := by exact Fin.pos n'
            rw[RelSeries.trimmed_length_eraseLast_le nonempt q'']

            let rserasedLen : rs.eraseLast.length = n := by aesop

            let iherased := ih rs.eraseLast rserasedLen

            let makeIntoLemma : (rs.submoduleComap S.f).eraseLast.trimmed_length ≤
                                (rs.submoduleComap S.f).trimmed_length := by
              let proof := (rs.submoduleComap S.f).trimmed_length_eraseLast_le nonempt qright
              omega

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
  open Classical in
  noncomputable
  def induced_lt_relSeries_of_le_relSeries
    (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b))
    : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b) := {
      length := RelSeries.trimmed_length rs
      toFun := fun n ↦ match n.val with
                | 0     => rs.toFun 0
                | (m+1) => by
                  -- Should follow from the definition of trimmed length
                  let existance : (∃ n : ℕ, rs.toFun ↑n ≠ rs.toFun ↑m) := sorry
                  let input := (Nat.find (p := fun (k : ℕ) ↦ rs.toFun k ≠ rs.toFun m)) existance
                  exact rs.toFun input
      step := sorry
    }
  -/

  /-
  This proof should go something like this: take rs some RelSeries. We case match on whether every
  inequality in rs is maximal. If so, then rs must be a composition series and we're done by
  Jordan Holder. If not, then we must have that there is somewhere where our series can split.

  In this second case, I think we do induction. We want to prove if there exists some non maximal
  guy, then trimmed length of rs is less than the length of the module. For zero case, I think we're
  done trivially. For inductive case, we assume this holds for all rs of length n. Then, for n+1,
  take the point where we have a non-maximal inequality. We should be able to show we can split this
  into two inequalities.

  Hmm. Idea is if there exists such a non-maximal inequality, we can construct a sequence which
  clearly has greater length.



  -/
  theorem Module.length_ge_trimmed_length
  (rs : RelSeries fun (a : Submodule R M) (b : Submodule R M) => a ≤ b)
   : RelSeries.trimmed_length rs ≤ Module.length fl := by

    --simp[RelSeries.trimmed_length]

    /-
    THIS PROOF IS A MISTAKE THAT SHOULDN'T BE REPEATED. THE TRIMMED LENGTH IS DEFINED IN TERMS OF
    RS.LENGTH, NOT THE LENGTH OF THE MODULE, SO THERE'S NO WAY TO PROCEEED USING THIS PROOF
    TECHNIQUE OF TRYING TO DO INDUCTION WITH ERASELAST BECAUSE THAT INEQUALITY MAY VERY WELL BE
    MAXIMAL

    induction' o : rs.length with n ih generalizing rs
    · simp[RelSeries.trimmed_length]
      rw[o]
      simp[go]
    · let erlen : rs.eraseLast.length = n := by aesop
      let ih' := ih rs.eraseLast erlen
      --#check rs.trimmed_length_eraseLast_le
      let succase : rs.length > 0 := by aesop
      obtain h | h := em <| rs.toFun ↑rs.length = rs.toFun (rs.length - 1)
      · let ereq := rs.trimmed_length_eraseLast_eq succase h
        rw[ereq]
        exact ih'
      · let h' : rs.toFun (rs.length - 1) < rs.toFun rs.length := sorry
        let erlt := rs.trimmed_length_eraseLast_le succase h'
        rw[erlt]
    -/




        sorry
      /-
      simp[go]
      split
      next h_1 =>
        let erlen : rs.eraseLast.length = n := by aesop
        let ih' := ih rs.eraseLast erlen
        let mas : go rs n = go rs.eraseLast n := by
          #check rs.trimmed_length_eraseLast_le
          apply go_equiv
          · omega
          · omega
          · intro i ltn

            sorry


        rw[mas]
        exact ih'
      next h_1 =>
        sorry
      -/

    /-
    simp[RelSeries.trimmed_length]
    rw[isFiniteLength_iff_exists_compositionSeries] at fl
    obtain ⟨cs, hcs⟩ := fl

    induction' h : rs.length with n ih generalizing rs
    · exact StrictMono.minimal_preimage_bot (fun ⦃a b⦄ a ↦ a) rfl (length fl)
    · simp[go]
      split
      · next h_1 =>
        let mas : rs.eraseLast.length = n := by aesop
        let ihel := ih rs.eraseLast mas
        let bigstep : go rs.eraseLast n = go rs n := sorry
        rw[← bigstep]
        exact ihel
      · next h_1 =>
          let mas : rs.eraseLast.length = n := by aesop
          let ihel := ih rs.eraseLast mas
          let bigstep : go rs.eraseLast n = go rs n := sorry
          rw[← bigstep]
          rw[Module.length_witness fl cs hcs]


          /-
          Here, we need to somehow use the fact that rs.toFun n < rs.toFun (n+1). We'd really like to
          case match on whether this is maximal or not.
          -/
          sorry
    -/







    theorem Module.length_additive
    {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS : S.ShortExact)
      (fl1 : IsFiniteLength R S.X₁) (fl2 : IsFiniteLength R S.X₂) (fl3 : IsFiniteLength R S.X₃):
      Module.length fl2 = Module.length fl1 + Module.length fl3 := by

    rw [Nat.le_antisymm_iff]
    rw[isFiniteLength_iff_exists_compositionSeries] at fl1 fl2 fl3

    choose s1 hs1 using fl1
    choose s2 hs2 using fl2
    choose s3 hs3 using fl3

    rw[Module.length_witness fl1 s1 hs1]
    rw[Module.length_witness fl2 s2 hs2]
    rw[Module.length_witness fl3 s3 hs3]

    constructor
    · let trimmedProof := trimmed_length_additive hS s2.lt_series
      let s2mas : s2.lt_series.length = s2.length := rfl
      rw[s2mas] at trimmedProof

      let detrimg := RelSeries.trimmed_length_leq_length (s2.lt_series.submoduleMap S.g)
      let detrimf := RelSeries.trimmed_length_leq_length (s2.lt_series.submoduleComap S.f)


      let trimleft := Module.length_ge_trimmed_length fl1 (s2.lt_series.submoduleComap S.f)
      let trimright := Module.length_ge_trimmed_length fl3 (s2.lt_series.submoduleMap S.g)

      rw[Module.length_witness fl1 s1 hs1] at trimleft
      rw[Module.length_witness fl3 s3 hs3] at trimright

      let inbet : (s2.lt_series.submoduleComap S.f).trimmed_length +
        (s2.lt_series.submoduleMap S.g).trimmed_length
        ≤ s1.length + s3.length := by exact Nat.add_le_add trimleft trimright

      apply Nat.le_trans (m := (s2.lt_series.submoduleComap S.f).trimmed_length +
        (s2.lt_series.submoduleMap S.g).trimmed_length)

      rw[Nat.add_comm] at trimmedProof
      exact trimmedProof
      exact inbet

      --  "Easy" direction - just take composition series for M' and M'' and stick them together
    · let gInv : RelSeries (fun (a : Submodule R S.X₂) (b : Submodule R S.X₂) => a < b) :=
        CompositionSeries.relSeries_of_surjective hS.moduleCat_surjective_g s3


      let fIm : RelSeries (fun (a : Submodule R S.X₂) (b : Submodule R S.X₂) => a < b) :=
        CompositionSeries.relSeries_of_injective hS.moduleCat_injective_f s1


      have connect : fIm.last = gInv.head := by
        let gInvheadker : gInv.head = LinearMap.ker S.g := by
          simp[gInv, CompositionSeries.relSeries_of_surjective, RelSeries.head]
          let obv : s3.toFun 0 = ⊥ := by aesop
          rw[obv]
          exact rfl
        let fImLastRange : fIm.last = LinearMap.range S.f := by
          simp[fIm, CompositionSeries.relSeries_of_injective, RelSeries.last]
          let obv : (s1.toFun (Fin.last s1.length)) = ⊤ := by aesop
          rw[obv]
          exact Submodule.map_top S.f


        simp_all only [fIm, fImLastRange, gInv, gInvheadker]
        obtain ⟨left, right⟩ := hs1
        obtain ⟨left_1, right_1⟩ := hs2
        obtain ⟨left_2, right_2⟩ := hs3
        exact CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hS.exact

      let smashfg := RelSeries.smash fIm gInv connect

      /-
      At this point, we can also just prove directly that the thing we get is a composition series.
      -/

      /-
      let testing : smashfg.IsCompositionSeries := by
        simp[RelSeries.IsCompositionSeries]
        constructor
        · --have hs11 := hs1.1
          have fbot := Submodule.map_bot S.f
          simp[smashfg, fbot]
          have rew : fIm.head = Submodule.map S.f s1.head := rfl
          rw[rew, hs1.1]
          exact fbot
        · constructor
          · have gtop := Submodule.comap_top S.g
            simp[smashfg]
            have rew : gInv.last = Submodule.comap S.g s3.last := rfl
            rw[rew, hs3.2]
            exact gtop
          · intro i
            simp[JordanHolderModule.instJordanHolderLattice]

            sorry
            --constructor
            --· exact smashfg.step i
            --· intro L bet1 bet2
        -/



      let combined := Module.length_ge_relSeries fl2 smashfg


      rw[← Module.length_witness fl2 s2 hs2]
      exact combined

end FL
