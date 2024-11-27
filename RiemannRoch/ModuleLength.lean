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
  def Module.length : ℕ :=
    Nat.find (p := fun (n : ℕ) ↦
      ∃ s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤ ∧ s.length = n) <| by
    rw[isFiniteLength_iff_exists_compositionSeries] at fl
    obtain ⟨s, hs⟩ := fl
    use s.length
    aesop

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

  --theorem Module.length_maximal
  /-
  noncomputable def ModuleLength :
      WithBot (WithTop ℕ) :=
    krullDim (Submodule R M)
  -/
  --def subModule_of_subset (L : Module R M)


  def CompositionSeries.relSeries_of_injective {f : M →ₗ[R] M'} (hf : Function.Injective f)
      (s : CompositionSeries (Submodule R M)) :
      RelSeries (fun (a : Submodule R M') (b : Submodule R M') => a < b) := {
        length := s.length
        toFun := fun n => Submodule.map f (s.toFun n) --LinearMap.submoduleImage (f.domRestrict (s.toFun n)) (s.toFun n)
        step := by {
          let proof := Submodule.map_strictMono_of_injective hf
          intro i
          apply proof
          exact CompositionSeries.lt_succ s i
          --exact Submodule.map_strictMono_of_injective
        }
      }

  def CompositionSeries.relSeries_of_surjective {f : M →ₗ[R] M'} (hf : Function.Surjective f)
      (s : CompositionSeries (Submodule R M')) :
      RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b) := {
        length := s.length
        toFun := fun n => Submodule.comap f (s.toFun n) --LinearMap.submoduleImage (f.domRestrict (s.toFun n)) (s.toFun n)
        step := by {
          let proof := Submodule.comap_strictMono_of_surjective hf
          intro i
          apply proof
          exact CompositionSeries.lt_succ s i
        }
      }


def RelSeries.IsCompositionSeries (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b)) : Prop :=
  rs.head = ⊥ ∧ rs.last = ⊤ ∧ ∀ (i : Fin rs.length), JordanHolderLattice.IsMaximal (rs.toFun i.castSucc) (rs.toFun i.succ)


def RelSeries.composition_series_of {rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b)}
  (cs : RelSeries.IsCompositionSeries rs) : CompositionSeries (Submodule R M) := {
    length := rs.length
    toFun := rs.toFun
    step := cs.2.2
  }

  def CompositionSeries.lt_series (cs : CompositionSeries (Submodule R M))
  : @RelSeries (Submodule R M) (· < ·) := by
  let inst : Lattice (Submodule R M) := by infer_instance
  let inst' : JordanHolderLattice (Submodule R M) := by infer_instance
  let p : @JordanHolderLattice.IsMaximal (Submodule R M) inst inst' ≤ fun a b ↦ a < b := by
    apply JordanHolderLattice.lt_of_isMaximal
  exact RelSeries.ofLE cs p
/-
def CompositionSeries.relSeries_of (cs : CompositionSeries (Submodule R M)) :
  RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b) := {
    length := cs.length
    toFun := cs.toFun
    step := fun i ↦ JordanHolderLattice.lt_of_isMaximal (cs.step i) --fun x y ↦ (JordanHolderLattice.lt_of_isMaximal cs.step) x y
  }
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
  (maximal : ∀ xs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b), rs.length ≥ xs.length)
  : rs.head = ⊥ ∧ rs.last = ⊤ := by
  apply by_contradiction
  intro absurdity
  rw [Mathlib.Tactic.PushNeg.not_and_or_eq] at absurdity
  obtain h | h := absurdity

  let cont : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b) := {
    length := rs.length + 1
    toFun := fun i ↦
      match i.val with
      | 0 => ⊥
      | m+1 => rs.toFun m
    step := fun i ↦ by
      simp
      split
      · next r s t =>
        let h' : rs.toFun 0 ≠ ⊥ := by aesop
        rw [@lt_iff_le_and_ne]
        constructor
        exact OrderBot.bot_le (rs.toFun i)
        let t' : i = 0 := by aesop
        rw[t']
        exact h'.symm
      · next r s t =>
        let s' : Fin (rs.length) := {
          val := s
          isLt := sorry
        }
        let t' : i = s.succ := sorry
        rw[t']
        let proof := rs.step s'
        let mas : s = s' := by aesop
        rw[mas]



        --exact rs.step (@Nat.cast (Fin (rs.length)) Fin.instNatCast s)
        sorry
  }


  let bull := maximal cont
  let m : cont.length = rs.length + 1 := rfl
  rw[m] at bull
  let absolutebull : 0 ≥ 1 := Nat.le_of_add_le_add_left bull
  exact Nat.not_succ_le_zero 0 absolutebull

  let cont : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b) := {
    length := rs.length + 1
    toFun := fun i ↦ if i.val = rs.length + 1 then ⊤ else rs.toFun i
    step := sorry
  }
  let bull := maximal cont
  let m : cont.length = rs.length + 1 := rfl
  rw[m] at bull
  let absolutebull : 0 ≥ 1 := Nat.le_of_add_le_add_left bull
  exact Nat.not_succ_le_zero 0 absolutebull

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


  /-
  I think the idea here should be you case match on whether rs is a composition series or not.
  If it is one, then you're done by Jordan Holder.

  If it's not, then there must be some place where the quotient is non simple, so this part of
  the series factors into more maps, increasing the length and giving a contradiction.
  -/
  open CompositionSeries in
  theorem Module.length_ge_relSeries
    (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b))
    : Module.length fl ≥ rs.length := by
      simp
      --rw[isFiniteLength_iff_exists_compositionSeries] at fl

      simp[Module.length]
      intro m mnotrsmax cs csbot cstop maximal
      #check jordan_holder
      #check em
      obtain h | h := em (RelSeries.IsCompositionSeries rs)
      let cs' := RelSeries.composition_series_of h
      --obtain h' | h' := em (RelSeries.head cs' = ⊥ ∧ RelSeries.last cs' = ⊤)
      let eq : cs.head = cs'.head := by
        rw[csbot]
        #check h.1
        let obv : cs'.head = rs.head := by aesop
        rw[obv]
        rw[h.1]
      let eq' : RelSeries.last cs = RelSeries.last cs' := by
        rw[cstop]
        let obv : cs'.last = rs.last := by aesop
        rw[obv]
        rw[h.2.1]
      obtain ⟨j, jh⟩ := jordan_holder cs cs' eq eq'
      -- should just be a theorem for this
      let obv : cs.length = cs'.length := by
        let card := Equiv.cardinal_eq j
        simp at card
        exact card
      let bydef : cs'.length = rs.length := by aesop
      rw[bydef] at obv
      rw[maximal] at obv
      rw [@Nat.lt_iff_le_and_ne] at mnotrsmax
      exact mnotrsmax.2 obv
      simp[RelSeries.IsCompositionSeries] at h
      -- Here we have a slight problem; we need to suppose the head of rs is ⊥ and last is ⊤, which
      -- means we may not have gained anything from changing the definition of isCompositionSeries.

      obtain h' | h' := em (RelSeries.head rs = ⊥ ∧ RelSeries.last rs = ⊤)

      -- We probably want to do a kind of induction here. The argument is that since our relseries
      -- (with head and last at ⊥ and ⊤) is not a composition series, it follows that there is some
      -- part of the sequence which we can break up. But this means that there is always a sequence
      -- longer than rs

      -- I think without doing induction here though, we're going to just keep case matching on the
      -- thing we produce being a composition series forever.

      -- The question is, what do we actually want to prove here? We probably want to construct the
      -- chain of these things and then use finite length to show it's finite


      obtain ⟨guy, hguy⟩ := h h'.1 h'.2
      simp[JordanHolderLattice.IsMaximal] at hguy
      simp[CovBy] at hguy
      obtain ⟨mid, hmid⟩ := hguy (rs.step guy)
      -- We probably need inducion here or something




      sorry

      sorry



  def RelSeries.submoduleMap (rs : RelSeries (α := Submodule R M) (· < ·))
    (f : M →ₗ[R] M') : RelSeries (α := Submodule R M') (· ≤ ·) :=
      RelSeries.map rs {toFun := Submodule.map f, map_rel' := fun a ↦ Submodule.map_mono (a.le)}

  def RelSeries.submoduleComap (rs : RelSeries (α := Submodule R M') (· < ·))
    (f : M →ₗ[R] M') : RelSeries (α := Submodule R M) (· ≤ ·) :=
      RelSeries.map rs {toFun := Submodule.comap f, map_rel' := fun a ↦ Submodule.comap_mono (a.le)}


  -- This feels unnecessarily difficult, I think it would be more sensible to index these things
  -- by natural numbers.

  -- NOT BEING USED CURRENTLY, PROBABLY NOT NECESSARY
  def RelSeries.delete {α : Type*} {r : Rel α α} {trans : Transitive r} (rs : RelSeries r)
    (i : Fin (rs.length)) : RelSeries r := if k : rs.length = 0 then rs else {
      length := rs.length - 1
      toFun := fun j ↦ if i < j then rs.toFun j else rs.toFun (j+1)
      step := by
        intro j
        obtain h | h := em (i < j.castSucc)
        let mover : i < j.succ := by sorry
        simp[h, mover]
        let j' : Fin (rs.length) := {val := j.val, isLt := by sorry}
        --#check j.castAdd 1

        --exact rs.step (@Nat.cast (Fin (rs.length + 1)) Fin.instNatCast ↑j)
        #check @Nat.cast (Fin rs.length)
        let obv : NeZero rs.length := {out := k}

        let proof := rs.step (@Nat.cast (Fin rs.length) Fin.instNatCast j)


        sorry
        sorry

        --aesop

    }


    /-by
        let mr : ∀ {a b : Submodule R ↑S.X₂}, JordanHolderLattice.IsMaximal a b → Submodule.map S.g a ≤ Submodule.map S.g b := by
          intro a b m
          let lt := JordanHolderLattice.lt_of_isMaximal m
          refine Submodule.map_mono ?_
          exact le_of_lt lt
        exact RelSeries.map s2 {toFun := Submodule.map S.g, map_rel' := mr}-/


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
          exact ne_or_eq (rs.toFun (↑m + 1)) (rs.toFun ↑m)

  lemma go_equiv (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b))
  (rs' : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b))
  (n : ℕ) (eqs : ∀ i : Fin (n+1), rs.toFun i = rs'.toFun i) : go rs n = go rs' n := by
    induction n with
    | zero => aesop
    | succ m ih =>
      obtain h | h := em (rs.toFun ↑(m + 1) = rs.toFun ↑m)
      simp[go, h]
      simp_all only [Nat.cast_add, Nat.cast_one, ↓reduceIte]
      split
      next h_1 =>
        simp_all only [Nat.cast_add, Nat.cast_one]
        let eqs' : ∀ (i : Fin (m+1)), rs.toFun i = rs'.toFun i := by sorry
        exact ih eqs'
      next h_1 =>
        simp_all only [Nat.cast_add, Nat.cast_one]
        let cont := eqs (m+1)
        let shouldberw : rs'.toFun (↑m + 1) = rs'.toFun ↑m := by sorry
        exact False.elim (h_1 shouldberw)
      simp[go, h]
      simp_all only [Nat.cast_add, Nat.cast_one, ↓reduceIte]
      split
      next h_1 =>
        sorry
      next h_1 =>
        sorry










  theorem RelSeries.trimmed_length_leq_length (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b))
  : rs.length ≥ RelSeries.trimmed_length rs := by
    simp[RelSeries.trimmed_length]
    induction rs.length with
    | zero => aesop
    | succ n ih =>
      --simp_all
      --obtain h | h := em (n = 0)
      --rw[h]
      --aesop
      -- Ih indirectly says 1 + go rs (n-1) ≤ n

      let test (i : ℕ) : go rs i = 1 + (go rs (i-1)) ∨ go rs i = go rs (i-1) := by
        cases i with
        | zero => simp
        | succ m =>
          simp[go]
          exact ne_or_eq (rs.toFun (↑m + 1)) (rs.toFun ↑m)
      simp_all
      obtain h' | h' := test (n+1)
      --refine Nat.le_add_right_of_le ?succ.inl.h
      simp at h'

      --refine Nat.one_add_le_iff.mpr ?succ.inr.inl.a
      --exact lt_add_one_iff.mpr ih

      rw[h']

      refine Nat.one_add_le_iff.mpr ?succ.inl.a
      exact lt_add_one_iff.mpr ih

      simp at h'
      rw[h']
      exact Nat.le_add_right_of_le ih
      --simp_all
      --exact Nat.le_add_right_of_le ih

      /-
      obtain ⟨k, hk⟩ : ∃ k, n = succ k := by sorry
      rw[hk]
      simp[go]
      -/





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
        aesop
        exact ((notex n) h.symm)
        exact Nat.add_comm 1 n
    rw[gofact (rs.length)] at hrs
    obtain h | h := em (rs.length = 0)
    --let test : (if rs.length = 0 then 0 else 1 + (rs.length - 1)) = 0 := if_pos h
    --rw[test] at hrs
    rw[h] at hrs

    contradiction

    --let test : (if rs.length = 0 then 0 else 1 + (rs.length - 1)) = 1 + (rs.length - 1) := if_neg h
    --rw[test] at hrs
    --rw [Nat.add_comm] at hrs
    --rw [Nat.sub_one_add_one h] at hrs
    --exact (lt_self_iff_false rs.length).mp h

    apply (lt_self_iff_false rs.length).mp
    exact hrs
  /-
  variable {M} {M'} in
  lemma submoduleMap_trimmed_length (rs : RelSeries (α := Submodule R M) (· ≤ ·))
    (f : M →ₗ[R] M') : trimmed_length (rs.submoduleMap f) ≤ trimmed_length rs := sorry
  -/

  #check @Inf.inf (Submodule R M')
  def Submodule.comap_compute {f : M →ₗ[R] M'} (hf : Function.Injective f) (S : Submodule R M') :
   Submodule.comap f S ≃ₗ[R] (@Inf.inf (Submodule R M')) S (LinearMap.range f) := by
      sorry


  theorem Set.preimage_mono_of_range_intersection {A B : Type*} {f : A → B} {S S' : Set B}
    (ltint : Set.range f ⊓ S < Set.range f ⊓ S') (lt : S ≤ S') : f ⁻¹' S < f ⁻¹' S' := by
      simp_all
      rw[Set.ssubset_def]
      rw[Set.ssubset_def] at ltint

      --rw[Set.subset_def, Set.subset_def] at ltint

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



      --let h : S' ⊆ S := by
      --  let m : f '' (f ⁻¹' S') ⊆ f '' (f ⁻¹' S) := by aesop



  --theorem kernel_restriction {A : Submodule R M} {f :  M →ₗ[R] M'} : LinearMap.ker (f.domRestrict A) = A ⊓ (LinearMap.ker f) := by sorry


  --
  theorem module_quotient_mono {A B C D : Submodule R M} {hc : C ≤ A} {hd : D ≤ B}
    (hab : A < B) (hquot: Submodule.map A.mkQ C ≃ₗ[R] Submodule.map B.mkQ D) : C < D := by sorry


/-
  variable {M} {M'} in
  theorem baz {A B : Submodule R M} {f :  M →ₗ[R] M'} (bar : LinearMap.ker f ⊓ A = LinearMap.ker f ⊓ B)
    (q : Submodule.map f A = Submodule.map f B) : A ≤ B := by
      intro x hx
      let y := f x
      have hyA : y ∈ Submodule.map f A := by use x, hx
      rw[q] at hyA
      obtain ⟨z, hz, hzy⟩ := hyA


  variable {M} {M'} in
  theorem foo {A B : Submodule R M} {f :  M →ₗ[R] M'} (bar : LinearMap.ker f ⊓ A = LinearMap.ker f ⊓ B)
    (q : Submodule.map f A = Submodule.map f B) : A = B := by
    apply le_antisymm
    apply baz bar q
    apply baz bar.symm q.symm-/

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

  --variable {M} {M'} in
  --theorem map_eq_iff (f :  M →ₗ[R] M') {S : Submodule R M} : Submodule.map f S

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



    -- This should be easy. f(M') ⊓ M_i = f(M') ⊓ M_{i+1} implies ker g ⊓ M_i = ker g ⊓ M_{i+1}.
    -- Since M_i < M_{i+1}, we have that g(M_i) < g(M_i+1)
    theorem RelSeries.submodule_map_lt_of_comap_eq_exact {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS : S.ShortExact)
    (rs : RelSeries (α := Submodule R S.X₂) (· < ·)) (i : Fin rs.length)
    (p : (rs.submoduleComap S.f).toFun i = (rs.submoduleComap S.f).toFun (i+1))
    : (rs.submoduleMap S.g).toFun i < (rs.submoduleMap S.g).toFun (i+1) := by

      let exactness : LinearMap.range S.f = LinearMap.ker S.g :=
        CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hS.exact

      -- let's try to get the actual equality happening here.
      -- This intersection here is Submodule.map f (Submodule.comap f rs.toFun i(+1))
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
          intro i
          rw[RelSeries.eraseLast]
          simp
          let imod : i % (rs.length - 1 + 1) = i := by sorry

          --rw [← imod]





          -- Now it's basically nothing to prove this



          --let lesconf := ih p
          sorry

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

          let mas : ¬ rs.toFun (n + 1) = rs.toFun n := sorry
          simp[mas]
          rw[Nat.add_comm]
          simp


          apply go_equiv
          intro i
          rw[RelSeries.eraseLast]
          simp
          let imod : i % (rs.length - 1 + 1) = i := by sorry



          sorry







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


            let q' : (rs.submoduleMap S.g).toFun n' = (rs.submoduleMap S.g).toFun (n' + 1) := by exact q
            let leftlt' := RelSeries.submodule_comap_lt_of_map_eq_exact hS rs n' q'

            let leftlt : (rs.submoduleComap S.f).toFun ((rs.submoduleComap S.f).length - 1) < (rs.submoduleComap S.f).toFun (rs.submoduleComap S.f).length := sorry

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

                  ring_nf
                  ring_nf at h
                  unfold Fin.castSucc at h
                  unfold Fin.succ at h
                  unfold Fin.castAdd at h
                  simp at h
                  sorry






                exact False.elim (q hdif)
              ·
                sorry
            let q'' : (rs.submoduleMap S.g).toFun ((rs.submoduleMap S.g).length - 1) < (rs.submoduleMap S.g).toFun ((rs.submoduleMap S.g).length) := sorry
            let nonempt : (rs.submoduleMap S.g).length > 0 := by exact Fin.pos n'
            rw[RelSeries.trimmed_length_eraseLast_le nonempt q'']

            let rserasedLen : rs.eraseLast.length = n := by aesop

            let iherased := ih rs.eraseLast rserasedLen

            let makeIntoLemma : (rs.submoduleComap S.f).eraseLast.trimmed_length ≤ (rs.submoduleComap S.f).trimmed_length := sorry

            suffices n + 1 ≤ (rs.submoduleMap S.g).eraseLast.trimmed_length + 1 + (rs.submoduleComap S.f).eraseLast.trimmed_length by exact le_add_of_le_add_left this makeIntoLemma

            ring_nf

            let shouldProve := Nat.add_le_add_left iherased 1
            ring_nf at shouldProve
            exact shouldProve






  -- Not completed because it's not clear if this is necessary. Could be useful for the trimmed
  -- length api though
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
  theorem Module.length_ge_trimmed_length (rs : RelSeries fun (a : Submodule R M) (b : Submodule R M) => a ≤ b)
   : RelSeries.trimmed_length rs ≤ Module.length fl := by
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









--def FiniteModuleLength : IsFiniteLength R M → ℕ
--| of_subsingleton => 0
--| of_simple_quotient =>

/-
  - WTS: given 0 → M' i→ M q→ M'' -> 0
  - length M = length M' + length M''

Proof:-
  - length M ≥ length M' + length M''
    - Take a filtration of M' of length n' and a filtration of M'' of length n''
    - Make a filtration of length n + n' from these
    - n ≥ n' + n''

  - length M ≤ length M' + length M''
    - Given a filtration M_0 ⊂ M_1 ⊂ ... ⊂ M_n in M consider Mᵢ' = Mᵢ ∩ M'
    - and Mᵢ'' = g (Mᵢ) (lengths are n' and n'' respectively)
    - If there are two consecutive elements the same in M' and in M''
    - at i and i+1, then Mi and Mi+1 must also be the same. We note that by
    - assumotion, Mi and Mi+1 cannot be the same. So the sum of the lengths of
    - these filtrations must be at least as large as M since going from i to i+1
    - makes progress in either M' or M'' (or both), and so n ≤ n' + n''
-/

  --def dumb (f : M ⟶ M') : (M →ₗ[R] M') :=


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
    · -- Here we're defining the interesection of our composition series M with M' as embedded by f,
      -- which should conveniently be given by the comap. We note that this is no longer a relSeries
      -- with < necessarily, but that the length of this sequence is greater than or equal to the
      -- length of M'. We somehow need that this sequence, when we prune it of all the equalities,
      -- will give us a well defined relseries on <, where we can apply our theorem to bound this
      -- above by the length of M'.


      let inter : RelSeries (α := Submodule R S.X₁) (· ≤ ·) := {
        length := s2.length
        toFun := fun i ↦ Submodule.comap S.f (s2.toFun i)
        step := by
          intro i
          refine Submodule.comap_mono ?_
          let proof := JordanHolderLattice.lt_of_isMaximal (s2.step i)
          exact le_of_lt proof
      }


      let im : RelSeries (fun (a : Submodule R S.X₃) (b : Submodule R S.X₃) => a ≤ b) := {
        length := s2.length
        toFun := fun i ↦ Submodule.map S.g (s2.toFun i)
        step := by
          intro i
          refine Submodule.map_mono ?_
          let proof := JordanHolderLattice.lt_of_isMaximal (s2.step i)
          exact le_of_lt proof
      }


      let unique_increase := RelSeries.submodule_comap_lt_of_map_eq_exact hS (CompositionSeries.lt_series s2)

      --let lengthCompare : (trimmed_length inter + trimmed_length im) ≥ s2.length := sorry

      --check CompositionSeries
      let trimmedProof := trimmed_length_additive hS s2.lt_series
      let s2mas : s2.lt_series.length = s2.length := rfl
      rw[s2mas] at trimmedProof

      let detrimg := RelSeries.trimmed_length_leq_length (s2.lt_series.submoduleMap S.g)
      let detrimf := RelSeries.trimmed_length_leq_length (s2.lt_series.submoduleComap S.f)

      -- We now just need something which says that the length of an LESeries is bounded by the length
      -- of a composition series and we're done.

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

      --let lenleft : (s2.lt_series.submoduleMap S.g).length =
      --#check (s2.lt_series.submoduleMap S.g).trimmed_length_leq_length
      --simp at trimmedProof
      -- We have now that the trimmed length of s2

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

      let combined := Module.length_ge_relSeries fl2 smashfg


      rw[← Module.length_witness fl2 s2 hs2]
      exact combined

end FL










  -- rw[← WithBot.eq_unbot_iff]
  -- rw[Nat.eq_iff_le_and_ge]
