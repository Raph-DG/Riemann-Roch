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



