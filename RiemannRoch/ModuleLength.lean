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
           (M M' : Type*)
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

example {α} (a : α) (f : α → α) (h : ∀ a, f a = a) : f (f a) = a := by
  apply Eq.trans
  apply h
  apply h

  theorem FiniteModuleLengthCompute (s : CompositionSeries (Submodule R M))
    (cs : RelSeries.head s = ⊥ ∧ RelSeries.last s = ⊤) : Module.length M fl = s.length := sorry

  /-
  noncomputable def ModuleLength :
      WithBot (WithTop ℕ) :=
    krullDim (Submodule R M)
  -/
  --def subModule_of_subset (L : Module R M)


  variable {M} {M'} in
  def relSeries_of_injective {f : M →ₗ[R] M'} (hf : Function.Injective f)
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
  variable {M} {M'} in
  def relSeries_of_surjective {f : M →ₗ[R] M'} (hf : Function.Surjective f)
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

variable {M} in
def IsCompositionSeries (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b)) : Prop :=
  ∀ (n : ℕ), ∀ (i : Fin n), JordanHolderLattice.IsMaximal (rs.toFun i) (rs.toFun (i+1))

variable {M} in
def compositionSeriesOf {rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b)}
  (cs : IsCompositionSeries rs) : CompositionSeries (Submodule R M) := sorry


  /-
  I think the idea here should be you case match on whether rs is a composition series or not.
  If it is one, then you're done by Jordan Holder.

  If it's not, then there must be some place where the quotient is non simple, so this part of
  the series factors into more maps, increasing the length and giving a contradiction.
  -/
  open CompositionSeries in
  theorem Module.length_ge_relSeries
    (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b))
    : Module.length M fl ≥ rs.length := by
      simp
      --rw[isFiniteLength_iff_exists_compositionSeries] at fl

      simp[Module.length]
      intro m mnotrsmax cs csbot cstop maximal
      #check jordan_holder
      #check em
      obtain h | h := em (IsCompositionSeries rs)
      let cs' := compositionSeriesOf h
      obtain h' | h' := em (RelSeries.head cs' = ⊥ ∧ RelSeries.last cs' = ⊤)
      let eq : RelSeries.head cs = RelSeries.head cs' := by
        rw[csbot]
        rw[h'.1]
      let eq' : RelSeries.last cs = RelSeries.last cs' := by
        rw[cstop]
        rw[h'.2]
      let jh := jordan_holder cs cs' eq eq'
      -- should just be a theorem for this
      sorry

      sorry

      sorry

  -- Length of an le series only counting steps which are not equality
  variable {M} in
  def trimmed_length (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b)) : ℕ := sorry


  open Classical in
  noncomputable
  def induced_lt_relSeries_of_le_relSeries
    (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a ≤ b))
    : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b) := {
      length := trimmed_length rs
      toFun := fun n ↦ match n.val with
                | 0     => rs.toFun 0
                | (m+1) => by
                  let existance : (∃ n : ℕ, rs.toFun ↑n ≠ rs.toFun ↑m) := sorry
                  let input := (Nat.find (p := fun (k : ℕ) ↦ rs.toFun k ≠ rs.toFun m)) existance
                  exact rs.toFun input
      step := sorry
    }









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
      Module.length S.X₂ fl2 = Module.length S.X₁ fl1 + Module.length S.X₃ fl3 := by

    rw [Nat.le_antisymm_iff]
    rw[isFiniteLength_iff_exists_compositionSeries] at fl1 fl2 fl3

    choose s1 hs1 using fl1
    choose s2 hs2 using fl2
    choose s3 hs3 using fl3

    rw[FiniteModuleLengthCompute S.X₁ fl1 s1 hs1]
    rw[FiniteModuleLengthCompute S.X₂ fl2 s2 hs2]
    rw[FiniteModuleLengthCompute S.X₃ fl3 s3 hs3]

    constructor
    · -- Here we're defining the interesetcion of our composition series M with M' as embedded by f,
      -- which should conveniently be given by the comap. We note that this is no longer a relSeries
      -- with < necessarily, but that the length of this sequence is greater than or equal to the
      -- length of M'. We somehow need that this sequence, when we prune it of all the equalities,
      -- will give us a well defined relseries on <, where we can apply our theorem to bound this
      -- above by the length of M'.
      let inter : RelSeries (fun (a : Submodule R S.X₂) (b : Submodule R S.X₂) => a ≤ b) := {
        length := s2.length

        -- I have absolutely no idea what's happening with this definition
        toFun := sorry --fun i ↦ Submodule.comap S.f (s2.toFun i)
        step := sorry
      }

      let im : RelSeries (fun (a : Submodule R S.X₂) (b : Submodule R S.X₂) => a ≤ b) := {
        length := s2.length

        -- I have absolutely no idea what's happening with this definition
        toFun := fun i ↦ sorry --Submodule.map S.g (s2.toFun i)
        step := sorry
      }

      let oneIncreases (i : ℕ) (eqleft : inter.toFun i = inter.toFun (i + 1))
        (eqright : im.toFun i = im.toFun (i+1)) : False := sorry



      sorry

      --  "Easy" direction - just take composition series for M' and M'' and stick them together
    · let gInv : RelSeries (fun (a : Submodule R S.X₂) (b : Submodule R S.X₂) => a < b) :=
        relSeries_of_surjective hS.moduleCat_surjective_g s3


      let fIm : RelSeries (fun (a : Submodule R S.X₂) (b : Submodule R S.X₂) => a < b) :=
        relSeries_of_injective hS.moduleCat_injective_f s1


      have connect : fIm.last = gInv.head := sorry

      let smashfg := RelSeries.smash fIm gInv connect

      let combined := Module.length_ge_relSeries S.X₂ fl2 smashfg



      sorry

end FL










  -- rw[← WithBot.eq_unbot_iff]
  -- rw[Nat.eq_iff_le_and_ge]
