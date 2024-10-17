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
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.FiniteLength

open AlgebraicGeometry
open CategoryTheory
open Opposite.op
open Module
open Order
open Ring

variable (R : Type*)
         [Ring R]
         (M M' : Type*)
         [AddCommGroup M]
         [AddCommGroup M']
         [Module R M]
         [Module R M']

noncomputable def ModuleLength :
    WithBot (WithTop ℕ) :=
  krullDim (Submodule R M)

--def subModule_of_subset (L : Module R M)

def relSeries_of_injective (f : M →ₗ[R] M') (hf : Function.Injective f)
    (s : CompositionSeries (Submodule R M)) :
    RelSeries (fun (a : Submodule R M') (b : Submodule R M') => a < b) := {
      length := s.length
      toFun := fun n => LinearMap.submoduleImage (f.domRestrict (s.toFun n)) (s.toFun n)
      step := by {
        intro i
        simp
        sorry
      }
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
    - Given a chain M_0 ⊆ M_1 ⊆ ... M_n consider Mᵢ' = Mᵢ ∩ M'
    - and Mᵢ'' = q (Mᵢ) (lengths are n' and n'' respectively)
    - If there are two consecutive elements the same in M' and in M''
    - at i and i+1, then Mi and Mi+1 must also be the same, so
    - n ≤ n' + n''
-/


section FL

  variable (fl : IsFiniteLength R M)

  noncomputable
  def FiniteModuleLength : ℕ := by
    rw[isFiniteLength_iff_exists_compositionSeries] at fl
    choose s _ using fl
    exact s.length


  theorem FiniteModuleLengthCompute (s : CompositionSeries (Submodule R M))
    (cs : RelSeries.head s = ⊥ ∧ RelSeries.last s = ⊤) : FiniteModuleLength R M fl = s.length := sorry

  theorem ModuleLengthAdditive
  {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS' : S.ShortExact)
  (fl1 : IsFiniteLength R S.X₁) (fl2 : IsFiniteLength R S.X₂) (fl3 : IsFiniteLength R S.X₃):
  FiniteModuleLength R S.X₂ fl2 = FiniteModuleLength R S.X₁ fl1 + FiniteModuleLength R S.X₃ fl3 := by
    rw [Nat.le_antisymm_iff]
    rw[isFiniteLength_iff_exists_compositionSeries] at fl1 fl2 fl3

    choose s1 hs1 using fl1
    choose s2 hs2 using fl2
    choose s3 hs3 using fl3

    rw[FiniteModuleLengthCompute R S.X₁ fl1 s1 hs1]
    rw[FiniteModuleLengthCompute R S.X₂ fl2 s2 hs2]
    rw[FiniteModuleLengthCompute R S.X₃ fl3 s3 hs3]

    constructor
    sorry
    sorry


end FL










  -- rw[← WithBot.eq_unbot_iff]
  -- rw[Nat.eq_iff_le_and_ge]
