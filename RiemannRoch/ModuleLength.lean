import Mathlib.Order.KrullDimension
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


variable (R : Type*)
         [Ring R]
         (M : Type*)
         [AddCommMonoid M]
         [Module R M]

noncomputable def ModuleLength :
    WithBot (WithTop ℕ) :=
  krullDim (Submodule R M)

variable (fl : IsFiniteLength M)

def FiniteModuleLength : ℕ =

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

theorem ModuleLengthAdditive {R : Type _} [Ring R]
{S : CategoryTheory.ShortComplex (ModuleCat R)} (hS' : S.ShortExact) :
ModuleLength R S.X₂ = ModuleLength R S.X₁ + ModuleLength R S.X₃ := by
  simp[ModuleLength, krullDim]


  -- rw[← WithBot.eq_unbot_iff]
  -- rw[Nat.eq_iff_le_and_ge]
  sorry
