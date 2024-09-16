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

open AlgebraicGeometry
open CategoryTheory
open Opposite.op
open Module

noncomputable def ModuleLength (R : Type _) (M : Type _) [Semiring R] [AddCommMonoid M] [Module R M] :
    WithBot (WithTop ℕ) :=
  krullDim (Submodule R M)

theorem ModuleLengthAdditive {R : Type _} [Ring R]
{S : CategoryTheory.ShortComplex (ModuleCat R)} (hS' : S.ShortExact) :
ModuleLength R ↑S.X₂ = ModuleLength R ↑S.X₁ + ModuleLength R ↑S.X₃ := sorry
