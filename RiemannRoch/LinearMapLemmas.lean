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
import Mathlib.Data.ENat.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Group
import Batteries.Tactic.ShowUnused



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

  open LinearMap
  theorem LinearMap.ne_map_or_ne_kernel_intersection_of_lt {A B : Submodule R M} (f :  M →ₗ[R] M') (hab : A < B) :
    Submodule.map f A ≠ Submodule.map f B ∨ ker f ⊓ A ≠ ker f ⊓ B := by
      by_cases q : ker f ⊓ A ≠ ker f ⊓ B
      · exact Or.inr q
      · simp only [ne_eq, not_not] at q
        apply Or.inl
        intro h
        apply hab.ne
        apply le_antisymm hab.le
        intro x hx
        obtain ⟨z, hz, hzy⟩ := (h ▸ ⟨x, hx, rfl⟩ : f x ∈ Submodule.map f A)
        suffices x - z ∈ LinearMap.ker f ⊓ A by simpa using add_mem this.2 hz
        exact q ▸ ⟨by simp[hzy], by apply sub_mem hx (hab.le hz)⟩
  #find_home! LinearMap.ne_map_or_ne_kernel_intersection_of_lt
  theorem LinearMap.ker_intersection_mono_of_map_eq {A B : Submodule R M} {f :  M →ₗ[R] M'} (hab : A < B)
    (q : Submodule.map f A = Submodule.map f B) : LinearMap.ker f ⊓ A < LinearMap.ker f ⊓ B :=
      lt_iff_le_and_ne.mpr ⟨inf_le_inf le_rfl hab.le,
       Or.elim (LinearMap.ne_map_or_ne_kernel_intersection_of_lt f hab)
        (fun h ↦ False.elim (h q)) (fun h ↦ h)⟩


  theorem LinearMap.map_mono_of_ker_intersection_eq {A B : Submodule R M} {f :  M →ₗ[R] M'} (hab : A < B)
    (q : LinearMap.ker f ⊓ A = LinearMap.ker f ⊓ B) : Submodule.map f A < Submodule.map f B :=
      lt_iff_le_and_ne.mpr ⟨Set.image_mono hab.le, Or.elim (LinearMap.ne_map_or_ne_kernel_intersection_of_lt f hab) (fun h ↦ h) (fun h ↦ False.elim (h q))⟩
