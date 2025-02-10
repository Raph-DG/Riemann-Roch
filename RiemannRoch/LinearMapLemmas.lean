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



  theorem LinearMap.ker_intersection_mono_of_map_eq {A B : Submodule R M} {f :  M →ₗ[R] M'} (hab : A < B)
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
  theorem LinearMap.map_mono_of_ker_intersection_eq {A B : Submodule R M} {f :  M →ₗ[R] M'} (hab : A < B)
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
