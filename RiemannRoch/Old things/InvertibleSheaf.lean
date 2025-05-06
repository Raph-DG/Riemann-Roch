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
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Presheaf


universe w u v t

open AlgebraicGeometry


axiom TensorProductOfSheaves {X : Scheme.{u}} : SheafOfModules X.ringCatSheaf → SheafOfModules X.ringCatSheaf → SheafOfModules X.ringCatSheaf

class IsInvertibleSheaf {X : Scheme.{u}} (F : SheafOfModules.{w, u, u, u} X.ringCatSheaf) : Prop where
  invertible : ∃ (G : SheafOfModules.{w, u, u, u} X.ringCatSheaf), Nonempty (TensorProductOfSheaves F G ≅ SheafOfModules.unit X.ringCatSheaf)


structure InvertibleSheaf (X : Scheme.{u}) where
  bundle : SheafOfModules X.ringCatSheaf
  invertible : IsInvertibleSheaf bundle

theorem TensorProductOfSheavesPreservesInvertibility (X : Scheme) (L K : SheafOfModules X.ringCatSheaf) [IsInvertibleSheaf L] [IsInvertibleSheaf K] : IsInvertibleSheaf (TensorProductOfSheaves L K) := sorry


instance PicardSetoid (X : Scheme.{u}) : Setoid (InvertibleSheaf X) where
  r := fun L K ↦ Nonempty (L.bundle ≅ K.bundle)
  iseqv := sorry

def PicardGroup (X : Scheme.{u}) : Type _ := Quotient (PicardSetoid X)


instance PicardGroupStructure (X : Scheme.{u}) : CommGroup (PicardGroup X) := sorry
