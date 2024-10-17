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

open AlgebraicGeometry


class IsFiniteType {X Y : Scheme} (f : X ⟶ Y) : Prop where
  locally_finite_type : LocallyOfFiniteType f
  quasi_compact : QuasiCompact f



class IsProper {X Y : Scheme} (f : X ⟶ Y) : Prop where
  universally_closed : UniversallyClosed f
  separated : IsSeparated f
  finite_type : IsFiniteType f


/-
Unnecessary in the long run, and it shouldn't be difficult to define,
I just can't find the unique map into spec Z given by any scheme
-/
class IsSeparatedScheme (X : Scheme) where
  sep : sorry
