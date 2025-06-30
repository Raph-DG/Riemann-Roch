import Mathlib
import RiemannRoch.AlgebraicCycle
import RiemannRoch.Divisor
import RiemannRoch.CechCohomology
import RiemannRoch.IsFreeAbelian



open AlgebraicGeometry
open CategoryTheory
open SheafOfModules
open Module
open CechCohomology
open IsFreeAbelian

universe w u v t

/-
Definition of a curve we're using for the statenent of Riemann-Roch, which is an
integral scheme of dimenson 1 which is proper over an algebraically closed field.

We also need some regularity assumption. In Hartshorne,they assume all local rings
are regular. I think it suffices just to be regular in codimension 1, but that could
be false. In any case, the exact form of this assumption is yet to be determined so
we leave it as a TODO
-/
variable {X : Scheme.{u}}
         {k : Type u}
         [Field k]
         [IsAlgClosed k]
         {f : X ⟶ Spec (CommRingCat.of k)}
         [IsProper f]
         [IsIntegral X]
         (dimOne : topologicalKrullDim X = 1)
         (D : WeilDivisor X)
         -- TODO: All local rings of X are regular
/--
This is true since X is finite type over a field (i.e. a Noetherian scheme).
TODO: Add this in a sensible way to Mathlib.
-/
instance : IsLocallyNoetherian X := sorry

/--
This is true since X is proper over a field.
-/
instance : CompactSpace X.carrier := sorry

--#check Γ(X, R)

/--
TODO: need some expression for the degree of D
-/
theorem RiemannRoch : χ 𝒪(D.1) = sorry + χ 𝒪((0 : AlgebraicCycle X)) := sorry
