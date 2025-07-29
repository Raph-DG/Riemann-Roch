import Mathlib
import RiemannRoch.Divisor


open AlgebraicGeometry
open CategoryTheory
open SheafOfModules
open Module

universe w u v t


/-
Definition of a curve we're using for the statenent of Riemann-Roch.
-/
variable {X : Scheme.{u}}
         {k : Type u}
         [Field k]
         [IsAlgClosed k]
         {f : X ⟶ Spec (CommRingCat.of k)}
         [IsProper f]
         [IsSeparated f] -- Should give that X is separated, so shouldn't need IsSeparatesScheme
         [IsIntegral X]
         (dimOne : topologicalKrullDim X = 1)
         (D : WeilDivisor X)

/-
That X is separated should be derivable from the strong assumptions about it
-/
--instance XSep : IsSeparatedScheme X := sorry

macro:max "𝒪(" D:term ")": term =>
  `(LineBundleOfDivisor $D)

macro:max "H"i:superscript(term) F:term: term =>
  `(CechCohomologyQCoh $F $(⟨i.raw[0]⟩))

macro:max "h"i:superscript(term) D:term: term =>
  `(FiniteDimensional.finrank (CechCohomologyQCoh (LineBundleOfDivisor $D) $(⟨i.raw[0]⟩))

theorem RiemannRoch :
 (finrank (CommRingCat.of k) (CechCohomologyQCoh (LineBundleOfDivisor D) f 0))
 - (finrank (CommRingCat.of k) (CechCohomologyQCoh (LineBundleOfDivisor D) f 1)) =
  DegreeOfWeilDivisor D +
  (finrank (CommRingCat.of k) (CechCohomologyQCoh (LineBundleOfDivisor (ZeroDivisor X)) f 0))
  - (finrank (CommRingCat.of k) (CechCohomologyQCoh (LineBundleOfDivisor (ZeroDivisor X)) f 1)) := sorry
