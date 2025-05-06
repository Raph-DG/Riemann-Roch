import Mathlib
import RiemannRoch.CechCohomology
import RiemannRoch.Divisors
import RiemannRoch.Proper

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
         [IsSeparatedScheme X] -- Unnecessary, make into a theorem
         {f : X ⟶ Spec (CommRingCat.of k)}
         [IsProper f]
         [IsSeparated f] -- Should give that X is separated, so shouldn't need IsSeparatesScheme
         {p : dimension X = 1}
         /-Need assumption that local rings are regular-/
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
  `(FiniteDimensional.finrank (CechCohomologyQCoh (LineBundleOfDivisor $D) $(⟨i.raw[0]⟩)))


instance LineBundleIsQCoh {X : Scheme.{u}} (D : WeilDivisor X) :
    IsQuasicoherent (LineBundleOfDivisor D) := sorry

-- theorem RiemannRoch : h⁰(D) - h¹(D) =
--   DegreeOfWeilDivisor D + h⁰(ZeroDivisor X) - h¹(ZeroDivisor X) := sorry

set_option pp.universes true

#check LineBundleIsQCoh




#check (instQCohModule 0 f (LineBundleOfDivisor D))

theorem RiemannRoch :
 (finrank (CommRingCat.of k) (CechCohomologyQCoh (LineBundleOfDivisor D) f 0))
 - (finrank (CommRingCat.of k) (CechCohomologyQCoh (LineBundleOfDivisor D) f 1)) =
  DegreeOfWeilDivisor D +
  (finrank (CommRingCat.of k) (CechCohomologyQCoh (LineBundleOfDivisor (ZeroDivisor X)) f 0))
  - (finrank (CommRingCat.of k) (CechCohomologyQCoh (LineBundleOfDivisor (ZeroDivisor X)) f 1)) := sorry
