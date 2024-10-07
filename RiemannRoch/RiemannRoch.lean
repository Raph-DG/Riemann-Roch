import Mathlib
import RiemannRoch.CechCohomology
import RiemannRoch.Divisors
import RiemannRoch.Proper

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules

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
         {p : dimension X = 1}
         /-Need assumption that local rings are regular-/
         (D : WeilDivisor X)

/-
That X is separated should be derivable from the strong assumptions about it
-/
lemma XSep : IsSeparated (𝟙 X) := sorry

macro:max "𝒪(" D:term ")": term =>
  `(LineBundleOfDivisor $D)

macro:max "H"i:superscript(term) F:term: term =>
  `(CechCohomologyQCoh $F $(⟨i.raw[0]⟩))

macro:max "h"i:superscript(term) D:term: term =>
  `(FiniteDimensional.finrank (CechCohomologyQCoh (LineBundleOfDivisor $D) $(⟨i.raw[0]⟩)))


instance LineBundleIsQCoh {X : Scheme} (D : WeilDivisor X) : IsQuasicoherent (LineBundleOfDivisor D) := sorry


theorem RiemannRoch : h⁰(D) - h¹(D) = DegreeOfWeilDivisor D + h⁰(ZeroDivisor X) - h¹(ZeroDivisor X) := sorry
