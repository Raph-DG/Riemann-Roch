import Mathlib
import RiemannRoch.CechCohomology
import RiemannRoch.Divisors
import RiemannRoch.Proper

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules
open FiniteDimensional

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


instance LineBundleIsQCoh {X : Scheme.{u}} (D : WeilDivisor X) :
    IsQuasicoherent (LineBundleOfDivisor D) := sorry

example {A : Type} (f : A  → A ) {a : A} (p : f (f (f (a))) = a) (q : f (f (f (f (f (a))))) = a) : f a = a := by cc


/-
Why doesn't this work?
-/
example {A : Type} [Group A] {a : A} {p : a⁻¹ * a = 1} {q : a * 1 = 1} {o : 1 * a = 1}
  {r : (a⁻¹)⁻¹ * (a⁻¹ * a) = ((a⁻¹)⁻¹ * a⁻¹) * a} {z : 1 = a⁻¹ * a} {l : (a⁻¹)⁻¹ * a⁻¹ = 1} : (a⁻¹)⁻¹ = a := by cc


def uipTest {A B : Type} {p : A = B} {a : A} : B := by
  rw[←p]
  exact a

#check HEq
/-
example {A : Type} {t : A × A → A} {i : A → A} {one : A} {p : t (i (one), one) = one}
-/

#check ZeroDivisor

-- theorem RiemannRoch : h⁰(D) - h¹(D) =
--   DegreeOfWeilDivisor D + h⁰(ZeroDivisor X) - h¹(ZeroDivisor X) := sorry

set_option pp.universes true

#check LineBundleIsQCoh

#check (finrank k (CechCohomologyQCoh (LineBundleOfDivisor D) 0))

theorem RiemannRoch :
 (finrank (CechCohomologyQCoh (LineBundleOfDivisor D) 0))
 - (finrank (CechCohomologyQCoh (LineBundleOfDivisor D) 1)) =
  DegreeOfWeilDivisor D +
  (finrank (CechCohomologyQCoh (LineBundleOfDivisor (ZeroDivisor X)) 0))
  - (finrank (CechCohomologyQCoh (LineBundleOfDivisor (ZeroDivisor X)) 1)) := sorry
