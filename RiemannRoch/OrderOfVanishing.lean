import Mathlib
import RiemannRoch.NewModuleLength
import Batteries.Tactic.ShowUnused



open AlgebraicGeometry
open CategoryTheory
open Opposite.op
open Module
open Order
open Ring

universe u v
variable {R : Type v}
         [CommRing R]
         (X : Scheme.{u})


noncomputable
def AlgebraicGeometry.Scheme.dimension : WithBot ℕ∞ := topologicalKrullDim X.carrier

/-
noncomputable
def Scheme.codimension {Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] := X.dimension - Y.dimension
-/



def quotientSequence (a b : R) : CategoryTheory.ShortComplex (ModuleCat R) where
  X₁ := ModuleCat.of R (R ⧸ (Ideal.span {a}))
  X₂ := ModuleCat.of R (R ⧸ (Ideal.span {a*b}))
  X₃ := ModuleCat.of R (R ⧸ (Ideal.span {b}))
  f :=
    let fl : R ⧸ (Ideal.span {a}) →ₗ[R] R ⧸ (Ideal.span {a*b}) :=
      let f : R →ₗ[R] R ⧸ (Ideal.span {a*b}) :=
        Submodule.mkQ (Ideal.span {a * b}) ∘ₗ
        IsLinearMap.mk' (fun r : R ↦ b * r) (IsLinearMap.isLinearMap_smul b)
      have hf : Ideal.span {a} ≤ LinearMap.ker f := sorry
      Submodule.liftQ (Ideal.span {a}) f hf
    ModuleCat.ofHom fl
  g := sorry
  zero := sorry

variable [IsNoetherianRing R]
         [IsLocalRing R]
         [DimensionLEOne R]
         {K : Type v}
         [Field K]
         [Algebra R K]
         [IsDomain R]
         [IsFractionRing R K]

variable (R) in
noncomputable
def orderOfVanishing (x : R) := Module.length R (R ⧸ Ideal.span {x})

-- Now we need a version that works as numerator - denominator.
-- That should be very doable, just need to work out how to work with elements of a localization
-- as fractions

-- Then if we can prove exactness of the above sequence, we get additivity for free. We still need
-- some reasoning to show that this gives a finite result. But once we have that we can start
-- defining principal divisors
