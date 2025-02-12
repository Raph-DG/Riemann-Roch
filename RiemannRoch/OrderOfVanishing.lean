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
variable (R : Type v)
         [CommRing R]
         (X : Scheme.{u})

noncomputable
def AlgebraicGeometry.Scheme.dimension : WithBot ℕ∞ := topologicalKrullDim X.carrier

/-
This doesn't work because we can't subtract elements of Withbot ℕ∞. We should probably just define
this the way the stacks project does as the supremum of lengths
noncomputable
def Scheme.codimension {Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] := X.dimension - Y.dimension
-/


variable {R} in
def quotientSequence (a b : nonZeroDivisors R) : CategoryTheory.ShortComplex (ModuleCat R) where
  X₁ := ModuleCat.of R (R ⧸ (Ideal.span {a.1}))
  X₂ := ModuleCat.of R (R ⧸ (Ideal.span {a.1*b.1}))
  X₃ := ModuleCat.of R (R ⧸ (Ideal.span {b.1}))
  f :=
    let fl : R ⧸ (Ideal.span {a.1}) →ₗ[R] R ⧸ (Ideal.span {a.1*b.1}) :=
      let f : R →ₗ[R] R ⧸ (Ideal.span {a.1*b.1}) :=
        Submodule.mkQ (Ideal.span {a.1 * b.1}) ∘ₗ
        IsLinearMap.mk' (fun r : R ↦ b.1 * r) (IsLinearMap.isLinearMap_smul b.1)
      have hf : Ideal.span {a.1} ≤ LinearMap.ker f := sorry
      Submodule.liftQ (Ideal.span {a.1}) f hf
    ModuleCat.ofHom fl
  g := sorry
  zero := sorry

variable {R} in
theorem quotientSequence_exact (a b : nonZeroDivisors R) : (quotientSequence a b).ShortExact := sorry

variable [IsNoetherianRing R]
         [IsLocalRing R]
         [DimensionLEOne R]
         -- We have that dimension is ≤ 1 now (meaning all primes are maximal), but we also need that
         -- this maximal ideal is not the zero ring, i.e. that we really do have a chain 0 < m < R
         {K : Type v}
         [Field K]
         [Algebra R K]
         [IsDomain R]
         [m : IsFractionRing R K]


noncomputable
def orderOfVanishing' (x : nonZeroDivisors R) := Module.length R (R ⧸ Ideal.span {x.1})

theorem orderOfVanishing'_additive (a b : nonZeroDivisors R) :
  orderOfVanishing' R (a*b) = orderOfVanishing' R a + orderOfVanishing' R b :=
   Module.length_additive <| quotientSequence_exact a b


/-
Note that in our context, we actually know these lengths are finite, so we just need to have that
written here
-/

theorem orderOfVanishing'_finite (x : nonZeroDivisors R) :
    ∃ a : ℕ, orderOfVanishing' R x = a := by
  -- This is nontrivial and will require a fair bit more stuff
  sorry

/-
This is a mildly insane definition of the order of vanishing. It should be correct, but using
choice 3 times doesn't give me much hope that it will be usable, and I'd also prefer not to
have the definition made in tactic mode.
-/
noncomputable
def orderOfVanishing (x : Kˣ) : ℤ := by
  let thing := m.surj' x.1
  choose frac hfrac using thing
  have : frac.1 ∈ nonZeroDivisors R := sorry
  have ex2 : ∃ b : ℕ, orderOfVanishing' R frac.2 = b := sorry
  choose a ha using (orderOfVanishing'_finite R ⟨frac.1, this⟩)
  choose b hb using (orderOfVanishing'_finite R frac.2)
  exact (a : ℤ) - (b : ℤ)
/-
At this point we have a definition of the order of vanishing as a function into ℤ, which should be
enough to define principal divisors.
-/


/-
This shows that the map Kˣ → Div X is a homomorphism of groups, meaning that principal divisors
form a group.
-/
theorem orderOfVanishing_additive (f g : Kˣ) :
  orderOfVanishing R (f*g) = orderOfVanishing R f + orderOfVanishing R g := sorry




/-
Assume for a moment that R is not necessarily local. Take x : R. We wish to show that
length R (M ⧸ xM) < ∞, where M is some R-submodule of ⨁ᵣK. This in turn shows that for
the case we want, the order of vanishing is finite, and so we can use the results we get
from these calculations as coefficients for divisors.

The proof goes something like this:

Since R has is Noetherian, x must be contained in a finite number of irreducible components. Since
R has dimension 1, these irreducible components muct all be points and indeed maximal ideals. In the
case we care about where R is local, this will just be the unique maximal ideal.

Since R is a Noetherian local ring, we know that dim (R ⧸ xR) = dim R - 1 (indeed, we have in a PR
that dim(R ⧸ xR) ≤ dim R - 1, which is all we need since dim cannot be ⊥). This implies that R⧸xR is
artinian (and hence is finite length as a module over itself), and by another lemma this means that
R is equal to the finite product of its localisations at its maximal ideals (Lemma 10.53.6 stacks project).
For some reason (this I need to find out), this implies that there is an analogous decomposition of
M as a product of M⧸xM localised at each maximal ideal (in the local case this should be that
localising at m gives the same ring, which makes sense since everything ouside of m is invertible
anyway).
-/
