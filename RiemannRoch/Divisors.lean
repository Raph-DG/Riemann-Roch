/-
import Mathlib.Order.KrullDimension
import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.Order.Hom.Basic
import Mathlib.AlgebraicGeometry.Properties
import RiemannRoch.ModuleLength
import RiemannRoch.Proper
import RiemannRoch.InvertibleSheaf
import Mathlib.Geometry.RingedSpace.PresheafedSpace
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.UniqueFactorizationDomain
-/
import Mathlib
import RiemannRoch.ModuleLength
import RiemannRoch.Proper
import RiemannRoch.InvertibleSheaf

variable (Y : AlgebraicGeometry.Scheme)
#check Y.carrier


open AlgebraicGeometry
open CategoryTheory
open SheafOfModules
open Opposite.op

noncomputable
def dimension (X : Scheme) : WithBot ℕ∞ := topologicalKrullDim X.carrier

/-
Suppose f an isomorphism of preorders.

Then, f.hom ≫ f.inv = ₁ & f.inv ≫ f.hom = ₁,
& we also know f.hom & f.inv are monotone

Suppose a < b

WTS: f.hom a < f.hom b

Well, we know there are some ya, yb ∈ Y s.t.
f.inv ya = a & f.inv yb = b

So, f.hom (f.inv ya) < f.hom (f.inv yb)
WTS: ya < yb

hmm, not so helpful, we can't use that a < b here

But we can use this to show f.inv strictmono ↔ f.hom strictmono

Ok, know f.hom a ≤ f.hom b & a < b, so we just need to show ¬ f.hom b ≤ f.hom a

Ok, so suppose f.hom b ≤ f.hom a.

Then, b ≤ a by monotonicity of f.inv

But that means a < b & b ≤ a, which is a contradiction.

-/

lemma Bijection_Nonempty_Preimage {X Y : Type _} (f : X → Y) (h : Function.Bijective f) : ∀ q : Y, (f ⁻¹' {q}).Nonempty := by {
  intro q
  obtain ⟨m, pf⟩ := h.2 q
  use m
  exact pf
}

lemma Bijection_Preimage_Singleton {X Y : Type _} (f : X → Y) (h : Function.Bijective f) : ∀ q : Y, ∃ l ∈ f ⁻¹' {q}, ∀ n ∈ f ⁻¹' {q}, n = l := by {
  intro q
  obtain ⟨elpiq, wit⟩  := Bijection_Nonempty_Preimage f h q
  use elpiq
  constructor
  exact wit
  intro n ninpi
  let fseq : f n = f elpiq := by {
    rw[ninpi]
    rw[wit]
  }
  exact h.1 fseq
}

lemma Bijection_Preimage_Inverse_Of_Image {X Y : Type _} (f : X → Y) (h : Function.Bijective f) : ∀ (u : Set X), f ⁻¹' (f '' u) = u := by
  exact fun u ↦ Eq.symm ((fun hf ↦ (Set.eq_preimage_iff_image_eq hf).mpr) h rfl)

lemma Bijection_Image_Inverse_Of_Preimage {X Y : Type _} (f : X → Y) (h : Function.Bijective f) : ∀ (u : Set Y), f '' (f ⁻¹' u) = u := by
  exact fun u ↦ Eq.symm ((fun hf ↦ (Set.preimage_eq_iff_eq_image hf).mp) h rfl)

#check lt_iff_le_not_le



structure ClosedImmersionOver (X : Scheme) :=
  source : Scheme
  embedding : source ⟶ X
  immersion : IsClosedImmersion embedding

def IsSubschemeMorphism {X : Scheme} {Z : ClosedImmersionOver X} {Y : ClosedImmersionOver X} (f : Y.source ⟶ Z.source) : Prop :=
  Y.embedding = f ≫ Z.embedding

def existsIsoOfClosedSubscheme (X : Scheme)
  (Y : ClosedImmersionOver X) (Z : ClosedImmersionOver X) : Prop
  :=  ∃ (h : Y.source ≅ Z.source), IsSubschemeMorphism h.hom

instance closedImmersionTargettingSchemeSetoid (X : Scheme) : Setoid (ClosedImmersionOver X) where
  r := existsIsoOfClosedSubscheme X
  iseqv := {
    refl := by {
      intro cl
      use Iso.refl cl.source
      rfl
    }
    symm := by {
      intro Y Z
      simp[existsIsoOfClosedSubscheme, IsSubschemeMorphism]
      intro i eq
      use i.symm
      rw[eq]
      simp
    }
    trans := by {
      intro ⟨y1, f1, im1⟩ ⟨y2, f2, im2⟩ ⟨y3, f3, im3⟩
      simp[existsIsoOfClosedSubscheme, IsSubschemeMorphism]
      intro y1iy2 eq1 y2iy3 eq2
      use y1iy2 ≪≫ y2iy3
      simp
      rw[←eq2]
      exact eq1
    }
  }

def ClosedSubscheme (X : Scheme) := Quotient (closedImmersionTargettingSchemeSetoid X)




def SubschemeDimension {X : Scheme} (Y : ClosedSubscheme X) : WithBot ℕ∞ := by
  sorry
  -- apply Quotient.lift
/-
Note this is of course not the real definition of the codimension
-/
noncomputable
def coDimension {X : Scheme} (Y : ClosedSubscheme X) : WithBot ℕ∞ := sorry /- dimension X - (SubschemeDimension Y) -/



/-
Note I just wanted to get this to compile, this really should be integral
closed subschemes.
-/
structure PrimeWeilDivisor (X : Scheme) where
 subscheme : ClosedSubscheme X
 codim : coDimension subscheme = 1
 /-integral : IsIntegral subscheme-/

def WeilDivisor (X : Scheme) := FreeAbelianGroup (PrimeWeilDivisor X)



/-
An attempt at defining the sheaf of rational functions via the presheaf of
total quotient rings. Running into some typing issues with sheafification.
-/
def RatPreSheaf (X : Scheme) : TopCat.Presheaf Type X.carrier := {
  obj := fun U ↦ FractionRing (X.presheaf.obj U)
  map := by {
    sorry
  }
}


def FieldOfFractionsOfScheme (X : Scheme) [IsIntegral X] : CommRingCat := sorry

/-
Order of vanishing of an element f of the function field of X at a point x. Defined as the
length of the module O_x / f
-/
def OrderOfRat {X : Scheme} [IsIntegral X] (f : FieldOfFractionsOfScheme X) (x : PrimeWeilDivisor X) : ℕ := sorry



/-
Sum over all codimension 1 varieties of the zero locus, commmonly denoted (f). This is well defined
because the number of points where f is 0 or infinity is a proper closed subset, and assuming X is Noetherian a
proper closed subset is a union of a finite number of irreducible closed subsets.

Probably best to actually define this as the sum of that decomposition explicitly rather than attempting to take
an infinite sum and proving that along most prime divisors our function has neither a zero nor a pole
-/
def PrincipalWeilDivisor {X : Scheme} [IsIntegral X] (f : FieldOfFractionsOfScheme X) : WeilDivisor X := sorry

structure IsPrincipal {X : Scheme} [IsIntegral X] (D : WeilDivisor X) where
  f : FieldOfFractionsOfScheme X
  eq : D = (PrincipalWeilDivisor f)


axiom LinearEquivalentWeil (X : Scheme) : WeilDivisor X → WeilDivisor X → Prop

def LineBundleOfDivisor {X : Scheme} (D : WeilDivisor X) : SheafOfModules X.ringCatSheaf := {
  val := sorry /-TopCat.Presheaf CommRingCat X.carrier-/
  isSheaf := sorry
}

/-
instance LineBundleIsQCoh {X : Scheme} (D : WeilDivisor X) : IsQuasicoherent (LineBundleOfDivisor D) := sorry
-/
instance divisorClassSetoid (X : Scheme) : Setoid (WeilDivisor X) where
  r := LinearEquivalentWeil X
  iseqv := sorry

def WeilDivisorClassGroup (X : Scheme) := Quotient (divisorClassSetoid X)

def ZeroDivisor (X : Scheme) : WeilDivisor X := sorry

axiom WeilDivisorClassGroupInstance (X : Scheme) : CommGroup (WeilDivisorClassGroup X)

attribute [instance] WeilDivisorClassGroupInstance




class IsLocallyUFD (X : Scheme) : Prop where
  domain : ∀ (x : X), IsDomain (X.presheaf.stalk x)
  ufm : ∀ (x : X), UniqueFactorizationMonoid (X.presheaf.stalk x)


/-
Isomorphism between Cl(X) and Pic(X) for an Integral Noetheian scheme whose local rings are all unique
factorisation domains. The definition of this will almost certainly go via Cartier divisors,
-/

def LineBundleDivisorEquivalence (X : Scheme) [IsIntegral X] [IsNoetherian X] [IsLocallyUFD X] : WeilDivisorClassGroup X ≃* PicardGroup X := sorry

def DegreeOfWeilDivisor {X : Scheme} (D : WeilDivisor X) : ℤ := sorry
