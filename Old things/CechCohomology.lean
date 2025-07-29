
import Mathlib
--import RiemannRoch.Divisors


open AlgebraicGeometry
open SheafOfModules
open CategoryTheory
open Limits
open PresheafedSpace


universe u v
variable {A : Type v} [Category A] {X : Scheme.{u}}


def nfoldInts {n : ℕ} (U : X.OpenCover) (t : Fin n → U.J) : (TopologicalSpace.Opens X) := by
  let osub : Fin n → TopologicalSpace.Opens X := fun i => {
    carrier := Set.range (U.map (t i)).1.base
    is_open' := IsOpenImmersion.isOpen_range (U.map (t i))
  }
  let inter : TopologicalSpace.Opens X := {
    carrier := ⋂ (i : Fin n), (osub i).carrier
    is_open' := sorry --TopologicalSpace.isOpen_inter -- I think this is a theorem somewhere, inter_is_open or something
  }
  exact inter

noncomputable
def left_int_rest {U V : TopologicalSpace.Opens X} : U ⊓ V ⟶ U := by exact U.infLELeft V


/-
Here we wish to define the inclusion ⋂ (i : Fin n), U.J to ⋂ (i : Fin (n+1)), U.J which is
0 if the set of U.J indexed by n is not contained in the set of U.J indexed by n+1
-/


def nFoldIntsMap {n : ℕ} (U : X.OpenCover) (t : Fin n → U.J) (t' : Fin (n+1) → U.J)
  (subs : Set.range t ⊆ Set.range t') : (U.J × nfoldInts U t ⟶ nfoldInts U t') := by
    let map : nfoldInts U t ⟶ nfoldInts U t' := {
      down := by {
        let test : (nfoldInts U t).carrier ⊆ (nfoldInts U t').carrier := by {
          unfold nfoldInts
          simp
          intro i
          sorry
        }
        exact { down := test }
      }
    }
    sorry












  --linc : ({carrier := U ∩ V, is_open' := TopologicalSpace.isOpen_inter}) ⟶ U
  --rinc : U ⊓ V ⟶ V
  --let test := ⋂ (i : Fin n), sorry
/-
Given a presheaf and an open cover, compute the cech nerve of the cover
-/

#check nfoldInts




noncomputable
def CechComplexWithRespectToCover [HasProducts A] [Preadditive A] (U : X.OpenCover)
    {n : ℕ} (fin : U.J ≅ Fin n) (F : (TopologicalSpace.Opens X)ᵒᵖ ⥤ A) : CochainComplex A ℕ := by
      let test := fun j (t : Fin j → U.J) => F.obj (Opposite.op (nfoldInts U t))
      let out : CochainComplex A ℕ := {
        X := fun i => by { --Discrete.functor (t : Fin i → U.J) × (F.obj (Opposite.op (nfoldInts U t)))
          let func := Discrete.functor (test i)
          exact (limit func)
        }
        d := fun i j ↦ by {
          simp
          let obv : Fintype U.J := sorry

          --let mor : (Fin i → U.J) → A := fun t ↦ ∑ (t' : Fin (i+1) → U.J), by {}
          sorry
        } -- Need F applied to a bunch of restriction maps
      }
      sorry





/-
Theorem: Given a separated scheme, any open affine cover will give the same
Cech cohomology value.

Note that being separated is not strictly necessary here, the reason we have it is because
it allows us to not need to check anything about the open cover. This also works
for an arbitrary scheme where we have an affine cover such that all intersections
of the cover are also affine (which is immediately implied by X being separated)
-/
theorem QCohCohomologyWorksForAnyCover (F : SheafOfModules X.ringCatSheaf) [IsQuasicoherent F] :
∀ (i : ℕ), ∃ (G : AddCommGrp),
∀ (U : X.AffineOpenCover),
Nonempty ((HomologicalComplex.homology (CechComplexWithRespectToCover (AlgebraicGeometry.Scheme.AffineOpenCover.openCover U) F.val.presheaf) i) ≅ G) := sorry


/-
May want to return a structure here that bundles our Abelian group with a proof that it's a Γ(X, X)
module
-/
axiom CechCohomologyQCoh {A : CommRingCat} (F : SheafOfModules X.ringCatSheaf)
    (f : X ⟶ Spec A) [IsSeparated f] [IsQuasicoherent F] (i : ℕ) : AddCommGrp

instance instQCohModule {A : CommRingCat} (i : ℕ) (f : X ⟶ Spec A) [IsSeparated f]
    (F : SheafOfModules X.ringCatSheaf) [IsQuasicoherent F] : Module A (CechCohomologyQCoh F f i) := sorry


macro:max "𝒪(" D:term ")": term =>
  `(LineBundleOfDivisor $D)

macro:max "H"i:superscript(term) F:term: term =>
  `(CechCohomologyQCoh $F $(⟨i.raw[0]⟩))

macro:max "h"i:superscript(term) F:term: term =>
  `(Module.finrank (CechCohomologyQCoh $F $(⟨i.raw[0]⟩)))

variable (G : SheafOfModules X.ringCatSheaf) [IsQuasicoherent G]

--#check h⁰G
#check 𝒪(ZeroDivisor X)

/- Serre finiteness and vanishing (Hartshorne theorem 5.2) -/

def ProjectiveSpace (R : CommRingCat) (n : ℕ) : Scheme.{u} := sorry

def TwistingSheaf {m : ℕ} {R : CommRingCat} (n : ℕ) : SheafOfModules (ProjectiveSpace R n).ringCatSheaf := sorry



/-
We now in princial have the Cech cohomology of a quasicoherent sheaf as something we can
mess around with

Now, to avoid proving too much about cohomology, it might be best to phrase Riemann
Roch as h^0(X, L(D)) - h^1(X, L(D)) = deg D + h^0(X, L(D)) - h^1(X, L(D))

So, here we need a notion of h^1 (i.e. the dimension of the corresponding vector space)

In other words, we need that over a field k we have that our Abelian group is a k-vector
space.
-/

/-
I'm a little worried we may want Serre finiteness. For this, I think, it might
be better just to prove it in the special case of line bundles on curves.

Noting that the pushforward preserves cohomology because
we have a closed subset (Hartshorne III 2.10), so if we can prove the result for
P^n we get our result. But we can classify line bundles on P^n by combinatorial
means, so we should be able to push this through.

The only problem is



In this case, we know any curve is covered by two open affines and since we're assuming
a lot about what a curve is, we can apply our above theorem to say that the
cohomology of our line bundle can be computed with respect to this cover.

What we'd really like is for our line bundle to trivialise on such a cover,
then we'd have that on

Then, we need to show that
-/


/-
Want: Vakil theorem 19.1.2 in here as our theorem about cohomology of line bundles
on projective space.

Then want: Hartshorne III 5.2 on the generalisation of this result to coherent sheaves

Could also use Hartshorne II 5.19, but this only proves that global sections of a coherent
sheaf are finitely generated, which doesn't help with H^1 unless we have Serre duality
-/
