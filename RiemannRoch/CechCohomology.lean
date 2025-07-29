import Mathlib
import RiemannRoch.EulerCharacteristic

open AlgebraicGeometry CategoryTheory Limits
/-!
# Cech cohomology

In this file we define a skeleton of the lemmas we need about Cech cohomology.
Since this is currently being developed by Kenny Lau, we're mainly treating this
as a black box for the time being.

As such, this will be the least developed of the files for some time, and we will
only update thsi file as we need lemmas or definitions in the statement and proof of
Riemann-Roch.
-/

universe w v v' v'' u u' u''

variable {C : Type u} [Category.{v} C] (J : Type u') [Category.{v'} J]
  (A : Type u'') [Category.{v''} A]

namespace AlgebraicGeometry
namespace Scheme
namespace AffineOpenCover

variable {X : Scheme.{u}} (𝒰 : X.AffineOpenCover)

def openSet (j : 𝒰.J) : X.Opens where
  carrier := Set.range (𝒰.map j).base
  is_open' := IsOpenImmersion.isOpen_range (𝒰.map j)


end AffineOpenCover
end Scheme
end AlgebraicGeometry

namespace CechCohomology

noncomputable def cechComplexFunctor {I : Type w} (U : I → C)
    [HasFiniteProducts C] [Preadditive A] :
    (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ := sorry

theorem nonempty_affineOpenCover (X : Scheme.{u}) : Nonempty (Scheme.AffineOpenCover.{u} X) := by
  choose R i h using @AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset (X := X)
  exact ⟨{
    J := X
    obj x := R (trivial : x ∈ ⊤) 
    map x := i (trivial : x ∈ ⊤)
    f := id
    covers x := by aesop
    map_prop x := (h (trivial : x ∈ ⊤)).1
  }⟩

#check ModuleCat.restrictScalars
def foo {X : Scheme} (R : CommRingCat) [X.CanonicallyOver (Spec R)]
    (F : SheafOfModules ((sheafCompose (Opens.grothendieckTopology ↥X)
    (forget₂ CommRingCat RingCat)).obj X.sheaf)) :
  X.Opensᵒᵖ ⥤ ModuleCat R where
    obj U := by
      let f := X ↘ Spec R
      sorry
    map := sorry
    map_id := sorry
    map_comp := sorry
  

noncomputable
def arbitraryAffineOpenCover (X : Scheme.{u}) := Nonempty.some <| nonempty_affineOpenCover X
/--
A stand in for the Euler characteristic of a sheaf F on a space, defined as:
χ(F) = ∑ (i : ℕ), (-1)^i h^i(X, F).

This is currently just a black box that produces an integer given a sheaf F. Currently it's
definitely at the wrong level of generality.

This is for a couple of reasons. For one, for Riemann Roch we're only going to be concerned with
the truncated Euler Characteristic `h⁰ - h¹`. This will avoid having to prove Serre finiteness.

This should also potentially not be a notion which is dependant on the
sheaf of rings (and it probably also shouldn't be dependant on the Grothendick topology). It's
also unclear this should take in a sheaf of modules at all. Indeed, the Cech cohomology is defined
-/
def χ {X : Scheme} {k : Type*} [Field k] [X.CanonicallyOver (Spec (CommRingCat.of k))]
  (F : SheafOfModules ((sheafCompose (Opens.grothendieckTopology ↥X)
  (forget₂ CommRingCat RingCat)).obj X.sheaf))
  : ℤ := HomologicalComplex.eulerChar₁ (R := k) <|
    let 𝒰 := arbitraryAffineOpenCover X
    (cechComplexFunctor _ 𝒰.openSet).obj <| _


--def χ {Y : TopCat} (F : TopCat.Presheaf AddCommGrp Y) : ℤ := sorry

end CechCohomology
