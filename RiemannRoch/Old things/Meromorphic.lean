import Mathlib
import RiemannRoch.LocallyFreeSheaf

open AlgebraicGeometry
universe u v

open CategoryTheory MonoidalCategory Limits

namespace SheafOfModules

section experiment

--variable {C : Type u} (F : Cᵒᵖ ⥤  )


end experiment

variable {C : Type u} [CategoryTheory.Category C]
         {J : CategoryTheory.GrothendieckTopology C} {R : CategoryTheory.Sheaf J RingCat.{v}}

#check R ⊗ R


variable {C : Type u} [CategoryTheory.Category C]
         {J : CategoryTheory.GrothendieckTopology C} {R : CategoryTheory.Sheaf J RingCat.{v}}
         (M : SheafOfModules.{v} R)
         [h1 : ∀ (X : C), (J.over X).HasSheafCompose (CategoryTheory.forget₂ RingCat AddCommGrp)]
         [h2 : ∀ (X : C), CategoryTheory.HasWeakSheafify (J.over X) AddCommGrp]
         [h3 : ∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrp]

namespace AlgebraicGeometry

open SheafOfModules
namespace RingedSpace

structure regularSection (U : Cᵒᵖ) where
  sec := R.val.obj U
  is_regular :=
    have : Ring ((R.val.obj U).carrier) := by infer_instance
    /-
    Should have something like the below statement, but there are some typeclass issues
    preventing things from being well typed.

    This could be fixed by making R a sheaf of commutative rings rather than just a
    sheaf of rings, but it feels like this is the correct level of generality. That said,
    I don't care about sheaves of noncommutative rings so maybe it's not the worst thing
    in the world.
    -/
    Function.Injective (LinearMap.mulLeft (R.val.obj U).carrier (R.val.obj U).carrier sec)

/-
lemma : regular sections form a multiplicative subset of R(U)
-/

/-
def : the sheaf of meromorphic sections of a sheaf F is the sheafification of
U ↦ S(U)⁻¹F(U)
-/

/-
def : the order of vanishing of a meromorphic section of an invertible sheaf at a
point
-/


/-
Note: On an integral scheme, the constant sheaf of the stalk of F at the generic point
is the same as the sheaf of meromorphic sections.

That works for me I think. Then we can fairly easily prove that any invertible sheaf
has a nontrivial meromorphic section.

So, we just need to define the divisor associated to an element of F localized at eta.
We just do the same procedure as before, taking order of vanishing and so on.
-/

/-
def : divisor of a meromorphic section.
-/

/-
theorem : any
-/
variable (X : RingedSpace)
         [∀ (X_1 : TopologicalSpace.Opens ↑↑X.toPresheafedSpace),
          ((Opens.grothendieckTopology ↑↑X.toPresheafedSpace).over X_1).WEqualsLocallyBijective AddCommGrp]
         (M : SheafOfModules ((sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf))
