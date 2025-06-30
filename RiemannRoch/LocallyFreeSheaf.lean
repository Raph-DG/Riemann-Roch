import Mathlib

/-!
# Locally free sheaves

in this file we define locally free sheaves as quasicoherent sheaves with trivial presentations.
We define invertible sheaves as a special case.

We conclude by showing that the invertible sheaves form a group under
taking tensor products.

To do this, we should show that any
-/

open AlgebraicGeometry
universe u v

open CategoryTheory MonoidalCategory Limits

namespace SheafOfModules

variable {C : Type u} [CategoryTheory.Category C]
         {J : CategoryTheory.GrothendieckTopology C} {R : CategoryTheory.Sheaf J RingCat.{v}}
         (M : SheafOfModules.{v} R)
         [h1 : ∀ (X : C), (J.over X).HasSheafCompose (CategoryTheory.forget₂ RingCat AddCommGrp)]
         [h2 : ∀ (X : C), CategoryTheory.HasWeakSheafify (J.over X) AddCommGrp]
         [h3 : ∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrp]

class IsLocallyFree : Prop extends IsQuasicoherent M where
  locally_trivial : ∃ p : M.QuasicoherentData, ∀ i : p.I, IsZero (kernel (p.presentation i).generators.π)


structure Trivialization where
  I : Type u
  X : I → C
  coversTop : J.CoversTop X
  K (i : I) : Type v
  free (i : I) : (SheafOfModules.free (K i)) ≅ (M.over (X i))

lemma isLocallyFree_iff_exists_trivialization : IsLocallyFree M ↔ Nonempty (Trivialization M) := by
  constructor
  · intro h

    obtain ⟨q, hq⟩ := h.locally_trivial
    let t : Trivialization M := {
      I := q.I
      X := q.X
      coversTop := q.coversTop
      K i := (q.presentation i).generators.I
      free i :=
        let f := (q.presentation i).generators.π

          /-(@SheafOfModules.freeHomEquiv _ _ _ _ (h2 (q.X i)) (h3 (q.X i)) (h1 (q.X i))
                 (M.over (q.X i))
                 ((q.presentation i).generators.I)).symm ((q.presentation i).generators.s)-/
        have : IsIso f := by
          have : Mono f := by exact Preadditive.mono_of_isZero_kernel f (hq i)
          have : Epi f := (q.presentation i).generators.epi
          have := h1 (q.X i)
          refine @CategoryTheory.isIso_of_mono_of_epi _ _ ?_ _ _ f _ _
          /-
          TODO: This holds for Abelian categories, but either typeclass inference is messing up
          or we do not have an Abelian category, the culprit probably being that R just goes
          to RingCat rather than CommRingCat.
          -/
          sorry
        asIso f
    }
    exact Nonempty.intro t
  · intro h
    obtain ⟨I, X, ct, K, fr⟩ := h
    let ans : M.IsLocallyFree := {
      nonempty_quasicoherentData := by
        let l : M.QuasicoherentData := {
          I := I
          X := X
          coversTop := ct
          presentation i := {
            generators := {
              I := (K i)
              s := @SheafOfModules.freeHomEquiv _ _ _ _ (h2 (X i)) (h3 (X i)) (h1 (X i)) (M.over (X i)) _ (fr i).hom
              epi := by
                specialize fr i

                /-
                This should just follow from the fact that f is an isomorphism
                -/
                sorry
            }
            relations := sorry
          }
        }
        exact Nonempty.intro l
      locally_trivial := by

        sorry
    }
    exact ans


/-
We should have that free sheaves are locally free, but I'm having a bit of trouble representing
this statement because of lack of understanding of the API. TODO

lemma isLocallyFree_free (X : C) (I : Type) : IsLocallyFree (@SheafOfModules.free C _ J R (h2 X) _ _ I) := sorry
-/
end SheafOfModules

namespace AlgebraicGeometry

open SheafOfModules
namespace RingedSpace


variable (X : RingedSpace)
         [∀ (X_1 : TopologicalSpace.Opens ↑↑X.toPresheafedSpace),
          ((Opens.grothendieckTopology ↑↑X.toPresheafedSpace).over X_1).WEqualsLocallyBijective AddCommGrp]
         (M : SheafOfModules ((sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf))

lemma isLocallyFree_iff_exists_nhd : IsLocallyFree M ↔ ∀ x : X, ∃ I : Type, ∃ U : TopologicalSpace.Opens X,
  x ∈ U ∧ Nonempty (M.over U ≅ SheafOfModules.free I) := sorry

/-
The stalk of a sheaf of modules over R is an R module

Note this may not be the right level of generality, should be stated in terms of R modules.
-/
instance (x : X) :
  Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk M.val.presheaf x).carrier := sorry

/--
Rank of a locally free sheaf
-/
@[stacks 01C9]
noncomputable
def rank (x : X) :=
  Module.rank (X.presheaf.stalk x) (TopCat.Presheaf.stalk M.val.presheaf x).carrier

variable [IsLocallyFree M]

/--
The stalk of a locally free sheaf is free.

Proof: Take a neighbourhood around x where M is free, then localize this at x.
-/
lemma IsLocallyFree.stalkFree (x : X) :
  Module.Free (X.presheaf.stalk x) (TopCat.Presheaf.stalk M.val.presheaf x).carrier := sorry


end RingedSpace

/-

-/
end AlgebraicGeometry
