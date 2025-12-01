import Mathlib
import RiemannRoch.SheafOfModules.Nonempty
import RiemannRoch.SheafOfModules.Subsheaf
import RiemannRoch.SheafOfModules.Constant
import RiemannRoch.AlgebraicCycle.Basic
import RiemannRoch.AlgebraicCycle.Principal

universe u

open AlgebraicGeometry CategoryTheory
structure LinearLocalPredicateNE {X : Scheme.{u}} (F : X.Modules) where
    P {U : X.Opens} [Nonempty ↥U] (f : Γₘ(F, U)) : Prop
    zero {U : X.Opens} [Nonempty ↥U] : P (0 : Γₘ(F, U))
    add {U : X.Opens} [Nonempty ↥U] {f g : Γₘ(F, U)} (hf : P f) (hg : P g) : P (f + g)
    smul {U : X.Opens} [Nonempty ↥U] (a : Γ(X, U)) {f : Γₘ(F, U)} (hf : P f) : P (a • f)
    res {U V : X.Opens} [Nonempty ↥U] [Nonempty ↥V] (k : V ≤ U) (f : Γₘ(F, U)) (hf : P f) :
      P (F.val.presheaf.map (homOfLE k).op f)
    local_prop {U : X.Opens} [Nonempty ↥U] (f : Γₘ(F, U)) :
      (∀ x ∈ U, ∃ (V : X.Opens) (_ : Nonempty ↥V) (k : V ≤ U) (_ : x ∈ V), P <| F.val.presheaf.map (homOfLE k).op f)
      → P f
/-
Again it might be helpful to have these only be defined for the nonempty sets,
then we can easily define what we want.

I think to be honest anything less than just writing {s : X.functionField | blah}
is more or less unacceptable.

We should think about what the best thing to do here is. As Andrew pointed out,
using the constructor which lifts a sheaf of abelian groups to a sheaf of modules
is kind of the correct way to talk about sheaves of the kind we're talking about.

I still think it's probably good to define this LinearLocalPredicate, but perhaps
we want the definition of the constant sheaf to be some lifted version of the
constant sheaf of Abelian groups.

Then we can probably use something like the existing constant sheaf notion, just
lifted from sheaves of abelian groups to sheaves of modules.


-/
open Classical in
def LinearLocalPredicateNE.toLinearLocalPredicate {X : Scheme.{u}} {F : X.Modules} (Pn : LinearLocalPredicateNE F) :
    LinearLocalPredicate F where
      P {U} f := if hU : Nonempty U then @Pn.P U hU f else True
      zero {U} := by
        split_ifs
        rename_i h
        exact @Pn.zero U h
        --sorry
      add {U} f g := by
        split_ifs
        rename_i h
        · exact @Pn.add U h f g
        · tauto
      smul {U} a f := by
        split_ifs
        rename_i h
        exact @Pn.smul U h a f
        tauto
      res {U V} k f := by
        split_ifs
        rename_i hU hV
        exact @Pn.res U V hU hV k f
        · tauto
        · rename_i hU hV
          obtain ⟨v, hv⟩ := hV
          exact (hU ⟨v, k hv⟩).elim
        · tauto
      local_prop {U} f := by
        split_ifs
        rename_i hU
        · have := @Pn.local_prop U hU f
          intro h
          simp_all
          sorry
        · simp



open Classical in
def LinearLocalPredicateNE.lineBundleProp {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (D : AlgebraicCycle X) :
    LinearLocalPredicateNE (sheafOfRationalFunctions X) where
      P {U} hU s :=
        letI s' := sectionNEToFunctionField U 0
        ((h : s' ≠ 0) → AlgebraicCycle.div s' h + D ≥ 0)
        /-
        have : Nonempty U := sorry
        /-
        TODO: Make some API which says takes in a rational function and produces for you
        a section of the constant sheaf of rational functions.
        -/
        simp [sheafOfRationalFunctions, presheafOfRationalFunctions, constantPresheaf, constantPresheafNE] at s
        sorry-/
      zero {U} x hx := False.elim <| hx <| sectionNEToFunctionField_zero U
      add {U} hU f g hf hg hfg:= by
        /-
        I guess we just want to have a bunch of lemmas saying that this map behaves
        as we want it to. I think the sheaf condition should come down to
        some very similar reasonining to what we've already done for the other thing.
        -/

        sorry
      smul := sorry
      res := sorry
      local_prop := sorry

noncomputable
def lineBundle {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (D : AlgebraicCycle X) :=
    (LinearLocalPredicateNE.lineBundleProp D).toLinearLocalPredicate.sheaf


/-
One thing that slightly worries me is that this definition will not allow for as nice notation.
I.e. elements of 𝒪ₓ(U) are now not definitionally equal to rational functions, which is
maybe a bit sad.
-/


/-
Should we instead define the constant sheaf of rational functions by lifting this construction?
-/
noncomputable
def ratSheaf : TopCat.Sheaf Ab X := (constantSheaf (Opens.grothendieckTopology X) Ab).obj
    (.of X.functionField)

universe u₁ v₁
noncomputable
def SheafOfModules.ofSheaf {C : Type u₁} [Category.{v₁, u₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat) (M : Cᵒᵖ ⥤ Ab)
  (hM : Presheaf.IsSheaf J M)
  [(X : Cᵒᵖ) → Module ↑(R.val.obj X) ↑(M.obj X)]
  (map_smul :
    ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (r : ↑(R.val.obj X)) (m : ↑(M.obj X)),
      (ConcreteCategory.hom (M.map f)) (r • m) =
        (ConcreteCategory.hom (R.val.map f)) r • (ConcreteCategory.hom (M.map f)) m) :
  SheafOfModules R where
    val := PresheafOfModules.ofPresheaf M map_smul
    isSheaf := hM

noncomputable
def ratPresheaf : TopCat.Presheaf Ab X where
  obj U := .of X.functionField
  map := sorry
  map_id := sorry
  map_comp := sorry


instance (X_1 : (TopologicalSpace.Opens ↥X)ᵒᵖ) :
  Module ↑(X.ringCatSheaf.val.obj X_1) ↑(ratSheaf.val.obj X_1) := by sorry

noncomputable
def ratSheafOfModules : X.Modules := by
  refine SheafOfModules.ofSheaf (X.ringCatSheaf) ratSheaf.val ratSheaf.cond ?_
  sorry
