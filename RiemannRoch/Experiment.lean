import Mathlib

open CategoryTheory Limits

variable (I : Type*) [Category I]

open lp

/-
The following is meant to represent a formal limit of rings.
-/
structure PreScheme where
  --I : Type*
  cat : Cat
  data : cat ⥤ CommRingCat
  --cat : Category I
  --data : I ⥤ CommRingCat
#check Limits.pair
noncomputable
def Γ (X : PreScheme) : CommRingCat := limit X.data

def Spec (R : CommRingCat) : PreScheme where
  cat := Cat.chosenTerminal
  data := Cat.fromChosenTerminalEquiv.invFun R

lemma test (R : CommRingCat) : Γ (Spec R) = R := by
  #check Functor.const
  simp [Γ, Spec, Cat.fromChosenTerminalEquiv]
  /-
  The problem here is we're using an arbitrary choice of limit object, which is silly in this
  context since there's an obvious choice (namely R). I'm not quite sure what the best thing to
  do about that is in this context.
  -/

  sorry

/-
We define the notion of a refinement of a diagram F : I ⥤ C to be another category I' and functor
ref I' ⥤ I such that limit F ≅ limit (ref ⋙ F).

I'm hoping we can show that for a given functor F, the catgory of refinements has an initial object
(or maybe terminal object depending on which way the arrows turn out to go naturally).

It may be better to define this as a typeclass, i.e. [IsRefinement F ref] would be a very reasonable
thing to write.

My suspicion is that this notion has been developed by someone before but I can't find it anywhere.
I also suspect that my desire to always have some initial object is a little ambitious, but
hopefully it holds in cases we're interested in.

One hope is that we can define some function which refines a given input category, and under nice
assumptions this is a computationally reasonable thing to do. I then wish to basically only ever
compute limits of the refinement, and that we shouold be able to do this in a way that makes
intelligent choices in a context where we have chosen limits.
-/
structure Refinement {I C : Cat} [HasLimits C] (F : I ⥤ C) where
  I' : Cat
  ref : I' ⥤ I
  is_refinement : limit F ≅ limit (ref ⋙ F)
