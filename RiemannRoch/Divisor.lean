import Mathlib
import RiemannRoch.CodimLemma
import RiemannRoch.AlgebraicCycle.Basic
import RiemannRoch.AlgebraicCycle.Principal

/-!
# Weil Divisors

In this file we define the notion of Weil divisors and construct the sheaf 𝒪(D), defining it on U
to be rational functions such that (f) + D ≥ 0 on U.

This definition gives good results on Noetherian, integral separated schemes which are regular in
codimension 1. Since our main goal is proving Riemann Roch for curves this should be enough power
for us, but we should in the future extend these results.
-/


open AlgebraicGeometry

open CategoryTheory
open Opposite.op
open Order
open AlgebraicCycle
open Opposite

universe u v
variable {X : Scheme.{u}}
         [IsIntegral X]
         [IsLocallyNoetherian X]


noncomputable
def AlgebraicGeometry.Scheme.dimension (X : Scheme.{u}) : ℕ∞ :=
  WithBot.unbot (topologicalKrullDim X) sorry

/--
This is a slightly nonstandard definition of what it means to be catenary, and it is
mainly stated here because we will need this assumption to show that principal divisors
(defined with respect to the coheight) are indeed divisors (i.e. cycles of dimension n-1).
-/
class Catenary (X : Scheme.{u}) where
  dimension_coheight (x : X) : coheight x = X.dimension - height x


open Classical in
/--
Given `U ⊆ V` and a fucntion locally finite on `U`, we produce a function locally finite
on `V` by taking the original value of the function on `U` and taking `0` elsewhere.
-/
noncomputable
def _root_.Function.locallyFinsuppWithin.extend {X Y : Type*} [TopologicalSpace X] {U : Set X}
  [Zero Y] {V : Set X} (D : Function.locallyFinsuppWithin V Y) (h : V ⊆ U) :
   Function.locallyFinsuppWithin U Y where
     toFun x := if x ∈ V then D x else 0
     supportWithinDomain' := by aesop
     supportLocallyFiniteWithinDomain' := by
      intro z hz
      by_cases o : z ∈ V
      · obtain ⟨W, hW⟩ := D.supportLocallyFiniteWithinDomain' z o
        use W
        refine ⟨hW.1, Set.Finite.subset hW.2 ?_⟩
        suffices (Function.support fun x ↦ if x ∈ V then D x else 0) ⊆ D.support by exact Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) this
        simp [@Function.support_subset_iff]
      ·
        sorry
      /-
      if z ∈ V, then we have this automatically by D.supportLocallyFiniteWithinDomain'. But I can't
      think of the argument in general for why this should work for a point outside of U.

      Here is the argument I think. Take an element z ∈ U \ V. Then, take some nhd W of z. For every
      point in W that is in U, take a nhd ...


      I don't know how we avoid taking an infinite intersection here. I'm starting to doubt this
      works.

      Take ℝ² with the usual topology, take V to be the open unit disc and V to be the disc of
      radius 2 centred at the origin. Then, take our D to have support at (0, 0), (1/2, 0),
      (3/4, 0), (7/8, 0),....

      I.e. a sequence of points clusering up near (1, 0). This should be locally finite in V,
      because at every point of V there is a nhd hitting only finitely many guys.

      Then, extend this to U by taking the value everywhere outside of V to be 0. We then get
      that at (1, 0) we're no longer locally finite.

      So that's that I suppose, I really can't see a good way of fixing this unfortunately. One
      way is to just work with finite rather than locally finite and restrict ourselves to the
      quasicompact situation.
      -/



open Function locallyFinsuppWithin
/--
Below we define the sheaf 𝒪(D) associated with a Weil divisor. We note that strictly speaking you
don't need the input cycle to be a divisor, so in this definition we just assume D is an arbitrary
cycle.
-/
def AlgebraicCycle.lineBundle (D : AlgebraicCycle X) (U : X.Opens) :=
  {s : (X.functionField) |
    (h : s ≠ 0) → (div s h) + .extend (restrict (V := U) (D) (by simp)) (by simp) ≥ 0}

/--
This should be a concrete definition of 𝒪(D) ⊗ 𝒪(D'). I think this is more or less
what we would get from just using the notion of sheafification for prelocal properties.

What I like about this definition is the elements are just elements of the function field,
which makes me think we could have a really nice notation for multiplying sections which
plays nicely with the tensor product basically for free.
-/
def AlgebraicCycle.lineBundleTProd (D D': AlgebraicCycle X) (U : X.Opens) :=
  {s : X.functionField | ∀ z ∈ U, ∃ V : X.Opens, V.1 ⊆ U.1 ∧ z ∈ V.1 ∧
   ∃ f : D.lineBundle V, ∃ g : D'.lineBundle V, s = f * g}

/--
We can now define what we mean by 𝒪(D + D') = 𝒪(D) ⊗ 𝒪(D')
-/
lemma AlgebraicCycle.picGroup (D D' : AlgebraicCycle X) (U : X.Opens) :
 AlgebraicCycle.lineBundleTProd D D' U = (D + D').lineBundle U := sorry

/-
The question, of course, it what's the utility of having this? Indeed, this is
only useful for RR if we can say somehow that this tensor product operation is exact. The
main problem being that it's unclear precisely what "exact" means in this context.

For that, I think we really will need the module structure, so we can't avoid the work =
below so easily.
-/

/--
This should eventually be proven. That said, it's unclear if we actually need this for RR,
it really depends on how we do tensor product. Of course, if we want to do the most direct
thing, then we have no choice but to prove this soon. However, if we just make some
construction of the tensor product of two line bundles as things which are locally products
of sections, then we could also avoid basically any business dealing with quasicoherent sheaves.
-/
noncomputable
def AlgebraicCycle.lineBundleAddSubgroup (D : AlgebraicCycle X) (U : X.Opens) :
    AddSubgroup (X.functionField) where
  carrier := {s : (X.functionField) |
    (h : s ≠ 0) → Function.locallyFinsuppWithin.restrict (V := U) ((div s h) + D) (by simp) ≥ 0}
  add_mem' := by
    /-
    We're trying to show that if f and g are in our set, then f+g is.
    Now, if either one is zero (say g = 0), then f + g = f which satisfies the property by assumption

    If neither are 0, we need to show that if (f) + D ≥ 0 and (g) + D ≥ 0 then (f + g) + D ≥ 0.
    I.e. for all x, (f + g) x + D x ≥ 0. (f + g) x = ordₓ (f + g).

    Should have ordₓ (f + g) = max (ordₓ(f), ordₓ(g)) or something? Well this can't be right,
    x + 1 does not vanish at 0 but x does. So this formula only holds if there is a root/pole at
    x. I think we should then have that ordₓ(f + g) = ordₓ(f) ∨ ordₓ(g).

    At the very least, we know that (a + b) ⊆ (a) + (b). This means that
    length (R / (a+b)) ≤ length (R / (a) + (b)) =?

    0 -> (b) -> R / (a) -> R / (a) + (b) -> 0

    WHat is ord (b)?? Is it the same thing as ord b? Well, submodules of R / (b)

    => ord a = ord b + m so m = ord a. It's not ord b because we needed to be able to say
    that b is an idela of R / (a), menaing it is contained in (a). So, we really need one
    contained in the other for this argument.
    -/
    intro a b ha hb
    simp_all
    intro h
    wlog o : ¬ a = 0 ∧ ¬ b = 0
    ·
      refine this D U ha hb h ?_
      /-
      wlog ¬ a = 0 ∧ b = 0
      -/
      sorry
    · sorry
  zero_mem' := sorry
  neg_mem' := sorry


instance (D : AlgebraicCycle X) (U : X.Opens) :
         Module (X.sheaf.val.obj (op U)) (D.lineBundleAddSubgroup U) := sorry

def AlgebraicCycle.lineBundleSheaf (D : AlgebraicCycle X) :
  SheafOfModules ((sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf) where
    val := {
      obj U := by
        simp
        sorry
        --exact ModuleCat.of (X.sheaf.val.obj U) (D.rationalSections (Opposite.unop U))
      map := sorry
      map_id := sorry
      map_comp := sorry
    }
    isSheaf := sorry

macro:max "𝒪(" D:term ")": term =>
  `(AlgebraicCycle.lineBundleSheaf $D)

noncomputable
def WeilDivisor (X : Scheme.{u}) := HomogeneousAddSubgroup X (X.dimension - 1)


variable [Catenary X]
