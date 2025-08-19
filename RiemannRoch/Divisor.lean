import Mathlib
import RiemannRoch.CodimLemma
import RiemannRoch.AlgebraicCycle.Basic
import RiemannRoch.AlgebraicCycle.Principal
import RiemannRoch.OrderOfVanishing.OrdLemmas
import RiemannRoch.OrderOfVanishing.DVR
import RiemannRoch.CodimLemma

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
         --(D : Function.locallyFinsuppWithin (⊤ : Set X) ℤ)

noncomputable
/-
This definition is currently sorried because I'm not sure if I always want to assume that
the schemes we're talking about are nonempty (which the typesignature of this definition
implicitly assumes). This is mainly just here to make statements relating the dimension
and codimension cleaner to state.
-/
def AlgebraicGeometry.Scheme.dimension (X : Scheme.{u}) : ℕ∞ :=
  WithBot.unbot (topologicalKrullDim X) sorry

/--
This is a slightly nonstandard definition of what it means to be catenary, and it is
mainly stated here because we will need this assumption to show that principal divisors
(defined with respect to the coheight) are indeed divisors (i.e. cycles of dimension n-1).
-/
class Catenary (X : Scheme.{u}) where
  dimension_coheight (x : X) : coheight x = X.dimension - height x

/-
open Classical in
/--
We note that this is distinct from locallyFinSuppWithin.restrict, since here we're restricting
a function which is globally locally finite to some open set, and again getting something which
is globally locally finite.
-/
noncomputable
def AlgebraicCycle.restrict (D : AlgebraicCycle X) (U : X.Opens) : AlgebraicCycle X where
  toFun x := if x ∈ U then D x else 0
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' := by
    intro z hz
    obtain ⟨W, hW⟩ := D.supportLocallyFiniteWithinDomain' z hz
    use W
    refine ⟨hW.1, ?_⟩
    apply Set.Finite.subset hW.2
    suffices (Function.support fun x ↦ if x ∈ U then D x else 0) ⊆
      Function.support D.toFun from Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) this
    aesop-/
#check Function.locallyFinsuppWithin.restrict
open Function locallyFinsuppWithin

noncomputable
def Function.locallyFinsuppWithin.restrict'.{u_1, u_2} {X : Type u_1} [TopologicalSpace X] (U : Set X) {Y : Type u_2}
  [Zero Y] {V : Set X} (D : Function.locallyFinsuppWithin U Y) (h : V ⊆ U) : Function.locallyFinsuppWithin V Y := Function.locallyFinsuppWithin.restrict D h

/--
Below we define the sheaf 𝒪(D) associated with a Weil divisor. We note that strictly speaking you
don't need the input cycle to be a divisor, so in this definition we just assume D is an arbitrary
cycle.
-/
def AlgebraicCycle.lineBundle (D : AlgebraicCycle X) (U : X.Opens) :=
  {s : (X.functionField) | (h : s ≠ 0) → (div s h).restrict (by aesop : U.1 ⊆ ⊤) + D.restrict (by aesop : U.1 ⊆ ⊤) ≥ 0}

lemma _root_.locallyFinsuppWithin.restrict_eq_within {Y : Type*} [TopologicalSpace Y] {U : Set Y}
    {Z : Type*} [Zero Z] {V : Set Y} (D : locallyFinsuppWithin U Z)
    (h : V ⊆ U) (z : Y) (hz : z ∈ V) :
  D.restrict h z = D z := dif_pos hz

lemma _root_.locallyFinsuppWithin.restrict_eq_zero {Y : Type*} [TopologicalSpace Y] {U : Set Y}
    {Z : Type*} [Zero Z] {V : Set Y} (D : locallyFinsuppWithin U Z)
    (h : V ⊆ U) (z : Y) (hz : z ∉ V) :
  D.restrict h z = 0 := dif_neg hz

/--
This should be a concrete definition of `𝒪(D) ⊗ 𝒪(D')` (though I have no reference for this so
it's possible this is a mistake). I think this is more or less
what we would get from just using the notion of sheafification for prelocal properties. However,
this API is written in terms of concrete functions, and here we have elements of the function
field.

What I like about this definition is the elements are just elements of the function field,
which makes me think we could have a really nice notation for multiplying sections which
plays nicely with the tensor product basically for free. That said, this might also be painless
if we just use the tensor product of sheaves of modules on the nose (this, however, does not
exist at the time of writing without a bit more work).
-/
def AlgebraicCycle.lineBundleTProd (D D': AlgebraicCycle X) (U : X.Opens) :=
  {s : X.functionField | ∀ z ∈ U, ∃ V : X.Opens, V.1 ⊆ U.1 ∧ z ∈ V.1 ∧
   ∃ f : D.lineBundle V, ∃ g : D'.lineBundle V, s = f * g}

/--
We can now define what we mean by 𝒪(D + D') = 𝒪(D) ⊗ 𝒪(D'). I believe this should be an equality
on the nose with the definitions we have set up, rather than just being an isomorphism.
-/
lemma AlgebraicCycle.picGroup (D D' : AlgebraicCycle X) (U : X.Opens)
    (h : ∀ x : X, coheight x = 1 → UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    AlgebraicCycle.lineBundleTProd D D' U = (D + D').lineBundle U := by
  simp[lineBundleTProd, lineBundle]
  ext a
  simp only [Set.mem_setOf_eq]
  constructor
  · /-
    Any function which is locally a product of sections of D and D' is globally a section of D + D'.
    -/
    intro h ha z
    by_cases o : z ∈ U
    · specialize h z o
      obtain ⟨V, VinU, zinV, hV⟩ := h
      obtain ⟨f, hf⟩ := hV
      obtain ⟨hf, hf2⟩ := hf
      obtain ⟨g, hg, afg⟩ := hf2
      subst afg
      have fnez : f ≠ 0 := left_ne_zero_of_mul ha
      specialize hf fnez z
      have gnez : g ≠ 0 := right_ne_zero_of_mul ha
      specialize hg gnez z

      simp [locallyFinsuppWithin.restrict_eq_within _ _ _ o]
      simp [locallyFinsuppWithin.restrict_eq_within _ _ _ zinV] at hf hg
      rw [div_homomorphism f fnez g gnez]
      simp_all
      omega
    · simp [locallyFinsuppWithin.restrict_eq_zero _ _ _ o]
  · /-
    This part is a bit more tricky. Given a section `s` of `𝓞(D + D')`, we need to show that for any
    `z : X`, there is a neighbourhood around which `s = f*g`, where `f` and `g` are sections of
    `𝒪(D)` and `𝒪(D')` respectively.

    In order to do this, we probably need that all local rings are UFDs.
    This implies that there is some neighbourhood `U` around `z` where `s` is of the form `(h)|ᵤ`
    for some rational function `h`. We also know in this context that all prime divisors of `U`
    are just given by the prime ideals of `U`, and that these are all principal.
    So we can factorise our rational function `h` using  the generators of these ideals.

    It is necessary to get this nhd where we have something precisely principal. For example, if
    we take X to be the projective line, D = -(0), D' = (0), then we want to work in U = X \ {∞}
    so that we can guarantee that (x) + D ≥ 0 (since otherwise it would have a pole).
    -/
    intro h z hz
    /-
    We wish to say that there is a nhd around z where D is principal, and one where D' is principal
    -/


    /-
    The existence of these neighbourhoods should follow from the fact that all local rings are UFDs.
    Namely, there should be some affine nhd around z which is a UFD, and hence
    -/
    have ex1 : ∃ U1 : X.Opens, ∃ f : X.functionField, ∃ hf : f ≠ 0,
        z ∈ U1 ∧ restrict D (by aesop : U1.1 ⊆ ⊤) = restrict (div f hf) (by aesop : U1.1 ⊆ ⊤) := sorry


    have ex2 : ∃ U2 : X.Opens, ∃ g : X.functionField, ∃ hg : g ≠ 0,
        z ∈ U2 ∧ restrict D' (by aesop : U2.1 ⊆ ⊤) = restrict (div g hg) (by aesop : U2.1 ⊆ ⊤) := sorry
    obtain ⟨U1, f, fnez, zinU1, hf⟩ := ex1
    obtain ⟨U2, g, gnez, zinU2, hg⟩ := ex2

    /-
    Suppose a = x, f = 2/x and g = x^2. Then, f*g = 2x, which has the same vanishing as a but is
    not a.

    Suppose ord (f/g) = ord (h/k) ↔ ord f - ord g = ord h - ord k.


    In a fraction ring over a UFD, elements have a reduced fraction form (meaning the numerator
    and denominator are relatively prime). I claim that these reduced fractions must differ by the
    algebra map of a unit. If this is true, then we can take reduced fractions of `a` and `f*g`
    to get that `a = u*(f*g)`, and so we can take `u*f` for our first function and `g` for our
    second (or vice versa). This I think will prove our result.
    -/

    use U ⊓ U1 ⊓ U2
    constructor
    · refine inf_le_of_left_le ?_
      refine inf_le_of_left_le ?_
      exact fun ⦃a⦄ a ↦ a
    · constructor
      · simp_all
      · use f
        constructor
        · intro hf
          sorry
        · use g
          constructor
          · sorry
          ·
            /-


            This may not be true, so I don't think we can use f and g on the nose. However, I think
            it's true that a and f*g can only differ by multiplciation by a unit.

            So we want some lemma saying (f) = (g) ↔ <f> = <g>. However, what precisely do we mean
            by this? Potentially we want to say that f and g differ by scalar multiplication by
            an element of `Γ(X, V)` (where `V` is the set where all these things are defined).

            I doubt it, since in an affine nhd, we certainly can't multiply by any function without
            changing the order of vanishing.

            I think we need to show the existence of an actual regular function, and we need U1 and
            U2 to be affine. The problem is, if we need to do this then this method doesn't work,
            since this would


            At this point we know that (a) = (f * g), and I claim that this should mean that this
            must mean that there is some u1 and u2 such that a = u1*f * u2*g. So we need to come
            up with even more order of vanishing api I think.
            -/

            sorry


variable (h' : ∀ x : X, coheight x = 1 → IsDiscreteValuationRing (X.presheaf.stalk x))
variable (V : X.Opens)



/-
The function field is not a module over the zero ring since any module over the zero ring must be
a zero module.
-/
#check Γ(X, ⊥)
set_option maxHeartbeats 0
/--
Here we construct the sections of 𝒪(D) over a nonempty open set U.
-/
noncomputable
def AlgebraicCycle.lineBundleModule
    (D : AlgebraicCycle X) (U : X.Opens) [Nonempty U] :
    Submodule Γ(X, U) X.functionField where
  carrier := {s : (X.functionField) | (h : s ≠ 0) → (div s h).restrict (by aesop : U.1 ⊆ ⊤) +
              D.restrict (by aesop : U.1 ⊆ ⊤) ≥ 0}
  add_mem' := by
    intro a b ha hb
    simp_all
    intro h
    by_cases ha0 : a = 0
    · simp_all
    by_cases hb0 : b = 0
    · simp_all
    intro Z
    specialize ha ha0 Z
    specialize hb hb0 Z
    simp_all
    have hU : U.1 ⊆ ⊤ := by aesop
    suffices min ((div a ha0).restrict hU Z) ((div b hb0).restrict hU Z) ≤
             (div (a + b) h).restrict hU Z by omega

    by_cases hZ : coheight Z = 1
    · have := krullDimLE_of_coheight hZ
      by_cases o : Z ∈ U
      · simp [locallyFinsuppWithin.restrict_eq_within _ _ _ o,
              div_eq_ord_of_coheight_eq_one _ _ _ hZ, Scheme.ord]
        have : IsDiscreteValuationRing ↑(X.presheaf.stalk Z) := h' Z hZ
        have := ordFrac_add (R := X.presheaf.stalk Z) a b
        simp_all
      · simp [locallyFinsuppWithin.restrict_eq_zero _ _ _ o]
    · by_cases o : Z ∈ U
      · simp only [TopologicalSpace.Opens.carrier_eq_coe, Set.top_eq_univ,
        locallyFinsuppWithin.restrict_eq_within _ _ _ o, inf_le_iff]
        rw[div_eq_zero_of_coheight_ne_one _ _ _ hZ, div_eq_zero_of_coheight_ne_one _ _ _ hZ,
          div_eq_zero_of_coheight_ne_one _ _ _ hZ]
        simp
      · simp [locallyFinsuppWithin.restrict_eq_zero _ _ _ o]
  zero_mem' := by aesop
  smul_mem' := by
    intro a f hf nez z
    simp_all
    have h : ¬ f = 0 := by aesop (add simp nez)
    specialize hf h z
    simp at hf
    have hU : U.1 ⊆ ⊤ := by aesop
    suffices (div f h).restrict hU z ≤ (div (a • f) nez).restrict hU z by
      trans (div f h).restrict hU z + D.restrict hU z
      · exact hf
      · exact
        (Int.add_le_add_iff_right
              ((locallyFinsuppWithin.restrict D (of_eq_true (Set.subset_univ._simp_1 ↑U))) z)).mpr
          this
    by_cases hz : coheight z = 1
    · by_cases o : z ∈ U
      · simp [locallyFinsuppWithin.restrict_eq_within _ _ _ o,
        div_eq_ord_of_coheight_eq_one _ _ _ hz, Scheme.ord]

        let i := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, o⟩

        have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk z) := krullDimLE_of_coheight hz

        let test : IsScalarTower ↑Γ(X, U) ↑(X.presheaf.stalk z) ↑X.functionField :=
            AlgebraicGeometry.functionField_isScalarTower X U ⟨z, o⟩
        apply @ordFrac_le_smul _ _ _ _ _ _ _ _ _ _ _ _ _ test a ?_ f
        · suffices ((algebraMap ↑Γ(X, U) ↑(X.presheaf.stalk z)) a) • f ≠ 0 by
            exact left_ne_zero_of_smul this
          simpa [algebraMap_smul]
      · simp [locallyFinsuppWithin.restrict_eq_zero _ _ _ o]
    · by_cases o : z ∈ U
      · simp [locallyFinsuppWithin.restrict_eq_within _ _ _ o,
              div_eq_zero_of_coheight_ne_one _ _ _ hz]
      · simp [locallyFinsuppWithin.restrict_eq_zero _ _ _ o]

#check X.presheaf
noncomputable
def AlgebraicCycle.lineBundleSheaf (D : AlgebraicCycle X) : X.Modules
   where
    val := {
      obj U := by
        by_cases o : Nonempty ↑↑(unop U)
        · exact ModuleCat.of (↑(X.ringCatSheaf.val.obj U)) <| AlgebraicCycle.lineBundleModule h' D (unop U)
        · exact ModuleCat.of (↑(X.ringCatSheaf.val.obj U)) PUnit
      map := by
        intro U V r
        split_ifs
        · apply ModuleCat.ofHom (Y := (ModuleCat.restrictScalars
                (RingCat.Hom.hom (X.ringCatSheaf.val.map r))).obj
                (ModuleCat.of ↑(X.ringCatSheaf.val.obj V) ↥(lineBundleModule h' D (unop V))))
          exact {
            toFun := by
              rintro ⟨f, hf⟩
              refine ⟨f, ?_⟩
              simp [lineBundleModule] at hf ⊢
              intro fnez
              specialize hf fnez
              intro z
              by_cases o : z ∈ unop V
              · simp [locallyFinsuppWithin.restrict_eq_within _ _ _ o]
                specialize hf z
                have : z ∈ unop U := le_of_op_hom r o
                simpa [locallyFinsuppWithin.restrict_eq_within _ _ _ this] using hf
              · simp [locallyFinsuppWithin.restrict_eq_zero _ _ _ o]
            map_add' := by
              intro f g
              simp
              rfl
            map_smul' := by
              rintro f ⟨g, hg⟩
              simp
              /-
              Should be a matter of writing the right API lemmas
              -/
              sorry

          }
        ·
          -- V ⊆ U and V = ∅. Should have that Γ (X, V) = 0, and 0 is both initial and terminal
          -- which takes care of these trivial cases
          sorry
        · sorry
        · /-
          This should be a special case of the last two, but depending on how long they take it
          probably won't be that bad to just leave this case here
          -/
          sorry
      map_id := by

        sorry
      map_comp := sorry
    }
    isSheaf := by
      /-
      Let's think about what the proof of this should actually be. We wish to show that this
      is a sheaf, meaning that for any open cover U_i of X, if I have that local sections s_i
      for each U_i agreeing on overlaps, I can just patch it into a big thing.

      This should be simple because a section over any of these is just a rational function,
      and they should all be the same rational function. So this just amounts to verifying
      that on the big set s + D ≥ 0, which is true since s is just s_i on each U_i (and we're
      on an integral scheme so we don't have to worry about different connected components).

      Uniqueness should also be pretty simple since we're really just talking about equality.
      -/
      sorry

macro:max "𝒪(" D:term ")": term =>
  `(AlgebraicCycle.lineBundleSheaf $D)

noncomputable
def WeilDivisor (X : Scheme.{u}) := HomogeneousAddSubgroup X (X.dimension - 1)


variable [Catenary X]
