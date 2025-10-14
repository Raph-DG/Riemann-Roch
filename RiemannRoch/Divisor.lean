import Mathlib
import RiemannRoch.CodimLemma
import RiemannRoch.AlgebraicCycle.Basic
import RiemannRoch.AlgebraicCycle.Principal
import RiemannRoch.OrderOfVanishing.Basic
import RiemannRoch.OrderOfVanishing.Properties
import RiemannRoch.CodimLemma

/-!
# Weil Divisors

In this file we define the notion of Weil divisors and construct the sheaf 𝒪(D), defining it on U
to be rational functions such that (f) + D ≥ 0 on U.

This definition gives good results on Noetherian, integral separated schemes which are regular in
codimension 1. Since our main goal is proving Riemann Roch for curves this should be enough power
for us, but we should in the future extend these results. Note that with a bit of care we can use
essentially the same approach without the integral assumption, however dropping other assumptions
requires a different approach (namely the approach covered in Hartshorne)
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

open Function locallyFinsuppWithin

lemma locallyFinsuppWithin.restrict_eq_within {Y : Type*} [TopologicalSpace Y] {U : Set Y}
    {Z : Type*} [Zero Z] {V : Set Y} (D : locallyFinsuppWithin U Z)
    (h : V ⊆ U) (z : Y) (hz : z ∈ V) :
  D.restrict h z = D z := dif_pos hz

lemma locallyFinsuppWithin.restrict_eq_zero {Y : Type*} [TopologicalSpace Y] {U : Set Y}
    {Z : Type*} [Zero Z] {V : Set Y} (D : locallyFinsuppWithin U Z)
    (h : V ⊆ U) (z : Y) (hz : z ∉ V) :
  D.restrict h z = 0 := dif_neg hz

variable (h' : ∀ x : X, coheight x = 1 → IsDiscreteValuationRing (X.presheaf.stalk x))

namespace AlgebraicCycle
namespace LineBundle

def carrier (D : AlgebraicCycle X) (U : X.Opens) : Set X.functionField :=
    {s : (X.functionField) | (h : s ≠ 0) → (div s h).restrict (by simp : U.1 ⊆ ⊤) +
    D.restrict (by simp : U.1 ⊆ ⊤) ≥ 0}

def add_mem (D : AlgebraicCycle X) (U : X.Opens) [Nonempty U] {a b : ↑X.functionField}
    (ha : a ∈ carrier D U) (hb : b ∈ carrier D U) : a + b ∈ carrier D U := by
    simp_all only [carrier]
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

def zero_mem (D : AlgebraicCycle X) (U : X.Opens) [Nonempty U] : 0 ∈ carrier D U := by
  simp [carrier]

def smul_mem (D : AlgebraicCycle X) (U : X.Opens) [Nonempty U] (a : Γ(X, U)) {f : X.functionField}
  (hf : f ∈ carrier D U) : a • f ∈ carrier D U := by
    simp_all only [carrier]
    intro nez z
    have h : ¬ f = 0 := by aesop (add simp nez)
    specialize hf h z
    simp only [TopologicalSpace.Opens.carrier_eq_coe, coe_zero, Pi.zero_apply, Set.top_eq_univ,
      coe_add, Pi.add_apply] at hf
    have hU : U.1 ⊆ ⊤ := by simp_all
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

def module
    (D : AlgebraicCycle X) (U : X.Opens) [Nonempty U] :
    Submodule Γ(X, U) X.functionField where
  carrier :=
    have : Algebra Γ(X, U) X.functionField :=
      instAlgebraCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensFunctionFieldOfNonemptyToScheme X U
    carrier D U
  add_mem' := add_mem h' D U
  zero_mem' := zero_mem D U
  smul_mem' := smul_mem D U

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
def tProdCarrier (D D': AlgebraicCycle X) (U : X.Opens) :=
  {s : X.functionField | ∀ z ∈ U, ∃ V : X.Opens, V.1 ⊆ U.1 ∧ z ∈ V.1 ∧
   ∃ f : carrier D V, ∃ g : carrier D' V, s = f * g}

/-
What do we want this tensor product for?

We really want to define a notion of the tensor product for the purposes of twisting
exact sequences. For the purpose, we want to define something like this:

def tProdCarrier (F G : Subsheaves of the constant sheaf of the function field) (U : X.Opens) :=
  {s : X.functionField | ∀ z ∈ U, ∃ V : X.Opens, V.1 ⊆ U.1 ∧ z ∈ V.1 ∧
    ∃ f : F V, ∃ g : G V, s = f*g}

We should also think about how 𝒪ₜ should be defined for some effective divisor t. I believe this
should just be the ideal sheaf of t, in which case it should be immediate that it is a subsheaf
of the sheaf of rational functions K.

I think this does indeed work, and that the below proofs really do represent the heart of the
difficulties involved in proving things about tensor products in the cases we care about.

I suppose we should also provide a proof that the tensor product of any subpresheaf of K with
an ideal sheaf is again just that ideal sheaf, and I think it will look sort of similar to the
below reasoning.

Once we have that, our final piece will be to show that this operation we've constructed is exact.
Of course, we could cheat a bit and just prove it's exact on sequences of the form
0 → 𝒪(-D) → 𝒪 → 𝒪D → 0.

I think we should consider writing some API generalising the current stuff about PreLocalPredicates.
We certainly should be able to express elements of the function field as being regular functions
which are not defined everywhere. (When I say regular functions here, I mean sections of 𝒪, but
in mathlib these are implemented as dependant functions from x : U to the stalk at x). I guess the
empty type is as good a type as any, so this approach should generalise to this context, though the
thought of implementing this stuff makes me very tired.
-/


/--
We can now define what we mean by 𝒪(D + D') = 𝒪(D) ⊗ 𝒪(D'). I believe this should be an equality
on the nose with the definitions we have set up, rather than just being an isomorphism.
-/
lemma picGroup (D D' : AlgebraicCycle X) (U : X.Opens) :
    tProdCarrier D D' U = carrier (D + D') U := by
  simp[tProdCarrier, carrier]
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
        z ∈ U1 ∧ restrict D (by simp : U1.1 ⊆ ⊤) = restrict (div f hf) (by simp : U1.1 ⊆ ⊤) := sorry


    have ex2 : ∃ U2 : X.Opens, ∃ g : X.functionField, ∃ hg : g ≠ 0,
        z ∈ U2 ∧ restrict D' (by simp : U2.1 ⊆ ⊤) = restrict (div g hg) (by simp : U2.1 ⊆ ⊤) := sorry
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

    /-
    Right, so at this point we have U1 in which D is (f), and U2 in which D' is (g), and U on which
    our section a of 𝒪(D + D') lives.

    We need to construct a as a product of elements of 𝒪(D) and 𝒪(D'). We should be able to say that on
    W := U ⊓ U1 ⊓ U2, we have that D|W = (f)|W, D'|W = (g)|W, so (D+D')|W = ((f) + (g))|W = (f*g)|W.

    At this point, we know that the order of vanising of a and f*g is going to be the same
    everywhere in W. I claim this should mean that a and f*g differ only by a unit u of Γ(X, W),
    so we can use u⁻¹ • f * g as our candidate.
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
            since this would mean we can't have sections with negative vanishing at z.


            At this point we know that (a) = (f * g), and I claim that this should mean that this
            must mean that there is some u1 and u2 such that a = u1*f * u2*g. So we need to come
            up with even more order of vanishing api I think.




            We know that for any z, ord f z = ord g z implies f and g differ by a unit in R
            in the local ring at R. We now need to lift that to something global.

            I'm wondering if we even need it in all local rings. E.g. if we have in the stalk
            at z that f = u • g, can this just be lifted globally?

            Well, this is true, but again not stritly what we want, since f and g may not literally
            be elements of the stalk at z, just elements of its fraction field.


            -/

            sorry

namespace Presheaf
open Classical in
noncomputable
def obj (D : AlgebraicCycle X) (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) :
    ModuleCat ↑(X.ringCatSheaf.val.obj U) :=
  if _ : Nonempty ↑↑(unop U)
  then ModuleCat.of (↑(X.ringCatSheaf.val.obj U)) <| module h' D (unop U)
  else ModuleCat.of (↑(X.ringCatSheaf.val.obj U)) PUnit

def obj_pos (D : AlgebraicCycle X) (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) [hU : Nonempty ↑↑(unop U)] :
    obj h' D U = (ModuleCat.of (↑(X.ringCatSheaf.val.obj U)) <| module h' D (unop U)) := dif_pos hU

def obj_neg (D : AlgebraicCycle X) (U : (TopologicalSpace.Opens ↥X)ᵒᵖ)
    (hU : ¬ Nonempty ↑↑(unop U)) :
    obj h' D U = ModuleCat.of (↑(X.ringCatSheaf.val.obj U)) PUnit := dif_neg hU

lemma mapPropertyNonempty (D : AlgebraicCycle X) {U V : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (r : U ⟶ V) [hU : Nonempty U.unop] [hV : Nonempty V.unop]
    (f : module h' D (unop U)) : ↑f ∈ module h' D (unop V) := by
  obtain ⟨f, hf⟩ := f
  simp [module]
  intro fnez
  specialize hf fnez
  intro z
  by_cases o : z ∈ unop V
  · simp [locallyFinsuppWithin.restrict_eq_within _ _ _ o]
    specialize hf z
    have : z ∈ unop U := le_of_op_hom r o
    simpa [locallyFinsuppWithin.restrict_eq_within _ _ _ this] using hf
  · simp [locallyFinsuppWithin.restrict_eq_zero _ _ _ o]

def mapFunNonempty (D : AlgebraicCycle X) {U V : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (r : U ⟶ V) [hU : Nonempty U.unop] [hV : Nonempty V.unop]
    (f : module h' D (unop U)) :
    ((ModuleCat.restrictScalars (RingCat.Hom.hom (X.ringCatSheaf.val.map r))).obj
    (ModuleCat.of ↑(X.ringCatSheaf.val.obj V) ↥(module h' D (unop V)))) :=
  ⟨f, mapPropertyNonempty h' D r f⟩

lemma mapFun_add (D : AlgebraicCycle X) {U V : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (r : U ⟶ V) [hU : Nonempty U.unop] [hV : Nonempty V.unop] (f g : ↥(module h' D (unop U))) :
    mapFunNonempty h' D r (f + g) = mapFunNonempty h' D r f + mapFunNonempty h' D r g := rfl

lemma mapFun_smul (D : AlgebraicCycle X) {U V : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (r : U ⟶ V) [hU : Nonempty U.unop] [hV : Nonempty V.unop] (a : ↑(X.sheaf.val.obj U))
    (f : (module h' D (unop U))) : mapFunNonempty h' D r (a • f) =
    a • mapFunNonempty h' D r f := by
  /-
  I believe this to be a problem of typeclass synthesis.
  -/

  rw[ModuleCat.restrictScalars.smul_def]
  simp [mapFunNonempty]
  apply Subtype.ext
  simp
  --rw?
  --rw [@Algebra.smul_def, @Algebra.smul_def]
  --congr 1
  #check (instAlgebraCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensFunctionFieldOfNonemptyToScheme X (unop V))
  let m : Algebra Γ(X, unop U) Γ(X, unop V) := (X.sheaf.val.map r).hom.toAlgebra
  let j : IsScalarTower Γ(X, unop U) Γ(X, unop V) X.functionField := by sorry
  rw [← @Algebra.compHom_smul_def]
  have := j.smul_assoc a 1 f
  rw[smul_one_smul] at this
  rw [one_smul] at this
  convert this
  simp [instAlgebraCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensFunctionFieldOfNonemptyToScheme]
  rw [@IsScalarTower.Algebra.ext_iff]
  intro b c
  simp
  /-
  This is hell
  -/
  sorry

open Classical in
noncomputable
def mapNonempty (D : AlgebraicCycle X) {U V : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (r : U ⟶ V) [hU : Nonempty U.unop] [hV : Nonempty V.unop] : obj h' D U ⟶
    (ModuleCat.restrictScalars (RingCat.Hom.hom (X.ringCatSheaf.val.map r))).obj
    (obj h' D V) := by
  simp only [obj, hU, hV]
  apply ModuleCat.ofHom (Y := (ModuleCat.restrictScalars
                (RingCat.Hom.hom (X.ringCatSheaf.val.map r))).obj
                (ModuleCat.of ↑(X.ringCatSheaf.val.obj V) ↥(module h' D (unop V))))
  exact {
    toFun := mapFunNonempty h' D r
    map_add' := mapFun_add h' D r
    map_smul' := mapFun_smul h' D r
  }

def mapNonempty_id (D : AlgebraicCycle X) (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) [Nonempty U.unop] :
  mapNonempty h' D (𝟙 U) =
  (ModuleCat.restrictScalarsId'App (CommRingCat.Hom.hom (X.sheaf.val.map (𝟙 U)))
  (congrArg RingCat.Hom.hom (X.ringCatSheaf.val.map_id U)) (obj h' D U)).inv := sorry

open Classical in
noncomputable
def mapEmptyLeft (D : AlgebraicCycle X) {U V : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (r : U ⟶ V) (hU : ¬ Nonempty U.unop) [hV : Nonempty V.unop] : obj h' D U ⟶
    (ModuleCat.restrictScalars (RingCat.Hom.hom (X.ringCatSheaf.val.map r))).obj
    (obj h' D V) := by
  have : (unop U).1 = ∅ := by exact Set.not_nonempty_iff_eq_empty'.mp hU
  have := CategoryTheory.leOfHom r.unop
  simp_all only [Scheme.Opens.nonempty_iff, TopologicalSpace.Opens.carrier_eq_coe,
    TopologicalSpace.Opens.coe_eq_empty, le_bot_iff, sheafCompose_obj_val, Functor.comp_obj,
    CommRingCat.forgetToRingCat_obj, Functor.comp_map, CommRingCat.forgetToRingCat_map_hom,
    TopologicalSpace.Opens.coe_bot, Set.not_nonempty_empty, not_false_eq_true]


open Classical in
noncomputable
def mapEmptyRight (D : AlgebraicCycle X) {U V : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (r : U ⟶ V) [hU : Nonempty U.unop] (hV : ¬ Nonempty V.unop) : obj h' D U ⟶
    (ModuleCat.restrictScalars (RingCat.Hom.hom (X.ringCatSheaf.val.map r))).obj
    (obj h' D V) := by
  simp only [obj, hU, hV]
  apply ModuleCat.ofHom (Y := (ModuleCat.restrictScalars
                (RingCat.Hom.hom (X.ringCatSheaf.val.map r))).obj
                (ModuleCat.of ↑(X.ringCatSheaf.val.obj V) PUnit))
  exact 0

open Classical in
noncomputable
def mapEmpty (D : AlgebraicCycle X) {U V : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (r : U ⟶ V) (hU : ¬ Nonempty U.unop) (hV : ¬ Nonempty V.unop) : obj h' D U ⟶
    (ModuleCat.restrictScalars (RingCat.Hom.hom (X.ringCatSheaf.val.map r))).obj
    (obj h' D V) := by
  simp only [obj, hU, hV]
  exact 𝟙 (ModuleCat.of (↑(X.sheaf.val.obj U)) PUnit.{u + 1})

def mapEmpty_id (D : AlgebraicCycle X) (U : (TopologicalSpace.Opens ↥X)ᵒᵖ)
    (hU : ¬ Nonempty U.unop) : mapEmpty h' D (𝟙 U) hU hU =
    (ModuleCat.restrictScalarsId'App (CommRingCat.Hom.hom (X.sheaf.val.map (𝟙 U)))
    (congrArg RingCat.Hom.hom (X.ringCatSheaf.val.map_id U)) (obj h' D U)).inv := by
  apply ModuleCat.hom_ext
  rw [@LinearMap.ext_iff]
  intro x
  let k := obj_neg h' D U hU
  simp [mapEmpty]
  sorry

open Classical in
noncomputable
def map (D : AlgebraicCycle X) {U V : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (r : U ⟶ V) : obj h' D U ⟶
    (ModuleCat.restrictScalars (RingCat.Hom.hom (X.ringCatSheaf.val.map r))).obj
    (obj h' D V) :=
  if hU : Nonempty U.unop
  then if hV : Nonempty V.unop
       then mapNonempty h' D r
       else mapEmptyRight h' D r hV
  else if hV : Nonempty V.unop
       then mapEmptyLeft h' D r hU
       else mapEmpty h' D r hU hV

def map_id (D : AlgebraicCycle X) (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) :
    map h' D (𝟙 U) = (ModuleCat.restrictScalarsId' (RingCat.Hom.hom (X.ringCatSheaf.val.map (𝟙 U)))
    (congrArg RingCat.Hom.hom (X.ringCatSheaf.val.map_id U))).inv.app (obj h' D U) := by
  simp [map]
  split_ifs
  · exact mapNonempty_id h' D U
  · rename_i hU
    exact mapEmpty_id h' D U hU

def map_comp (D : AlgebraicCycle X)
  {X_1 Y Z : (TopologicalSpace.Opens ↥X)ᵒᵖ} (f : X_1 ⟶ Y) (g : Y ⟶ Z) :
  map h' D (f ≫ g) = map h' D f ≫
    (ModuleCat.restrictScalars (RingCat.Hom.hom (X.ringCatSheaf.val.map f))).map (map h' D g) ≫
    (ModuleCat.restrictScalarsComp' (RingCat.Hom.hom (X.ringCatSheaf.val.map f))
    (RingCat.Hom.hom (X.ringCatSheaf.val.map g))
    (RingCat.Hom.hom (X.ringCatSheaf.val.map (f ≫ g)))
    (congrArg RingCat.Hom.hom (X.ringCatSheaf.val.map_comp f g))).inv.app (obj h' D Z) := sorry

open Classical in
noncomputable
def presheaf (D : AlgebraicCycle X) : PresheafOfModules X.ringCatSheaf.val where
  obj := obj h' D
  map := map h' D
  map_id := map_id h' D
  map_comp := map_comp h' D

lemma presheaf.obj_eq (D : AlgebraicCycle X) (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) :
    (presheaf h' D).obj U = obj h' D U := rfl

lemma presheaf.obj_eq' (D : AlgebraicCycle X) (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) :
    (presheaf h' D).presheaf.obj U = (forget₂ _ _).obj (obj h' D U) := rfl

lemma presheaf.map_eq (D : AlgebraicCycle X) {U V : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (r : U ⟶ V) : (presheaf h' D).map r = map h' D r := rfl


lemma presheaf.map_eq' (D : AlgebraicCycle X) {U V : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (r : U ⟶ V) : (presheaf h' D).presheaf.map r =
    AddCommGrp.ofHom (AddMonoidHom.mk' (map h' D r) (by simp)) := rfl
/-
AddCommGrp.ofHom <| AddMonoidHom.mk' (M.map f) (by simp)
-/

--open Topology
open Presheaf
lemma isSheaf (D : AlgebraicCycle X) :
    TopCat.Presheaf.IsSheaf (presheaf h' D).presheaf := by
  rw[TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro I 𝒰 s hs

  simp [TopCat.Presheaf.IsGluing, presheaf.map_eq', map]
  wlog h : (∀ i : I, Nonempty (𝒰 i))
  · sorry
  simp_rw [presheaf.obj_eq', obj] at s
  simp at s
  /-
  So what should we take as our section? It
  -/
  --simp_all


  /-
  The idea is s encodes a section of 𝒪(D) on each 𝒰 i. This is to say, we have
  s i : X.functionField, and on 𝒰 i, (s i) + D ≥ 0, and on overlaps s i = s i'. Of course,
  this means that the underlying function of all the s is must be the same by sheafiness of the
  sheaf of rational functions on X. So we should probably just define the sheaf of rational
  functions, then we can do this all very nicely I think.
  -/




  --rw [TopCat.Presheaf.isSheaf_iff_isSheafPairwiseIntersections]
  --let test : TopCat.Presheaf Ab X := (presheaf h' D).presheaf
  --suffices TopCat.Presheaf.IsSheaf test by exact this

  --#check TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (presheaf h' D).presheaf
  --intro I 𝒰
  --let test : Presheaf := sorry
  --apply TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types _
  /-rw [TopCat.Presheaf.isSheaf_iff_isSheafPairwiseIntersections]

  refine
    (TopCat.Presheaf.isSheafOpensLeCover_iff_isSheafPairwiseIntersections
          (presheaf h' D).presheaf).mp
      ?_
  intro a b-/
  sorry

end Presheaf

namespace Sheaf

noncomputable
def sheaf (D : AlgebraicCycle X) : X.Modules where
  val := Presheaf.presheaf h' D
  isSheaf := Presheaf.isSheaf h' D

end Sheaf
end LineBundle
end AlgebraicCycle

--def ι (p q : X) (h : p ⤳ q) :
def ι {p : X} : X.residueField p →+* X.functionField := sorry

#check X.residueField

/-
The following is, I believe, a sensible (ish) definition of Oₚ(D) in a very concrete way.
We then need to construct some map from 𝒪ₓ(D) to 𝒪ₚ(D), and we need to do it somehow via restriction.

What's the idea? If our function has poles everywhere on p, that's no good. Or indeed if it
has double vanishing on p or something that's no good. So either there exists a neighbourhood
around p on which we can take a restriction, or there doesn't and we send things to 0.

So we just need to define that map, then we need to prove some exactness result and then
we win.

(I think surjectivity will be hardest to show here, I'm not sure if we need to reason by
stalks or something which sounds bad with our current definition). I guess we just use the
covering definition on the stacks project.

This might even be surjective on the nose (in the sense of presheaves). I'm not entirely sure.

O_X(U) → O_p(U) should I think always be surjective.
-/



/--
This is intended to be a concrete definition of 𝒪ₚ(D) for a point p ∈ X. The idea is that these
should precisely be those rational functions which (locally) split up as a product of sections of
𝒪ₓ(D) and sections of 𝒪ₚ.

The definition below may need some tweaking, since it seems like we can add in as many poles and
such as we like. So maybe the sections here should be given by sections of 𝒪ₓ(D) satisfying this
condition (since we really would like that when we take a product with our g, the resulting s is
something which also adds to D to give something positive.)

I think below should be a reasonable enough definition of the thing we want, so to batle test it
we need to produce the desired exact sequence, and also show that in the case where p is a closed
point and we're working over a field K, we recover that field K.

Supposing p is just a point. Then a section of 𝒪ₚ is just a rational function on X which is written
as a product (ι f)*g, for g a section of 𝒪ₓ(D). The claim is that the set of all such products is
simply the residue field itself.

For this, it suffieces to show we have a surjection from the residue field to this set.
But I don't know how this could possibly be if there were multiple sections of the line bundle,
bevause surely if we had n sections, we would get n possible outputs.

I'm not sure this is the correct approach. We should maybe be defining this instead in terms
of the evaluation function, i.e.
s : X.residueField p | locally, s = evaluation f * something in residueField at p. This might work
a bit better, and indeed it might define the map for us essentially for free.
-/
def test (p : X) (D : AlgebraicCycle X) (U : X.Opens) : Set X.functionField :=
  {s : X.functionField | s ∈ AlgebraicCycle.LineBundle.carrier D U ∧
   ∀ z ∈ U, ∃ V : X.Opens, V.1 ⊆ U.1 ∧ z ∈ V.1 ∧
   ∃ f : X.residueField p, ∃ g : AlgebraicCycle.LineBundle.carrier D V,
   (ι f) ∈ AlgebraicCycle.LineBundle.carrier 0 V ∧ s = (ι f)*g.1}
/-
This is a slightly clunky way of writing this, but this I think makes the whole thing correct.
What should the associated map be? I guess we can try just sending s to s. But I think that won't
work. E.g. if we have 2x-2, this vanishes at x = 1, but we want to send this to x=1.

So we would take e.g. (2x-y-2)(x^2 - y) to (2x-2) (x^2 - y).
Just taking the evaluation though, which should take y to 0, would take x^2 - y just to x^2.
So we need a way of factorising these sections somehow.

So what we really want is a machine which takes s ↦ (f ∈ Γ(X, V)ˣ)*s' ↦ (ι (ev f)) * s'
What properties do we want of this factorization? I guess we could just define a function
which takes a factorization of the top and the bottom into irreducibles, computes the order
of vanishing at D for each guy and sorts the factors into two buckets.

I'm not sure if that's the most intelligent thing to do or if there's something more abstract.
Indeed, every section s of 𝒪ₓ(D) should satisfy this property I think, since 1 is a regular
function.

The sections associated to y = x and x = 0 should end up being the same. In this context, I don't
think they are the same. So I don't think this formulation is quite right.
We really want to say somehow that (ι f) is maximal or something

Say for example we have O(2). This allows poles of orders 0, 1 or 2 at 0. So, if we start with
s which vanishes along D to order 1, and we have
-/

/-
We should now define some function which takes in a section of 𝒪(D) on U and returns a section
of 𝒪ₚ(D). So, a section of 𝒪(D) would be a function f s.t. (f) + D ≥ 0.

I guess the thing is, we can always just take f to the element 1*f. This I imagine should give
what we want.

I'm still a little unconvinced of this construction.
Let's try it in the case where p is the x axis of the affine plane X = A^2. And maybe we'll take
our divisor to be the parabola y-x^2.

So we should have that sections of O_X(-D) are functions vanishing on the parabola. And sections
of O_p(-D) are then given by products of functions vansihing at D with vertical lines.

So we get, for instance, that the function x+1 vanishing at -1 is a section? Well, no, I guess
the sections restricted to Y are interpretted to be somehow the restriction of the divisor D to Y
when that's defined.

I guess the main concern is that the elements of the residue field are notably a field, and so
it seems like this is just sections of 𝒪ₓ(D) which isn't right.

I think this requirement that the whole thing be a section of 𝒪ₓ(D) is wrong, but I'm not sure how.
Sections of 𝒪ₚ(D) in this case should be elements of the residue field such that when we multiply
them by a section, we remain inside 𝒪ₓ(D). But then I think it really should be pairs, because we
may mutiply the same function with different sections.

E.g. if we take insted 𝒪ₚ(D), we should have that the section with a pole along the parabola gives
a different product than the constant section
-/

/-
This is another definition, but I'm a bit worried that it doesn't take locality into account.
I.e. I think this works if the cohomology of the ideal sheaf of the ideal sheaf is trivial.
But if not, then we have sections which are not in the image of a restriction. Ok, that's still not
game over, but it feels like we're going to get into trouble.

I'm worried that what we really want is something like a cover of U on which we have pairs (f, g)
like this, then two are equal if there is some common refinement of both.

Let's try and think of an example where this breaks. So, certainly our example from before should
now work.

I think this is not going to work, because we need equalities on these pairs, i.e. we need that
(f, g) = (1, fg) if f is an element of the residue field and so on. Of course, all of this is
taken care of by a good tensor product construction.

Namely, for any hope of the natural map taking f ↦ (1, f) to be surjective, we need some equalities
here. So I have no idea if this can even be recovered.

The only thing I can think now is that maybe sheafification is not required in this case, then we
can just use the presheaf. Let's try an example I suppose,

Let's try p = P^1 inside P^2, and take our divisor D to be










Right, I think we want to define somehow a factorization of sections `s` of `𝒪ₓ(D)` into `f × k`,
where `f` is a section of `𝒪ₓ` and `k` is a section of `𝒪ₓ(D)`. We want this to be maximal in the
sense that f is as large as it possibly could be.

The definition I have in mind is this. We should define a function `σ` which takes a rational
function and produces the largest open set `U` on which it is defined as a section `Γ(X, U)`.
We wish to find a factorization of `s` such that `σ f` is mininmised.

I'm not quite sure how we should show that such a thing exists, maybe using Zorn's lemma or
something.

Ok, then we define our `𝒪ₚ(D)` to be those sections of `𝒪ₓ(D)` such that `f` as defined above is
in the image of `ι`, and maybe we need this to only hold locally. This I think works as a
definition, but it's a little involved I must admit.

Steps:-

1. Define the maximal open set on which a rational function is defined.
2. Show that any section `s ∈ Γ(𝒪ₓ(D), U)` uniquely factorizes as a section `f ∈ Γ(X, U)`
   and a section `g ∈ Γ(𝒪ₓ(D), U)` such that the set `V` with `U ⊆ V` on which `f` is defined
   is minimised.

   How should this construction work? I think it should be some sort of Noetherian induction, but
   it's not entirely clear to me what the best thing to do here should be.

   Is this sensible? I'm not entirely sure. Let's do a quick example.
   Take a section of our favourite line bundle, 𝒪ₓ(D) for D a parabola in X = P^2. Then, a section
   for this might be something like c⧸(y-x^2) or some constant. Then our factorization would be
   c and 1/y-x^2 I suppose. But of course, our heuristic here cannot distinguish between constants
   if we're working over a field k (and maybe otherwise). Can we also take x/(y - x^2) here? I
   think so, if we take xz/(yz - x^2) then we get z/(yz) = 1/y ↦ (1/x) / (y/x) in the yz plane, and
    xz/(z-x^2) in the xz plane.

    (x, y, z) ↦ (x/z, y/z, 1) ↦ (x/y, 1, z/y) ↦ (1, y/x, z/x).
    (x, y) ↦ (x/y, 1/y) ↦ (y/x, 1/x)


    Right, so x can only be defined in P2 - ∞, so that would seem to be our answer here.
   Ok, let's try 𝒪(D²). Then we can take x/(y - x^2)

-/



#check zorn_le
def test' (p : X) (D : AlgebraicCycle X) (U : X.Opens) :=
  {(f, g) : (X.residueField p) × (AlgebraicCycle.LineBundle.carrier D U) |
    (ι f) * g.1 ∈ AlgebraicCycle.LineBundle.carrier D U}

--def thigno (p : X) (D : AlgebraicCycle X) (U : X.Opens) :=
  --{f : X.residueField p | (ι f) ≥ 0}

/-def test (p : X) (D : AlgebraicCycle X) (U : X.Opens) : Set (X.residueField p) :=
    {s : (X.residueField p) | (h : s ≠ 0) →
    ∀ z : X, ∃ V : X.Opens, V.1 ⊆ U.1 ∧ z ∈ V ∧ ∃ s' : AlgebraicCycle.LineBundle.carrier D V,
    (div (ι s * s'.1) (by sorry)).restrict (by simp : V.1 ⊆ ⊤) +
    D.restrict (by simp : V.1 ⊆ ⊤) ≥ 0}-/

--def test' (p : X) (D : AlgebraicCycle X) (U : X.Opens) : Set (X.residueField p) :=
--  {s : X.residueField p | }


#check IsLocalRing.ResidueField.map
variable (p : X)

--theorem testing : genericPoint X ⤳ p := genericPoint_specializes p

instance definitelyTrue : IsLocalHom (X.presheaf.stalkSpecializes (genericPoint_specializes p)).hom := sorry
#check IsLocalRing.ResidueField.map <| (X.presheaf.stalkSpecializes (genericPoint_specializes p)).hom

/-
This gives our definition of ι
-/


#check X.residue
#check X.descResidueField
#check AlgebraicGeometry.Scheme.evaluation

/-
This above should give a definition of out restriction map. Namely, our section of O_X is assumed
to have non-negative vanishing everywhere outside of D and hence has no poles at p (assuming D is
not supported at p). So then we have that around p, our section is some regular function.

This might take some defining but it's certainly doable. Then we just need to show that when we
interpret the guy back as some element of X.functionField, we get something which has positive
vanishing at D. For that, we probably need some statement about order of vanishing

Hang on, does this notion work?

If we take functions on the x axis that are meant to vanish to order 2, this should be the same
as O_{(y)} (y-x^2). But sections of this thing will be x^2,  which when lifted does not vanish
along y-x^2.
-/




/-
We should have that the restriction of a regular function to p is 0 if it vanishes everywhere
along p and otherwise just some restriction map.

So indeed if it doesn't vanish everywhere we can find some nhd U around p with our function
in Γ(X, U)ˣ. This
-/


/-
If we wish to define the exact sequence 0 -> O_X(-p) -> O_X -> O_p -> 0

Where we define O_X(-p) to be things with no poles at p and O_X as things with positive
order of vanishing everywhere (i.e. no poles anywhere).

We also want 0 -> O_X(D-p) -> O_X(D) -> O_p(D) -> 0

For this, we need some way of taking a tensor product with a line bundle.
For this, we can define O_p(D) at {f : residue field at p | (ι (f)) ≥ 0} where ι is the
map from the residue field at p to the function field. This should have ok results assuming
that X is smooth I think, otherwise we might get some trouble.


It may be that it's easier than expected to define the tensor product for the category of sheaves
of modules. With that approach, we still need to show the following:

- 𝒪ₓ(D) ⊗ 𝒪ₓ(D') ≅ 𝒪ₓ(D + D')
- Tensoring with a line bundle is exact (which would need to go via stalkwise reasoning)

-/



  sorry
