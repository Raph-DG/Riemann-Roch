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
    simp_all [carrier]
    intro nez z
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

def module
    (D : AlgebraicCycle X) (U : X.Opens) [Nonempty U] :
    Submodule Γ(X, U) X.functionField where
  carrier := carrier D U
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




            We know that for any z, ord f z = ord g z implies f and g differ by a unit in R
            in the local ring at R. We now need to lift that to something global.

            I'm wondering if we even need it in all local rings. E.g. if we have in the stalk
            at z that f = u • g, can this just be lifted globally?


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
  simp_all


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

lemma isSheaf (D : AlgebraicCycle X) :
    TopCat.Presheaf.IsSheaf (presheaf h' D).presheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafPairwiseIntersections]

  refine
    (TopCat.Presheaf.isSheafOpensLeCover_iff_isSheafPairwiseIntersections
          (presheaf h' D).presheaf).mp
      ?_
  intro a b
  sorry

end Presheaf

namespace Sheaf

noncomputable
def AlgebraicCycle.lineBundleSheaf (D : AlgebraicCycle X) : X.Modules where
  val := Presheaf.presheaf h' D
  isSheaf := Presheaf.isSheaf h' D




end Sheaf
end LineBundle
end AlgebraicCycle
