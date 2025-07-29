import Mathlib
import RiemannRoch.CodimLemma
import RiemannRoch.AlgebraicCycle.Basic
import RiemannRoch.AlgebraicCycle.Principal
import RiemannRoch.DVR

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
/--
Below we define the sheaf 𝒪(D) associated with a Weil divisor. We note that strictly speaking you
don't need the input cycle to be a divisor, so in this definition we just assume D is an arbitrary
cycle.
-/
def AlgebraicCycle.lineBundle (D : AlgebraicCycle X) (U : X.Opens) :=
  {s : (X.functionField) | (h : s ≠ 0) → (div s h).restrict (by aesop : U.1 ⊆ ⊤) + D.restrict (by aesop : U.1 ⊆ ⊤) ≥ 0}

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
    This part should not be too bad, we just need to develop a bit of API about the restrict
    function and the answer should essentially just fall out.
    -/
    intro h ha
    suffices ∀ z ∈ U, (0 : AlgebraicCycle X) z ≤ (div a ha + (D + D').restrict U) z by sorry
    intro z hz
    obtain ⟨V, VU, zV, f, hf, g, hg, hfg⟩ := h z hz
    --apply Function.locallyFinsuppWithin.ext
    sorry

  · /-
    This part is a bit more tricky. Given a section `s` of `𝓞(D + D')`, we need to show that for any
    `z : X`, there is a neighbourhood around which `s = f*g`, where `f` and `g` are sections of
    `𝒪(D)` and `𝒪(D')` respectively.

    In order to do this, we probably need that all local rings are UFDs.
    This implies that there is some neighbourhood `U` around `z` where `s` is of the form `(h)|ᵤ`
    for some rational function `h`. We also know in this context that all prime divisors of `U`
    are just given by the prime ideals of `U`, and that these are all principal.
    So we can factorise our rational function `h` using  the generators of these ideals.
    -/
    intro h z hz



    sorry

/-
The question, of course, it what's the utility of having this? Indeed, this is
only useful for RR if we can say somehow that this tensor product operation is exact. The
main problem being that it's unclear precisely what "exact" means in this context.

For that, I think we really will need the module structure, so we can't avoid the work =
below so easily.
-/


/-
This is necessary for defining the map in this direction. To weaken this we need to just define
𝒪(D) as the inverse of the map assigning a rational section its divisor.
-/
variable (h' : ∀ x : X, coheight x = 1 → IsDiscreteValuationRing (X.presheaf.stalk x))
variable (V : X.Opens)
#check AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen
#check Module (X.presheaf.obj (op V)) X.functionField
#check Eq.symm

--instance test (U : X.Opens) [Nonempty U] (z : X) (h : z ∈ U) : Algebra ↑Γ(X, U) ↑(X.presheaf.stalk z) := by sorry
  --#check X.germToFunctionField U

/-
instance stower (U : X.Opens) [Nonempty U] (z : X) (h : z ∈ U) :
  have := test U z h
  IsScalarTower ↑Γ(X, U) ↑(X.presheaf.stalk z) ↑X.functionField := sorry-/

--{s : (X.functionField) | (h : s ≠ 0) → (div s h) + restrict D U ≥ 0}


lemma _root_.locallyFinsuppWithin.restrict_eq_within {Y : Type*} [TopologicalSpace Y] {U : Set Y}
  {Z : Type*} [Zero Z] {V : Set Y} (D : locallyFinsuppWithin U Z) (h : V ⊆ U) (z : Y) (hz : z ∈ V) :
  D.restrict h z = D z := dif_pos hz

lemma _root_.locallyFinsuppWithin.restrict_eq_zero {Y : Type*} [TopologicalSpace Y] {U : Set Y}
  {Z : Type*} [Zero Z] {V : Set Y} (D : locallyFinsuppWithin U Z) (h : V ⊆ U) (z : Y) (hz : z ∉ V) :
  D.restrict h z = 0 := dif_neg hz

/-
/-, div_eq_ord_of_coheight_eq_one _ _ _ hZ, inf_le_iff,
      Multiplicative.toAdd_le, WithZero.unzero_le_unzero, Scheme.ord]-/
        have : IsDiscreteValuationRing ↑(X.presheaf.stalk Z) := h' Z hZ
        have := ordFrac_add (R := X.presheaf.stalk Z) a b
        exact inf_le_iff.mp this
-/

noncomputable
def AlgebraicCycle.lineBundleAddSubgroup
    (D : AlgebraicCycle X) (U : X.Opens) [Nonempty U] :
    Submodule Γ(X, U) X.functionField where
    --AddSubgroup (X.functionField) where
  carrier := {s : (X.functionField) | (h : s ≠ 0) → (div s h).restrict (by aesop : U.1 ⊆ ⊤) + D.restrict (by aesop : U.1 ⊆ ⊤) ≥ 0}
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
    suffices min ((div a ha0).restrict hU Z) ((div b hb0).restrict hU Z) ≤ (div (a + b) h).restrict hU Z by omega

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
      · simp[locallyFinsuppWithin.restrict_eq_within _ _ _ o]
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
    --have af : a • f ≠ 0 := by aesop
    suffices (div f h).restrict hU z ≤ (div (a • f) nez).restrict hU z by
      trans (div f h).restrict hU z + D.restrict hU z
      · exact hf
      · exact
        (Int.add_le_add_iff_right
              ((locallyFinsuppWithin.restrict D (of_eq_true (Set.subset_univ._simp_1 ↑U))) z)).mpr
          this
      /-
      trans ((div f h) z + (D.restrict U) z)
      · exact hf
      · exact (Int.add_le_add_iff_right ((D.restrict U) z)).mpr this-/
    by_cases hb : coheight z = 1
    · simp [locallyFinsuppWithin.restrict, div_eq_ord_of_coheight_eq_one _ _ _ hb]
      simp[Scheme.ord]
      /-
      ordFrac_le_smul is not enough for what we want, since we want this for smul with any ring
      for which we can define it, not just for R. Namely, Γ(X, U) is not our R, and indeed is not
      dimension 1 (or even neccessarily Noetherian!)
      -/
      --have : IsNoetherianRing ↑Γ(X, U) := by sorry
      --#check ordFrac_le_smul a
      have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk z) := krullDimLE_of_coheight hb
      have : a • f = (algebraMap Γ(X, U) X.functionField) a * f := rfl
      rw[this]
      simp
      by_cases k : (Ring.ordFrac ↑(X.presheaf.stalk z)) f = (0 : (WithZero (Multiplicative ℤ)))
      · simp[k]

      suffices (Ring.ordFrac ↑(X.presheaf.stalk z)) ((algebraMap ↑Γ(X, U) ↑X.functionField) a) ≥ 1 by sorry

      by_cases o : z ∈ U


      #check X.presheaf.germ U z
      · --apply Eq.symm
        have := X.presheaf.stalkSpecializes (sorry : genericPoint X ⤳ z) --TopCat.Presheaf.germ_stalkSpecializes o (sorry : genericPoint X ⤳ z)
        --apply ordFrac_le_smul

        sorry

      · /-
        Here we can just say that
        -/
        sorry
    · simp [div_eq_zero_of_coheight_ne_one _ _ _ hb]


  /-neg_mem' := by
    intro a neg ha' b
    simp_all
    specialize neg (by aesop (add simp ha')) b
    simp at neg
    suffices div a (by aesop (add simp ha')) b = div (-a) ha' b by rwa [← this]
    by_cases hb : coheight b = 1
    · simp [div_eq_ord_of_coheight_eq_one _ _ _ hb]
      congr 1
      simp[Scheme.ord]
      have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk b) := krullDimLE_of_coheight hb
      apply ordFrac_neg
    · simp [div_eq_zero_of_coheight_ne_one _ _ _ hb]-/




    /-
    TODO: add that Ring.ord R x = Ring.ord R (-x) to the ord API
    -/



--instance Module (X.presheaf.val) ()
/-
We also want that this is an 𝒪(U) module
-/
/-
instance (D : AlgebraicCycle X) (U : X.Opens) :
         Module (X.sheaf.val.obj (op U)) (D.lineBundleAddSubgroup U) := sorry-/
--SheafOfModules ((sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf)
noncomputable
def AlgebraicCycle.lineBundleSheaf (D : AlgebraicCycle X) : X.Modules
   where
    val := {
      obj U := by
        by_cases o : Nonempty ↑↑(unop U)
        · exact ModuleCat.of (↑(X.ringCatSheaf.val.obj U)) <| AlgebraicCycle.lineBundleAddSubgroup h' D (unop U)
        · exact ModuleCat.of (↑(X.ringCatSheaf.val.obj U)) PUnit
      map := by
        intro U V r

        sorry
      map_id := sorry
      map_comp := sorry
    }
    isSheaf := sorry

macro:max "𝒪(" D:term ")": term =>
  `(AlgebraicCycle.lineBundleSheaf $D)

noncomputable
def WeilDivisor (X : Scheme.{u}) := HomogeneousAddSubgroup X (X.dimension - 1)


variable [Catenary X]
