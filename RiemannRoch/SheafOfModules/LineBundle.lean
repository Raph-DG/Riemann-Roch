import Mathlib
import RiemannRoch.SheafOfModules.Nonempty
import RiemannRoch.SheafOfModules.Subsheaf
import RiemannRoch.SheafOfModules.Testing
import RiemannRoch.AlgebraicCycle.Basic
import RiemannRoch.AlgebraicCycle.Principal
import RiemannRoch.AlgebraicCycle.Factor
/-!
# The invertible sheaf associated with a Weil Divisor

In this file, we define the invertible sheaf associated with a Weil divisor `D` on an integral
scheme where all local rings of codimension `1` points are discrete valuation rings. We also
construct a morphism `𝒪ₓ(D) ⟶ 𝒪ₓ(D + D')` for effective `D'` and show it is a monomorphism
in this case.

We also construct the exact sequence `0 ⟶ 𝒪ₓ(D - P) ⟶ 𝒪ₓ(D) ⟶ k(P) ⟶ 0` where `P` is a closed
point and `k(P)` is the skyscraper sheaf at `P` whose stalk at `P` is the residue field at `P`.
This is useful for inductive arguments about divisors on curves, since such divisors are composed
entirely of closed points.

This is not the most general case this theory can be developed in. With some care, this general
approach can be pushed work for schemes which are not necessarily irreducible, and the
analogous construction for Cartier divisors gives more general results as well. We chose to
develop things at this level of generality because in this case, sections of `𝒪ₓ(D)` are very
literally just elements of the function field of `X`, which is useful if one wants to do more
elaborate concrete constructions involving these sheaves. Of course, we will also at some point
develop more general things, most likely starting by developing a library about Cartier divisors.
-/

universe u v w

#check PresheafOfModules
open AlgebraicGeometry CategoryTheory Order Function locallyFinsuppWithin

open Function locallyFinsuppWithin

open Classical in
/--
TODO: Move from this file and PR into mathlib
-/
lemma _root_.Function.locallyFinsuppWithin_le_iff {X Y : Type*} [TopologicalSpace X] {U : Set X}
    [Zero Y] [Lattice Y] (D D' : locallyFinsuppWithin U Y) : D ≤ D' ↔ ∀ z ∈ U, D z ≤ D' z :=
  ⟨fun h z _ ↦ h z, fun h z ↦ if hz : z ∈ U then h z hz else by simp [hz]⟩

/--
A LinearLocalPredicsteNE is a linear local predicate which is only specified on nonempty subsets.
This is useful for defining subsheaves of sheaves of modules.
-/
structure LinearLocalPredicateNE {X : Scheme.{u}} (F : X.Modules) where
    P {U : X.Opens} [Nonempty ↥U] (f : Γₘ(F, U)) : Prop
    zero {U : X.Opens} [Nonempty ↥U] : P (0 : Γₘ(F, U))
    add {U : X.Opens} [Nonempty ↥U] {f g : Γₘ(F, U)} (hf : P f) (hg : P g) : P (f + g)
    smul {U : X.Opens} [Nonempty ↥U] (a : Γ(X, U)) {f : Γₘ(F, U)} (hf : P f) : P (a • f)
    res {U V : X.Opens} [Nonempty ↥U] [Nonempty ↥V] (k : V ≤ U) (f : Γₘ(F, U)) (hf : P f) :
      P (F.val.presheaf.map (homOfLE k).op f)
    local_prop {U : X.Opens} [Nonempty ↥U] (f : Γₘ(F, U)) :
      (∀ x ∈ U, ∃ (V : X.Opens) (_ : Nonempty ↥V) (k : V ≤ U) (_ : x ∈ V), P <|
      F.val.presheaf.map (homOfLE k).op f) → P f

namespace LinearLocalPredicateNE

open Classical in
/-
Given a linear local predicate which is only defined for nonempty sets, produce a linear local
predicate by simply extending the predicate to be true on the empty set.
-/
def toLinearLocalPredicate {X : Scheme.{u}} {F : X.Modules}
    (Pn : LinearLocalPredicateNE F) :
    LinearLocalPredicate F where
      P {U} f := if hU : Nonempty ↥U then @Pn.P U hU f else True
      zero {U} := by
        split_ifs
        rename_i h
        exact @Pn.zero U h
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
          convert this using 1
          constructor
          · intro h x hx
            obtain ⟨V, hVU, hVx, hV⟩ := h x hx
            use V
            have : Nonempty ↥V := by use x
            use this, hVU, hVx
            simp [this] at hV
            exact hV
          · intro h x hx
            obtain ⟨V, neV, k, xV, hV⟩ := h x hx
            use V, k, xV
            simp [neV]
            exact hV
        · simp

end LinearLocalPredicateNE

namespace locallyFinsuppWithin

open Function locallyFinsuppWithin
lemma restrict_eq_within {Y : Type*} [TopologicalSpace Y] {U : Set Y}
    {Z : Type*} [Zero Z] {V : Set Y} (D : locallyFinsuppWithin U Z)
    (h : V ⊆ U) (z : Y) (hz : z ∈ V) :
  D.restrict h z = D z := dif_pos hz

lemma restrict_eq_zero {Y : Type*} [TopologicalSpace Y] {U : Set Y}
    {Z : Type*} [Zero Z] {V : Set Y} (D : locallyFinsuppWithin U Z)
    (h : V ⊆ U) (z : Y) (hz : z ∉ V) :
  D.restrict h z = 0 := dif_neg hz

end locallyFinsuppWithin


namespace AlgebraicCycle

variable {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X]
    (h' : ∀ x : X, coheight x = 1 → IsDiscreteValuationRing (X.presheaf.stalk x))
    (D : AlgebraicCycle X)


namespace lineBundle
/--
Given an algebraic cycle `D`, we define the set of sections `Γ(𝒪ₓ(D), U)` for a nonempty set `U`.
Note the nonemptiness is important here
-/
def P {U : X.Opens} [hU : Nonempty ↥U]
  (s : ↑((sheafOfRationalFunctions X).val.obj (Opposite.op U))) : Prop :=
  letI s' := sectionNEToFunctionField U s
  (h : s' ≠ 0) → (div s' h).restrict (by simp : U.1 ⊆ ⊤) + D.restrict (by simp : U.1 ⊆ ⊤) ≥ 0

/--
`0` is a section of `𝒪ₓ(D)`on any nonempty open set `U`.
-/
def zero {U : X.Opens} [x : Nonempty ↥U] :
    P (U := U) D 0 :=
  fun hx ↦ False.elim <| hx <| sectionNEToFunctionField_zero U

/--
If `f` and `g` are rational functions such that `f g ∈ Γ(𝒪ₓ(D), U)`, then `f + g ∈ Γ(𝒪ₓ(D), U)`.
-/
def add {U : X.Opens} [hU : Nonempty ↥U]
    {f g : ↑((sheafOfRationalFunctions X).val.obj (Opposite.op U))}
    (hf : P D f) (hg : P D g) : P D (f + g) := by
  intro h
  have := sectionNEToFunctionField_add U f g
  simp [this] at h ⊢
  set a := sectionNEToFunctionField U f
  set b := sectionNEToFunctionField U g
  by_cases ha0 : a = 0
  · simp_all [P]
  by_cases hb0 : b = 0
  · simp_all [P]
  intro Z
  specialize hf ha0 Z
  specialize hg hb0 Z
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

def smul {U : X.Opens} [hU : Nonempty ↥U] (a : ↑Γ(X, U))
    (f' : ↑((sheafOfRationalFunctions X).val.obj (Opposite.op U)))
    (hf : P D f') (nez : sectionNEToFunctionField U (a • f') ≠ 0) :
    restrict (div (sectionNEToFunctionField U (a • f')) nez) (by simp : U.1 ⊆ ⊤) +
    restrict D (by simp : U.1 ⊆ ⊤) ≥ 0 := by
        simp [sectionNEToFunctionField_smul U a f'] at nez ⊢
        intro z
        have : Nonempty U := hU
        have h : ¬ sectionNEToFunctionField U f' = 0 := by
          simp_all only [ne_eq]
          intro o
          simp_all only [not_true_eq_false, smul_zero]
        set f := sectionNEToFunctionField U f'
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

def res {U V : X.Opens} [hU : Nonempty ↥U] [hV : Nonempty ↥V]
    (k : V ≤ U) (f' : ↑((sheafOfRationalFunctions X).val.obj (Opposite.op U)))
    (hf' : P D f') : P D
    ((ConcreteCategory.hom ((sheafOfRationalFunctions X).val.presheaf.map (homOfLE k).op)) f') := by
  have := sectionNEToFunctionField_res U V k f'
  unfold P
  rw [this]
  intro h
  specialize hf' h
  intro z
  by_cases h : z ∈ V
  · have : z ∈ U := by exact k h
    simp [restrict_apply, h]
    specialize hf' z
    simp [restrict_apply, this] at hf'
    exact hf'
  · simp [h]


def local_prop
    {U : X.Opens} [Nonempty ↥U] (s : ↑((sheafOfRationalFunctions X).val.obj (Opposite.op U))) :
    (∀ x ∈ U, ∃ (V : X.Opens) (_ : Nonempty ↥V) (k : V ≤ U) (_ : x ∈ V),
    P D ((ConcreteCategory.hom
    ((sheafOfRationalFunctions X).val.presheaf.map (homOfLE k).op)) s)) → P D s := by
  intro loc hf z
  by_cases h : z ∈ U
  · simp
    obtain ⟨V, neV, k, zinV, hV⟩ := loc z h
    have := sectionNEToFunctionField_res U V k s
    specialize hV (this ▸ hf) z
    simp_all
    convert hV using 1
    congr 1
    · simp [restrict_apply, zinV, h]
      congr 2
      exact this.symm
    · simp [restrict_apply, zinV, h]
  · simp [h]


def linearLocalPredicateNE : LinearLocalPredicateNE (sheafOfRationalFunctions X) where
  P := P D
  zero := zero D
  add := add h' D
  smul := smul D
  res := res D
  local_prop := local_prop D

end lineBundle

/--
A definition of `𝒪ₓ(D)` for a cycle `D` on a locally Noetherian integral Scheme `X` which is regular
in codimension `1`.
-/
noncomputable
def lineBundle {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (h' : ∀ x : X, coheight x = 1 → IsDiscreteValuationRing (X.presheaf.stalk x))
    (D : AlgebraicCycle X) :=
    (lineBundle.linearLocalPredicateNE h' D).toLinearLocalPredicate.sheaf

/--
TODO: Move from this file

The restriction of a sum of cycles is the sum of the restrictions.
-/
lemma _root_.Function.locallyFinsuppWithin.restrict_add {X : Type*} [TopologicalSpace X] {U : Set X}
    {Y : Type*} [AddCommGroup Y] {V : Set X} (D D' : locallyFinsuppWithin U Y) (h : V ⊆ U) :
    ((D + D').restrict h) = D.restrict h + D'.restrict h := by
  ext z
  by_cases hz : z ∈ V
  all_goals simp [restrict_apply, hz]


namespace lineBundle
/--
TODO - I'm not convinced this is the most sensible way to write this lemma
(Find a way of writing this that can be interpretted by a human being)

If `f` is a section of `𝒪ₓ(D)`, then it is also a section of `𝒪ₓ(D + D')` for effective `D'`.
-/
lemma inclusionProp
    (D D' : AlgebraicCycle X) (h : D' ≥ 0) (U : (TopologicalSpace.Opens ↥X)ᵒᵖ)
    --(f : Γₘ(lineBundle h' D, Opposite.unop U)) :
    --f.1 ∈ LinearLocalPredicateNE.lineBundleProp h' (D + D') (Opposite.unop U)
    (f : ↑((sheafOfRationalFunctions X).val.obj (Opposite.op (Opposite.unop U))))
    (hf : f ∈ LinearLocalPredicate.submodule (sheafOfRationalFunctions X)
      (lineBundle.linearLocalPredicateNE h' D).toLinearLocalPredicate (Opposite.unop U)) :
    f ∈ LinearLocalPredicate.submodule (sheafOfRationalFunctions X)
    (lineBundle.linearLocalPredicateNE h' (D + D')).toLinearLocalPredicate
    (Opposite.unop U) := by
  simp [LinearLocalPredicate.submodule, lineBundle.linearLocalPredicateNE,
    LinearLocalPredicateNE.toLinearLocalPredicate] at hf ⊢
  intro x hx fnez
  specialize hf x hx fnez
  simp [restrict_add]
  apply le_trans hf
  simp
  intro z
  simp [restrict_apply]
  split_ifs
  · exact h z
  · rfl

/--
The inclusion mapping `𝒪ₓ(D) ⟶ 𝒪ₓ(D + D')`, defined by `h ↦ h`.
-/
noncomputable
def extend (D D' : AlgebraicCycle X) (h : D' ≥ 0) : lineBundle h' D ⟶ lineBundle h' (D + D') where
    val := {
      app U :=
        ModuleCat.ofHom
          {
            toFun := fun ⟨f, hf⟩ ↦ ⟨f, inclusionProp h' D D' h U f hf⟩
            map_add' := by aesop
            map_smul' := by aesop
          }
    }

/--
The inclusion morphism `𝒪ₓ(D) ⟶ 𝒪ₓ(D + D')` is a monomorphism
-/
lemma extend_mono --{X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    --(h' : ∀ x : X, coheight x = 1 → IsDiscreteValuationRing (X.presheaf.stalk x))
    (D D' : AlgebraicCycle X) (h : D' ≥ 0) :
    Mono <| extend h' D D' h := by
  suffices ∀ (U : (TopologicalSpace.Opens ↥X)ᵒᵖ), Function.Injective <|
    (extend h' D D' h).val.app U by
    suffices Mono <| (SheafOfModules.toSheaf X.ringCatSheaf).map <|
      extend h' D D' h by cat_disch
    exact
      Sheaf.mono_of_injective
        ((SheafOfModules.toSheaf X.ringCatSheaf).map (extend h' D D' h)) this
  intro U
  simp [extend]
  intro ⟨x, hx⟩ ⟨y, hy⟩ h
  change (AddHom.toFun _) (⟨x, hx⟩ : ↑((lineBundle h' D).val.obj U)) =
         (AddHom.toFun _) (⟨y, hy⟩ : ↑((lineBundle h' D).val.obj U)) at h
  grind

/--
The quotient `𝒪ₓ(D) ⧸ 𝒪ₓ(D + D')` for an effective divisor `D'`.

Currently this is not being used, as we are instead constructing an explicit model of this thing
for the purposes of Cech cohomology calculations.
-/
noncomputable
def lineBundleQuotient --{X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  --(h' : ∀ x : X, coheight x = 1 → IsDiscreteValuationRing (X.presheaf.stalk x))
  (D D' : AlgebraicCycle X) (h : D' ≥ 0) := Limits.cokernel <| extend h' D D' h


--section ClosedPoint
--variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  --(h' : ∀ x : X, coheight x = 1 → IsDiscreteValuationRing (X.presheaf.stalk x))
variable (p : X)

open Classical in
def _root_.AlgebraicCycle.single_apply {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (x : X)
    (c : ℤ) (z : X) :
    single x c z = if z = x then c else 0 := by
  unfold single
  change Set.indicator {x} (Function.const X c) z = _
  simp [Set.indicator_apply]

/--
A cycle supported at a single point with a positive coefficient is effective.
-/
lemma _root_.AlgebraicCycle.single_effective (x : X) (c : ℤ) (hc : c ≥ 0) : single x c ≥ 0 := by
  intro z
  simp [single_apply x c z]
  by_cases o : x = z
  all_goals grind

/--
On open sets away from `P`, `lineBundleMapping` is surjective (and hence bijective, and hence
an isomorphism of modules)
-/
lemma extend_surjective (U : X.Opensᵒᵖ) (hU : p ∉ U.1):
    Function.Surjective <| ((extend h' (D - single p 1) (single p 1) (single_effective p 1 (by simp))).val.app U).hom := by
  simp [extend]
  intro ⟨s, hs⟩
  suffices s ∈ LinearLocalPredicate.submodule (sheafOfRationalFunctions X)
    (lineBundle.linearLocalPredicateNE h' (D - single p 1)).toLinearLocalPredicate (Opposite.unop U) by
    use ⟨s, this⟩
    change (⟨s, _⟩ : (lineBundle h' (D - single p 1 + single p 1)).val.obj U) = ⟨s, hs⟩
    grind
  simp [LinearLocalPredicate.submodule, lineBundle.linearLocalPredicateNE,
    LinearLocalPredicateNE.toLinearLocalPredicate, lineBundle.P] at hs ⊢
  intro x hx h
  specialize hs x hx h
  intro z
  by_cases o : z ∈ U.1
  · specialize hs z
    simp [restrict_apply, single_apply p 1 z, o] at hs ⊢
    have : ¬ z = p := by grind
    simpa [this] using hs
  · simp [o]


open Opposite
/--
Given an open set `U` and a point `p ∈ U` where the stalk at `p` is a discrete valuation ring has
uniformizer `ϖ`, a section of `𝒪ₓ(D)` on `U` can be written as `u · ϖⁿ` where `u` is a unit of the
stalk at `p` and `n ≥ - D p`.
-/
lemma eq_unit_mul_zpow_irreducible (U : X.Opens) (p : X)
    (hp : p ∈ U) (hp' : coheight p = 1)
    (s : (lineBundle h' D).val.obj (op U)) (hs : s ≠ 0) {ϖ : X.presheaf.stalk p}
    (hϖ : Irreducible ϖ) :
    haveI : Nonempty ↥U := by use p
    ∃ (n : ℤ) (_ : n ≥ - D p)(u : (X.presheaf.stalk p)ˣ), sectionNEToFunctionField U s.1 =
    (algebraMap (X.presheaf.stalk p) (X.functionField) u)*
    (algebraMap (X.presheaf.stalk p) (X.functionField) ϖ)^n := by
  have : Nonempty ↥U := by use p
  have := h' p hp'
  obtain ⟨s, hs'⟩ := s
  have : s ≠ 0 := by
    have : (0 : (lineBundle h' D).val.obj (op U)) = ⟨0, by simp⟩ := rfl
    rw [this] at hs
    aesop
  have : sectionNEToFunctionField U s ≠ 0 :=
    sectionNEToFunctionField_ne_zero U s this
  obtain ⟨n, u, hnu⟩ := IsDiscreteValuationRing.eq_unit_mul_zpow_irreducible this hϖ

  simp [LinearLocalPredicate.submodule, lineBundle.linearLocalPredicateNE,
    LinearLocalPredicateNE.toLinearLocalPredicate, lineBundle.P] at hs'
  specialize hs' p hp this p
  simp [restrict_apply, hp, div_eq_ord_of_coheight_eq_one _ _ p hp'] at hs'
  simp [Scheme.ord] at hs'
  use Multiplicative.toAdd (WithZero.unzero (Scheme.ord_ne_zero hp' this)), (by omega), u
  convert hnu
  suffices ((Scheme.ord p hp') (sectionNEToFunctionField U s)) = (WithZero.exp n) by simp_all

  simp [Scheme.ord]
  simp_rw [hnu, map_mul, map_zpow₀, ordFrac_irreducible ϖ hϖ]
  rw [ordFrac_of_isUnit u.1 (by simp)]
  simp


noncomputable
instance instModuleResidueField (U : X.Opens) (hP : p ∈ U) :
  Module ↑(X.ringCatSheaf.val.obj (op U)) ↑(X.residueField p) :=
  (X.evaluation U p hP).hom.toModule


open Classical in
/--
TODO: Generalize beyond the residue field
-/
noncomputable
def skyscraperAb : TopCat.Sheaf Ab X := skyscraperSheaf p (.of <| X.residueField p)

def skyscraperAbSection (U : X.Opens) (hU : p ∈ U) (f : X.residueField p) :
  (skyscraperAb p).presheaf.obj (op U) := by
  simp [skyscraperAb, skyscraperSheaf, skyscraperPresheaf, hU]
  exact f

@[simp]
def skyscraperAbSection_zero (U : X.Opens) (hU : p ∈ U)  :
  skyscraperAbSection p U hU 0 = 0 := by
  simp [skyscraperAbSection, skyscraperAb, skyscraperSheaf, skyscraperPresheaf, hU]
  --unfold_projs

  sorry
noncomputable
instance {R : Type u} [CommRing R] : Module R (⊤_ Ab.{u}) := by
  let k := (Limits.terminal.from (CommRingCat.of.{u} R))
  let m := k.hom.toModule

  --convert m


  sorry

  --have : Limits.IsTerminal (AddCommGrp.of PUnit.{u+1}) := by sorry
  --suffices Module R (AddCommGrp.of PUnit.{u+1}) by

  --  sorry
  --infer_instance


open Classical in
noncomputable
instance (U : (TopologicalSpace.Opens X)ᵒᵖ) : Module ↑(X.ringCatSheaf.val.obj U)
  ↑((skyscraperAb p).presheaf.obj U) := by
  simp [skyscraperAb, skyscraperSheaf, skyscraperPresheaf]
  by_cases o : p ∈ unop U
  · let k := instModuleResidueField p (unop U) o
    suffices Module ↑(X.sheaf.val.obj U) (AddCommGrp.of <| X.residueField p) from
      module_pos_of_ab (X.sheaf.val.obj U) ((AddCommGrp.of ↑(X.residueField p))) (⊤_ Ab) o
    exact instModuleResidueField p (unop U) o
  · exact module_neg_of_ab (X.sheaf.val.obj U) ((AddCommGrp.of ↑(X.residueField p))) (⊤_ Ab) o
    /-suffices Module.{u, u} ↑(X.sheaf.val.obj U) (AddCommGrp.of PUnit) by
      exact module_neg_of_ab (X.sheaf.val.obj U) ((AddCommGrp.of ↑(X.residueField P))) (⊤_ Ab) o

    infer_instance-/


noncomputable
def skyscraperPresheafOfModules : PresheafOfModules X.ringCatSheaf.val := by
  apply PresheafOfModules.ofPresheaf (skyscraperAb p).presheaf
  intro U V k s s'
  simp [skyscraperAb, skyscraperSheaf]
  /-
  This should follow fairly readily once the above instances are sorted out
  -/
  sorry

noncomputable
def skyscraperSheafOfModules : SheafOfModules X.ringCatSheaf where
  val := skyscraperPresheafOfModules p
  isSheaf := (skyscraperAb p).2


noncomputable
def secondMapFun (U : X.Opens)
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hP' : coheight p = 1) (o : p ∈ U)
    (s : (lineBundle h' D).val.obj (op U)) :
    ↑((skyscraperAb p).presheaf.obj (op U)) := by
  by_cases hs : s = 0
  · exact 0
  --simp only [skyscraperAb, skyscraperSheaf, skyscraperPresheaf, o, ↓reduceIte]
  apply skyscraperAbSection p U o
  have : IsDiscreteValuationRing ↑(X.presheaf.stalk p) := h' p hP'
  choose n hn u hnu using eq_unit_mul_zpow_irreducible
    h' D U p o hP' s hs hϖ
  exact X.residue p (u * ϖ ^ (n + D p).toNat)


/-
This is the lemma we're going to need in order to compute anything with the above definition.

The proof should be the following:

`res s = res (u * ϖⁿ)`

`secondMapFun s = res (uₛ · ϖ ^ {nₛ + D P})`

WTS: Given `s = u · ϖ ^ n`, that `secondMapFun s = res (u · ϖ ^ {n + D P})`.


`res (uₛ · ϖ ^ {nₛ + D P}) = res uₛ · res (ϖ ^{nₛ + D P})`
                          `= if nₛ + D P = 0 then res uₛ else 0`
                          ...

This should be doable without too much hassle, let's try and prove everything using it then prove it
-/
lemma secondMapFun_apply (U : X.Opens)
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hP' : coheight p = 1) (o : p ∈ U)
    (s : (lineBundle h' D).val.obj (op U))
    {u : (X.presheaf.stalk p)ˣ} {n : ℤ}
    (hs :
    haveI : Nonempty ↥U := by use p
    sectionNEToFunctionField U s.1 = (algebraMap (X.presheaf.stalk p) (X.functionField) u) *
    (algebraMap (X.presheaf.stalk p) (X.functionField) ϖ)^n) :
    secondMapFun h' D p U ϖ hϖ hP' o s =
    skyscraperAbSection p U o (X.residue p (u * ϖ ^ (n + D p).toNat)) := by
  simp [secondMapFun]
  split_ifs
  · rename_i h
    have : Nonempty ↥U := by use p
    have : sectionNEToFunctionField U s.1 = 0 := by simp [h]
    rw [this] at hs
    --rw [← hs]
    sorry
  · rename_i h

    sorry

/-
We wish to say that secondMapFun can be computed with respect to any such choice, i.e. if
a = u ϖ^n, then secondMapFun a = secondMapFun (u ϖ^n).

We also want that secondMapFun (u ϖ^n) = X.residue P (u ϖ^(n + D p))
-/
lemma secondMapFun_map_add_left_zero (U : X.Opens)
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hP' : coheight p = 1) (o : p ∈ U)
    (x y : (lineBundle h' D).val.obj (op U)) (hx : x = 0):
    secondMapFun h' D p U ϖ hϖ hP' o (x + y) =
    secondMapFun h' D p U ϖ hϖ hP' o x + secondMapFun h' D p U ϖ hϖ hP' o y := by
  simp [secondMapFun]
  subst hx
  simp_all only [zero_add, ↓reduceDIte]
  split
  next h => simp_all only [zero_add, ↓reduceDIte]
  next h =>
    simp_all
    intro h_1
    subst h_1
    grind

lemma secondMapFun_map_add_right_zero (U : X.Opens)
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hP' : coheight p = 1) (o : p ∈ U)
    (x y : (lineBundle h' D).val.obj (op U)) (hx : y = 0) :
    secondMapFun h' D p U ϖ hϖ hP' o (x + y) =
    secondMapFun h' D p U ϖ hϖ hP' o x + secondMapFun h' D p U ϖ hϖ hP' o y := by
  simp [secondMapFun]
  subst hx
  simp_all only [add_zero, ↓reduceDIte]
  split
  next h => simp_all only [add_zero, ↓reduceDIte]
  next h =>
    simp_all
    intro h_1
    subst h_1
    grind



lemma secondMapFun_map_add_sum_zero (U : X.Opens)
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hP' : coheight p = 1) (o : p ∈ U)
    (x y :
    ↑((LinearLocalPredicate.presheafAb (sheafOfRationalFunctions X)
    (lineBundle.linearLocalPredicateNE h' D).toLinearLocalPredicate).obj
    (op U))) (hx : x + y = 0) : secondMapFun h' D p U ϖ hϖ hP' o (x + y) =
    secondMapFun h' D p U ϖ hϖ hP' o x + secondMapFun h' D p U ϖ hϖ hP' o y := by
  simp [secondMapFun]

  --aesop
  sorry




lemma secondMapFun_map_add_ne_zero (U : X.Opens)
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hP' : coheight p = 1) (o : p ∈ U)
    (x y : (lineBundle h' D).val.obj (op U)) (hx : x ≠ 0) (hy : y ≠ 0) :
    secondMapFun h' D p U ϖ hϖ hP' o (x + y) =
    secondMapFun h' D p U ϖ hϖ hP' o x + secondMapFun h' D p U ϖ hϖ hP' o y := by
  have neU : Nonempty ↥U := by use p
  obtain ⟨n, hn, u, hnu⟩ := eq_unit_mul_zpow_irreducible
    h' D U p o hP' x hx hϖ
  obtain ⟨m, hm, v, hmv⟩ := eq_unit_mul_zpow_irreducible
    h' D U p o hP' y hy hϖ
  rw [secondMapFun_apply h' D p U ϖ hϖ hP' o x hnu, secondMapFun_apply h' D p U ϖ hϖ hP' o y hmv]
  wlog h : n ≤ m
  · have := this h' D p U ϖ hϖ hP' o y x hy hx neU m hm v hmv n hn u hnu -- y x ϖ hϖ hy0 hx0 n β hy m α hx
    grind
  obtain ⟨k, rfl⟩ := Int.exists_add_of_le h
  /-have xy : x + y = (algebraMap R K α + (algebraMap R K β) * (algebraMap R K ϖ)^k) *
      (algebraMap R K ϖ)^m := by
    rw [hx, hy, ← zpow_natCast, zpow_add₀]
    · ring
    · exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors <|
        mem_nonZeroDivisors_of_ne_zero <| Irreducible.ne_zero hϖ-/
  have : sectionNEToFunctionField U (x + y).1 =
    (algebraMap ↑(X.presheaf.stalk p) ↑X.functionField) (u + v*ϖ^k) *
    (algebraMap ↑(X.presheaf.stalk p) ↑X.functionField) ϖ ^ n := by
    change sectionNEToFunctionField U (x.1 + y.1) = _
    rw [sectionNEToFunctionField_add U x.1 y.1]
    rw [hnu, hmv, zpow_add₀]
    · simp
      ring
    · exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors <|
        mem_nonZeroDivisors_of_ne_zero <| Irreducible.ne_zero hϖ
  /-
  This is very doable, we now just need to show that u + v ϖ is indeed a unit, and then we win.
  The problem I suppose is that this feels like a bit of duplicated work somehow.

  The smul thing should have essentially the same proof I believe, but we have to split apart
  the thing we're acting with too.
  -/

  sorry

/-
The proof of this lemma should be similar to the previous one, again we may need some glue in the
DVR library to avoid repeated work.
-/
lemma secondMapFun_map_smul_ne_zero (U : X.Opens)
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hP' : coheight p = 1) (o : p ∈ U)
    (a : ↑(X.ringCatSheaf.val.obj (op U)))
    (x : (lineBundle h' D).val.obj (op U)) (hx : x ≠ 0) :
    secondMapFun h' D p U ϖ hϖ hP' o (a • x) =
    a • secondMapFun h' D p U ϖ hϖ hP' o x := by sorry

noncomputable
def secondMap' (U : X.Opens)
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hP' : coheight p = 1):
    (lineBundle h' D).val.obj (op U) ⟶ (skyscraperSheafOfModules p).val.obj (op U) := by
  apply ModuleCat.ofHom

  by_cases o : p ∈ U
  · exact {
      toFun s := secondMapFun h' D p U ϖ hϖ hP' o s
      map_add' := sorry
      map_smul' := sorry
    }
  · exact 0


open Classical in
/--
The morphism from 𝒪ₓ(D) taking `h = u ϖ^n ↦ res (u ϖ ^ {n + D P})`
-/
noncomputable
def quotientMap (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hP' : coheight p = 1) :
    lineBundle h' D ⟶ skyscraperSheafOfModules p where
      val := {
        app U := secondMap' h' D p (unop U) ϖ hϖ hP'
        naturality := by
          simp [secondMap']

          sorry
      }

/-
The second map in our sequence is a local surjection.

NOTE: coheight P = 1 is a bit of a stupid assumption, we really just need that the stalk of 𝒪ₓ at
P is a DVR.
-/
instance (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hP' : coheight p = 1)
    (hD : ∀ z : X, coheight z ≠ 1 → D z ≥ 0)
    (PClosed : ∀ x : X, x ≤ p → x = p) :
    CategoryTheory.Sheaf.IsLocallySurjective <|
    (SheafOfModules.toSheaf X.ringCatSheaf).map <| quotientMap h' D p ϖ hϖ hP' := by
  refine
    (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff
          ((SheafOfModules.toSheaf X.ringCatSheaf).map (quotientMap h' D p ϖ hϖ hP'))).mp
      ?_

  suffices TopCat.Presheaf.IsLocallySurjective <|
    ((sheafToPresheaf (Opens.grothendieckTopology ↥X) AddCommGrp).map
    ((SheafOfModules.toSheaf X.ringCatSheaf).map (quotientMap h' D p ϖ hϖ hP'))) from this
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U s z hz
  have : Nonempty ↥U := by use z
  /-
  Not having this double simp here yields different results funnily enough
  -/
  simp at s
  simp [skyscraperSheafOfModules, skyscraperPresheafOfModules, skyscraperAb, skyscraperSheaf,
  skyscraperPresheaf] at s
  by_cases h : z ≤ p
  ·
    have : p ∈ U := Specializes.mem_open h U.2 hz
    simp [this] at s
    have : p = z := (PClosed z h).symm
    subst this
    obtain ⟨x, hx⟩ := X.residue_surjective p s
    have : IsDiscreteValuationRing ↑(X.presheaf.stalk p) := sorry
    have : x ≠ 0 := sorry


    obtain ⟨n, u, hun⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible this hϖ
    let f := ((algebraMap ↑(X.presheaf.stalk p) ↑X.functionField) ↑u * (algebraMap ↑(X.presheaf.stalk p)
       ↑X.functionField) ϖ ^ (n - D p))

    /-
    This says there is some neighbourhood of P such that the order of vanishing of all
    non P points is trivial.

    This should be a corollary of some general topological nonsense
    -/
    have : ∃ (V : X.Opens) (_ : V ≤ U) (_ : p ∈ V), ∀ a ∈ V,
      (a ≠ p) → (ha : coheight a = 1) → Scheme.ord a ha f = 1 :=
      /-
      TODO: We need more conditions
      -/
      sorry
    obtain ⟨V, VinU, PinV, hV⟩ := this
    have : Nonempty ↥V := by use p
    let flift := sectionNE
      ((algebraMap ↑(X.presheaf.stalk p) ↑X.functionField) ↑u * (algebraMap ↑(X.presheaf.stalk p)
       ↑X.functionField) ϖ ^ (n - D p)) V
    let sec : (lineBundle h' D).val.obj (op V) := {
      val := flift
      property := by
        simp [LinearLocalPredicate.submodule, lineBundle.linearLocalPredicateNE,
        LinearLocalPredicateNE.toLinearLocalPredicate, lineBundle.P]
        intro y hy hflift a
        --rw [div_le_iff]
        --a
        by_cases k : a ∈ V
        · simp [restrict_apply, k]

          by_cases j : coheight a = 1
          · simp [div_eq_ord_of_coheight_eq_one _ _ a j]
            suffices (Scheme.ord a j f) * WithZero.exp (D a) ≥ 1 by
              /-
              Should hold by Multiplicative.toAdd_mono, and potentially some other
              monotonicity lemma
              -/
              sorry
            by_cases aP : a = p
            ·
              sorry
            ·
              specialize hV a k aP j
              rw [hV]
              simp
              suffices D a ≥ 0 by exact WithZero.le_exp_of_log_le this
              have : D a = 0 := sorry
              exact this.ge

          · simp [div_eq_zero_of_coheight_ne_one _ _ a j]
            exact hD a j
        · simp [k]

    }
    use V, (homOfLE VinU)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    ·
      sorry
    · sorry
    · exact PinV
  · /-
    Since ¬ z ≤ P, there exists a neighbourhood of z not containing P
    -/
    have : ∃ (V : X.Opens) (_ : V ≤ U) (_ : z ∈ V), p ∉ V := sorry
    obtain ⟨V, hV, hVz, hVP⟩ := this
    use V, homOfLE hV
    /-

    -/


    sorry
  /-
  Argument:

  If `z ≤ P` then `P ∈ U`, meaning `s` is given by an element of the residue field.
  We know the X.residue is surjective by X.residue_surjective, meaning there is something
  mapping

  Otherwise, we can find a neighbourhood of z not containing P, in which our guy is going
  to be surjective.
  -/


lemma quotientMapEpi (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hP' : coheight p = 1)
  (PClosed : ∀ x : X, x ≤ p → x = p) :
    Epi <| quotientMap h' D p ϖ hϖ hP' := by
    suffices Epi <| (SheafOfModules.toSheaf X.ringCatSheaf).map <| quotientMap h' D p ϖ hϖ hP' by sorry
    sorry
    --apply CategoryTheory.Sheaf.epi_of_isLocallySurjective




noncomputable
def fundamentalComplex (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hP' : coheight p = 1) :
  ShortComplex X.Modules where
  X₁ := lineBundle h' (D - single p 1)
  X₂ := lineBundle h' D
  X₃ := skyscraperSheafOfModules p
  f :=
    /-
    This is a somewhat questionable definition tbh. I don't love that we need this rewrite here,
    and I think it could be worthwhile making a version of the lineBundleMapping which
    explicitly uses D - P -> D
    -/
    let k := extend h' (D - single p 1) (single p 1) (by sorry)
    have : lineBundle h' (D - single p 1 + single p 1) = lineBundle h' D := by simp
    this ▸ k

  g := quotientMap h' D p ϖ hϖ hP'
  zero :=
    /-
    Once we have this stated properly this will follow more or less trivially by the following
    little argument.

    Proof:
    h = u ϖ^n where n ≥ 1 - D P

    g (h) = res (u ϖ ^(n + D P))
          = res (u ϖ ^ m ), m ≥ 1,
          = 0
    -/
    sorry

/-
This should be no work at all with the above definitons (at least that's the hope).
-/
lemma fundamentalComplexExact (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hP' : coheight p = 1)
    (PClosed : ∀ x : X, x ≤ p → x = p) : (fundamentalComplex h' D p ϖ hϖ hP').Exact := sorry



end lineBundle
