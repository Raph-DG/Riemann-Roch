import Mathlib
import RiemannRoch.SheafOfModules.Nonempty
import RiemannRoch.SheafOfModules.Subsheaf

open CategoryTheory Opposite
universe u

/-
It might be easiest to do this in the case where X is irreducible, because then we
get module instances all the way down
-/
variable {X : Type*} [TopologicalSpace X] (R : (TopologicalSpace.Opens X)ᵒᵖ ⥤ RingCat.{u})
  --(A : Type*) [CommRing A] [Module (R.obj ⊤) A]
  --(l : ∀ U : (TopologicalSpace.Opens X)ᵒᵖ, [Nonempty (U.unop)] → Module (R.obj U) A)
  /-
  We need to somehow say that all of these module structures are equivalent
  -/
  --(l : ∀ U : (TopologicalSpace.Opens X)ᵒᵖ, [Nonempty (U.unop)] → ModuleCat (R.obj U))

#check TopCat.Sheaf
#check (constantSheaf (Opens.grothendieckTopology X) Ab).obj

/-
def constantPresheafNE : PresheafOfModulesNE R where
  obj U hU := ModuleCat.of (R.obj U) A
  map := by
    intro a b c d f
    apply ModuleCat.ofHom (Y := (ModuleCat.restrictScalars
                (RingCat.Hom.hom (R.map f))).obj
                (ModuleCat.of ↑(R.obj b) (ModuleCat.of (↑(R.obj b)) A)))
    exact {
      toFun a := a
      map_add' x y := rfl
      map_smul' o g := by
        rw [@RingHom.id_apply]
        congr

        /-
        We should come up with some abstraction that does this for free, or at least without so
        much coersion.
        -/
        sorry
    }

noncomputable
def constantPresheaf : PresheafOfModules R := PresheafOfModules.mk' R <| constantPresheafNE R A l-/

open TopCat

#check PresheafOfModules.ofPresheaf
open AlgebraicGeometry
noncomputable
def presheafNEOfRationalFunctions (X : Scheme.{u}) [IsIntegral X] :
    PresheafOfModulesNE X.ringCatSheaf.val :=
  let m (U : X.Opensᵒᵖ) [Nonempty ↥(unop U)] :
    Module ↑(X.ringCatSheaf.val.obj U) ↑X.functionField := 
      have : Nonempty ↑(unop U) := by assumption
      (X.germToFunctionField (unop U)).hom.toModule
      --have k : (unop U) ≤ ⊤ := by exact fun ⦃a⦄ a ↦ _root_.trivial
      --#check X.ringCatSheaf.val.map (homOfLE k).op
      --X.presheaf.map


      --have : Nonempty ↑(unop U) := by assumption
      --(X.germToFunctionField (unop U)).hom.toModule
  {
    obj U hU := ModuleCat.of _ X.functionField
    map {U V} hU hV k := by
      have : Nonempty ↑(unop U) := hU
      apply ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (RingCat.Hom.hom (X.ringCatSheaf.val.map k))).obj
        (ModuleCat.of ↑(X.ringCatSheaf.val.obj V) ↑X.functionField))
      exact {
        toFun a := a
        map_add' := by simp
        map_smul' a f := by 
          let j : Module ↑(X.ringCatSheaf.val.obj U) ↑(X.ringCatSheaf.val.obj V) := (X.ringCatSheaf.val.map k).hom.toModule
          let p : IsScalarTower ↑(X.ringCatSheaf.val.obj U) ↑(X.ringCatSheaf.val.obj V) X.functionField := sorry
          
          --let test : IsScalarTower ↑(X.ringCatSheaf.val.obj U) (↑((ModuleCat.restrictScalars (CommRingCat.Hom.hom (X.sheaf.val.map k))).obj (ModuleCat.of ↑(X.ringCatSheaf.val.obj V) ↑X.functionField))) X.functionField := sorry
          
          simp [m, Scheme.germToFunctionField]
          #check IsScalarTower
          congr

          
          --refine Module.ext ?_
          

          


          sorry
      }
      --sorry
  }

open AlgebraicGeometry
noncomputable
def presheafOfRationalFunctions (X : Scheme.{u}) [IsIntegral X] :
    PresheafOfModules X.ringCatSheaf.val :=
  let m (U : X.Opensᵒᵖ) [Nonempty ↥(unop U)] :
    Module ↑(X.presheaf.obj U) ↑X.functionField := --inferInstanceAs <| Module ↑(X.presheaf.obj U) ↑X.functionField
      have : Nonempty ↑(unop U) := by assumption
      (X.germToFunctionField (unop U)).hom.toModule
  sorry

  --constantPresheaf X.ringCatSheaf.val X.functionField m

/-
This is easier than the general thing and all I really care about, so let's just generalise later.

Tbh I think the same proof should work for topological spaces and replacing the function field with
an arbitrary thing satisfying that it's a module over Γ(X, U) for every nonempty U
(where Γ(X, U) I guess now can denote the sections of some arbitrary sheaf on U).
-/
lemma isSheaf_of_integral (X : Scheme) [IsIntegral X] :
    TopCat.Presheaf.IsSheaf (presheafOfRationalFunctions X).presheaf := by

  rw [Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf sf_comp
  /-
  This is a little bit silly, we should probably just write some API
  -/
  by_cases h : ∃ i : ι, Nonempty (U i)
  · have p : Nonempty <| (iSup U : X.Opens) := sorry
    obtain ⟨i, hi⟩ := h
    obtain ⟨x, _⟩ := Classical.exists_true_of_nonempty hi
    let gl : ToType ((presheafOfRationalFunctions X).presheaf.obj (op (iSup U))) := by
      have : Nonempty ↥(iSup U) := sorry
      simp [presheafOfRationalFunctions, constantPresheaf, PresheafOfModules.mk', this]
      split_ifs
      simp [constantPresheafNE]
      let s := sf i
      simp [presheafOfRationalFunctions, constantPresheaf, PresheafOfModules.mk'] at s
      split_ifs at s
      · simp [constantPresheafNE] at s
        exact s
      · contradiction

    use gl
    constructor
    --refine ⟨⟨gl, ?_⟩, ?_, ?_⟩
    · simp [gl]
      split_ifs
      · cat_disch
      · contradiction
    · intro gl' hgl'
      simp [gl]
      cat_disch

  ·
    /-
    In this case, there is no nonempty set in the cover so we pick the only thing
    possible, the unique section of the empty set. This should be trivial once we get
    past all the garbage.
    -/
    sorry
/-
Once we have this sheaf of rational functions, the idea will be to construct `𝒪ₓ(D)`
using this IsLinearLocalPredicate business. So I suppose we should construct some
notion of a linear local predicate associated to this thing.

In that case, it's probably good for usability to define some sheafification of
predicates like we have in the LocalPredicate library if we want to have our tensor product
construction at some point. For now though we should just be able to show that

-/

/-
TODO: get a better name for this stupid sheaf
-/
noncomputable
def sheafOfRationalFunctions (X : Scheme) [IsIntegral X] : X.Modules where
  val := presheafOfRationalFunctions X
  isSheaf := isSheaf_of_integral X

@[simp]
lemma sheafOfRationalFunctions_nonempty {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [h : Nonempty ↥U] :
    ↑((sheafOfRationalFunctions X).val.obj (op U)) = X.functionField.1 := by
  simp [sheafOfRationalFunctions, presheafOfRationalFunctions, constantPresheaf,
    PresheafOfModules.mk', constantPresheafNE, h]

def sectionNE {X : Scheme.{u}} [IsIntegral X] (f : X.functionField) (U : X.Opens) [h : Nonempty ↥U] :
    (sheafOfRationalFunctions X).val.obj (op U) := (sheafOfRationalFunctions_nonempty U) ▸ f

def sectionNEToFunctionField {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [h : Nonempty ↥U]
    (s : (sheafOfRationalFunctions X).val.obj (op U)) : X.functionField :=
  (sheafOfRationalFunctions_nonempty U) ▸ s

@[simp]
lemma sectionNE_zero {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [h : Nonempty ↥U] :
    sectionNE 0 U = 0 := by

  simp [sectionNE]
  let k := sheafOfRationalFunctions_nonempty U (h := h)
  sorry

lemma iteThing {P : Prop} [Decidable P] (h : P) (R : CommRingCat) (b : ModuleCat R) (a : Type*)
   [AddCommGroup a] [Module R a] :
    (if P then ModuleCat.of R a else b) = a := by simp [h]

lemma ModuleCat.ite_zero {P : Prop} [Decidable P] {R : CommRingCat} {b : ModuleCat R} {c : Type*}
    [l : AddCommGroup c] [n : Module R c] (h : P) :
    --(t : (if _ : P then ModuleCat.of R c else b) = c) :
    (by simp[h] : (if _ : P then ModuleCat.of R c else b) = c) ▸
    ((if _ : P then ModuleCat.of R c else b).isAddCommGroup.toZero.zero) = (0 : c) := by
  unfold_projs
  grind

lemma ModuleCat.ite_add {P : Prop} [Decidable P] {R : CommRingCat} {b : ModuleCat R} {c : Type*}
    [l : AddCommGroup c] [n : Module R c] (h : P) (x y : ↑(if _ : P then ModuleCat.of R c else b)) :
    (by simp[h] : (if _ : P then ModuleCat.of R c else b) = c) ▸
    ((if _ : P then ModuleCat.of R c else b).isAddCommGroup.add x y) =
    (by simp[h] : (if _ : P then ModuleCat.of R c else b) = c) ▸ x +
    (by simp[h] : (if _ : P then ModuleCat.of R c else b) = c) ▸ y := by
  unfold_projs
  grind

lemma ModuleCat.ite_smul {P : Prop} [Decidable P] {R : CommRingCat} {b : ModuleCat R} {c : Type*}
    [l : AddCommGroup c] [n : Module R c] (h : P) (x : R) (y : ↑(if _ : P then ModuleCat.of R c else b)) :
    (by simp[h] : (if _ : P then ModuleCat.of R c else b) = c) ▸
    (x • y) = x • (by simp[h] : (if _ : P then ModuleCat.of R c else b) = c) ▸ y := by
  unfold_projs
  grind

/-
lemma ModuleCat.ite_res {P P' : Prop} [Decidable P] [Decidable P'] {R : CommRingCat}
    {b : ModuleCat R} {c : Type*}
    [l : AddCommGroup c] [n : Module R c] (h : P) (h' : P')
    (x : ↑(if _ : P then ModuleCat.of R c else b))
    (y : ↑(if _ : P' then ModuleCat.of R c else b)) :
    (by simp[h] : (if _ : P then ModuleCat.of R c else b) = c) ▸ x =
    (by simp[h'] : (if _ : P' then ModuleCat.of R c else b) = c) ▸ y := by
  unfold_projs
  sorry
  --grind-/

/-
I think these silly lemmas are unfortunately going to be important
-/

lemma iteThing3 {P : Prop} [Decidable P] {R : CommRingCat} {b : ModuleCat R} {c : Type*}
    [l : AddCommGroup c] [n : Module R c] (h : ¬P) :
    (by simp[h] : (if _ : P then b else ModuleCat.of R c) = c) ▸
    ((if _ : P then b else ModuleCat.of R c).isAddCommGroup.toZero.zero) = (0 : c) := by
  unfold_projs
  grind


open Classical
@[simp]
lemma sectionNEToFunctionField_zero {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [h : Nonempty ↥U]
    : sectionNEToFunctionField U 0 = 0 := by
  unfold_projs
  dsimp [sectionNEToFunctionField, sheafOfRationalFunctions, presheafOfRationalFunctions,
    constantPresheaf, constantPresheafNE, PresheafOfModules.mk', h, ModuleCat.ite_zero]
  generalize_proofs a b
  let h' : Nonempty U := h
  let k : AddCommGroup X.functionField := inferInstance
  let m : Module ↑(X.sheaf.val.obj (op U)) ↑X.functionField := (X.germToFunctionField U).hom.toModule
  have : (if x : Nonempty ↥U then ModuleCat.of ↑(X.sheaf.val.obj (op U)) ↑X.functionField
          else ModuleCat.of (↑(X.sheaf.val.obj (op U))) PUnit.{u + 1}) =
          ModuleCat.of ↑(X.sheaf.val.obj (op U)) ↑X.functionField := by
      split_ifs
      rfl
  rw[ModuleCat.ite_zero (P := Nonempty ↥U) (R := ↑(X.sheaf.val.obj (op U)))
    (b := ModuleCat.of (↑(X.sheaf.val.obj (op U))) PUnit.{u + 1})
    (c := X.functionField.1) (l := k) (n := m) h]
  rfl


@[simp]
lemma sectionNEToFunctionField_add {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [h : Nonempty ↥U]
    (s s' : ↑((sheafOfRationalFunctions X).val.obj (op U))) :
    sectionNEToFunctionField U (s + s') =
    sectionNEToFunctionField U s + sectionNEToFunctionField U s' := by
  simp [sectionNEToFunctionField]
  let h' : Nonempty U := h
  let k : AddCommGroup X.functionField := inferInstance
  let m : Module ↑(X.sheaf.val.obj (op U)) ↑X.functionField := (X.germToFunctionField U).hom.toModule
  have : (if x : Nonempty ↥U then ModuleCat.of ↑(X.sheaf.val.obj (op U)) ↑X.functionField
          else ModuleCat.of (↑(X.sheaf.val.obj (op U))) PUnit.{u + 1}) =
          ModuleCat.of ↑(X.sheaf.val.obj (op U)) ↑X.functionField := by
      split_ifs
      rfl
  erw [ModuleCat.ite_add (P := Nonempty ↥U) (R := ↑(X.sheaf.val.obj (op U)))
    (b := ModuleCat.of (↑(X.sheaf.val.obj (op U))) PUnit.{u + 1})
    (c := X.functionField.1) (l := k) (n := m) h s s']

@[simp]
lemma sectionNEToFunctionField_smul {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [h : Nonempty ↥U]
    (a : Γ(X, U)) (s : ↑((sheafOfRationalFunctions X).val.obj (op U))) :
    letI : Nonempty U := h
    letI : Algebra Γ(X, U) X.functionField := (X.germToFunctionField U).hom.toAlgebra
    sectionNEToFunctionField U (a • s) = a • sectionNEToFunctionField U s := by
  simp [sectionNEToFunctionField]
  let h' : Nonempty U := h
  let k : AddCommGroup X.functionField := inferInstance
  let m : Module ↑(X.sheaf.val.obj (op U)) ↑X.functionField := (X.germToFunctionField U).hom.toModule
  have : (if x : Nonempty ↥U then ModuleCat.of ↑(X.sheaf.val.obj (op U)) ↑X.functionField
          else ModuleCat.of (↑(X.sheaf.val.obj (op U))) PUnit.{u + 1}) =
          ModuleCat.of ↑(X.sheaf.val.obj (op U)) ↑X.functionField := by
      split_ifs
      rfl
  rw [ModuleCat.ite_smul (P := Nonempty ↥U) (R := ↑(X.sheaf.val.obj (op U)))
    (b := ModuleCat.of (↑(X.sheaf.val.obj (op U))) PUnit.{u + 1})
    (c := X.functionField.1) (l := k) (n := m) h a s]

--sectionNEToFunctionField V ((ConcreteCategory.hom ((sheafOfRationalFunctions X).val.presheaf.map (homOfLE k).op)) f')
@[simp]
lemma sectionNEToFunctionField_res {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) [hU : Nonempty ↥U] (V : X.Opens) [hV : Nonempty ↥V]
    (k : V ≤ U) (s : ↑((sheafOfRationalFunctions X).val.obj (op U))) :
    sectionNEToFunctionField V ((sheafOfRationalFunctions X).val.presheaf.map (homOfLE k).op s) =
    sectionNEToFunctionField U s := by
  unfold_projs
  --simp [sectionNEToFunctionField]

  simp [sectionNEToFunctionField, sheafOfRationalFunctions, presheafOfRationalFunctions,
    constantPresheaf, constantPresheafNE, PresheafOfModules.mk', hU, hV]
  let h' : Nonempty U := hU
  let m : Module ↑(X.sheaf.val.obj (op U)) ↑X.functionField := (X.germToFunctionField U).hom.toModule
  --erw [ModuleCat.comp_apply, ModuleCat.comp_apply]
  --simp
  --unfold_projs

  sorry
  /-
  --erw [ConcreteCategory.comp_apply]
  --rw [CategoryTheory.GradedObject.eqToHom_apply]
  generalize_proofs a b c d e f

  congr 1
  · simp [hU, hV]
  · refine Function.hfunext rfl ?_
    intro a b c
    simp_all only [nonempty_subtype, heq_eq_eq]
    subst c
    obtain ⟨w, h⟩ := hV

    sorry
  ·
    sorry
  · exact
    proof_irrel_heq (sheafOfRationalFunctions_nonempty V) (sheafOfRationalFunctions_nonempty U)
  --unfold_projs


  #check ModuleCat.Hom.hom'
  --have : ModuleCat.ofHom { toFun := fun a : X.functionField ↦ a, map_add' := (by simp), map_smul' := (by simp)} = 𝟙 (ModuleCat.of Γ(X, U) X.functionField) := rfl

  --generalize_proofs a b c d e f g h i j k l


  sorry-/
