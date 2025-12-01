import Mathlib

open AlgebraicGeometry Opposite CategoryTheory

/-!
The following is a different way to construct sheaves of modules by specifying only the
behaviour on nonempty sets.

Notably, here we do not directly construct the sheaf of modules but start by constructing
a sheaf of abelian groups. This is mathematically irrelevant, but it leads to a lot of the
category theory nonsense being a lot easier.
-/

structure TopCat.PresheafNE (C : Type*) [Category C] (X : TopCat) where
  objNE (U : (TopologicalSpace.Opens ↑X)ᵒᵖ) [Nonempty ↥(U.unop)] : C
  mapNE {U V : (TopologicalSpace.Opens ↑X)ᵒᵖ} [Nonempty ↥(U.unop)] [Nonempty ↥(V.unop)]
      (k : U ⟶ V) : (objNE U ⟶ objNE V)
  mapNE_id (U : (TopologicalSpace.Opens ↑X)ᵒᵖ) [Nonempty ↥(U.unop)] : mapNE (𝟙 U) = 𝟙 (objNE U) :=
      by cat_disch
  mapNE_Comp {U V W : (TopologicalSpace.Opens ↑X)ᵒᵖ} [Nonempty ↥(U.unop)]
   [Nonempty ↥(V.unop)] [Nonempty ↥(W.unop)] (k : U ⟶ V) (l : V ⟶ W) :
   mapNE (k ≫ l) = mapNE k ≫ mapNE l := by cat_disch

open Classical in
noncomputable
def TopCat.PresheafNE.presheaf {X : TopCat} (M : TopCat.PresheafNE Ab X) : TopCat.Presheaf Ab X where
  obj U := if _ : Nonempty ↥(U.unop) then M.objNE U else .of PUnit
  map {U V} f := by
    split_ifs
    · exact M.mapNE f
    · exact 0
    · /-
      This branch will never be reached. I'm not sure if it's better to define the map here or
      just to bake in the contradiction to the definition.
      -/
      exact 0
    · exact 0
  map_id := by
    intro U
    split_ifs
    · simp [M.mapNE_id]
      grind
    · rename_i h
      simp [h]
      suffices Subsingleton ↑(if _ : Nonempty ↥(unop U) then M.objNE U else AddCommGrp.of PUnit) by
        ext a
        apply Subsingleton.elim
      simp [h]
      exact instSubsingletonPUnit

  map_comp := by
    intro U V W k l
    split_ifs
    · rename_i h
      by_cases hV : Nonempty ↥(V.unop)
      · simp [h, hV]
        simp [mapNE_Comp]
        cat_disch
      · simp only [h, eq_mpr_eq_cast, ↓reduceDIte, congrArg_cast_hom_left, hV,
        congrArg_cast_hom_right, Limits.zero_comp, Limits.comp_zero,
        Preadditive.IsIso.comp_left_eq_zero]
        have : ¬ Nonempty ↥(W.unop) := Set.not_nonempty_iff_eq_empty'.mpr <|
            Set.subset_eq_empty (leOfHom l.unop) <| Set.not_nonempty_iff_eq_empty'.mp hV
        simp [this]
    · rename_i hU
      by_cases hV : Nonempty ↥(V.unop)
      · have : ¬ Nonempty ↥(V.unop) := Set.not_nonempty_iff_eq_empty'.mpr <|
            Set.subset_eq_empty (leOfHom k.unop) <| Set.not_nonempty_iff_eq_empty'.mp hU
        contradiction
      · have : ¬ Nonempty ↥(W.unop) := Set.not_nonempty_iff_eq_empty'.mpr <|
            Set.subset_eq_empty (leOfHom l.unop) <| Set.not_nonempty_iff_eq_empty'.mp hV
        simp [hU, hV, this]

--variable (X : Scheme) [IsIntegral X]
--#check (constantSheaf (Opens.grothendieckTopology X) Ab).obj (.of X.functionField)
--#check constantSheaf (TopologicalSpace.Opens X)ᵒᵖ

noncomputable
def ratPresheafNE (X : Scheme) [IsIntegral X] : TopCat.PresheafNE Ab X where
  objNE U hU := AddCommGrp.of X.functionField
  mapNE {U V} hU hV k := 𝟙 <| AddCommGrp.of X.functionField

noncomputable
def ratPresheaf (X : Scheme) [IsIntegral X] : TopCat.Presheaf Ab X := (ratPresheafNE X).presheaf

universe u
def module_pos {P : Prop} (R : Type*) (M : Type u) (N : Type u) [CommRing R]
    [AddCommMonoid M] [AddCommMonoid N] [Decidable P] (h : P)
    [m : Module R M] :
    haveI : AddCommMonoid ↑(if P then M else N) := by aesop
    Module R (if P then M else N) := by
  have : (if P then M else N) = M := if_pos h
  convert m
  congr
  (expose_names;
    exact
      cast_heq (Eq.symm (id (congrArg AddCommMonoid (ite_cond_eq_true M N (eq_true h))))) inst_1)

def module_pos_of_ab {P : Prop} (R : Type*) (M N : AddCommGrp) [CommRing R]
    [Decidable P] (h : P) [m : Module R M] :
    Module R (AddCommGrp.carrier (if P then M else N)) := by
  have : (if P then M else N) = M := if_pos h
  convert m
  congr

def module_neg_of_ab {P : Prop} (R : Type*) (M N : AddCommGrp) [CommRing R]
    [Decidable P] (h : ¬P) [m : Module R N] :
    Module R (AddCommGrp.carrier (if P then M else N)) := by
  have : (if P then M else N) = N := if_neg h
  convert m
  congr

universe v
open Classical in
noncomputable
instance p (X : Scheme) [IsIntegral X] (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    Module ↑(X.ringCatSheaf.val.obj U) ↑((ratPresheaf.{v} X).obj U) := by
  simp [ratPresheaf, ratPresheafNE, TopCat.PresheafNE.presheaf]
  split_ifs
  · rename_i h
    suffices Module ↑(X.sheaf.val.obj U) ↑X.functionField by
      exact module_pos_of_ab ↑(X.sheaf.val.obj U) (AddCommGrp.of ↑(X.functionField)) (AddCommGrp.of PUnit) h
    have : Nonempty ↑(unop U) := h
    exact (X.germToFunctionField (unop U)).hom.toModule
  · rename_i h
    suffices Module ↑(X.sheaf.val.obj U) ↑(PUnit.{v+1}) by
      exact module_neg_of_ab ↑(X.sheaf.val.obj U) (AddCommGrp.of ↑(X.functionField)) (AddCommGrp.of PUnit) h
    exact PUnit.module

instance thingy {X : Scheme.{u}} {U V : X.Opens} (k : V ≤ U) : Module Γ(X, U) Γ(X, V) := (X.sheaf.val.map (homOfLE k).op).hom.toModule

instance {X : Scheme.{u}} [IsIntegral X] {U V : X.Opens} (k : V ≤ U) [Nonempty U] [Nonempty V] :
    letI := thingy k
    IsScalarTower Γ(X, U) Γ(X, V) X.functionField := by

  suffices X.germToFunctionField U = X.sheaf.val.map (homOfLE k).op ≫ (X.germToFunctionField V) by
    simp [thingy]

    sorry
  exact
    Eq.symm
      (TopCat.Presheaf.germ_res X.sheaf.val (homOfLE k) (genericPoint ↥X)
        (Scheme.germToFunctionField._proof_1 X V))

open Classical in
/--
TODO:

This is now the one remaining part of the sheaf of rational functions API that I wanted, meaning
this method has shown to (at least locally) produce better results.

That said, this proof is more annoying than expected
-/
noncomputable
def ratPresheafOfModules (X : Scheme) [IsIntegral X] : PresheafOfModules (X.ringCatSheaf.val) := by
  apply PresheafOfModules.ofPresheaf (ratPresheaf X)
  intro U V k a s

  by_cases hU : Nonempty ↥(U.unop)
  · by_cases hV : Nonempty ↥(V.unop)
    · simp [ratPresheaf, ratPresheafNE,TopCat.PresheafNE.presheaf, hU, hV]

      have : ↑((ratPresheaf X).obj U) = ↑((ratPresheaf X).obj V) := by
        simp [ratPresheaf, ratPresheafNE,TopCat.PresheafNE.presheaf, hU, hV]
      let m : Module ↑(X.sheaf.val.obj V) ↑((ratPresheaf X).obj U) := by
        rw [this]
        exact p X V
      --have : ↑a = this ▸ ((X.sheaf.val.map k) a) := sorry
      /-
      Here we need to show that a • s = (X.sheaf.val.map k) a • s, except that because
      a • s lives in K(U) and (X.sheaf.val.map k) a • s lives in K(V), there's also a bunch of
      eqToHoms floating around/
      -/
      --unfold_projs

      suffices a • s = (X.sheaf.val.map k) a • s by


        --convert this

        --rw [this]
        --simp_all [sheafCompose_obj_val, Functor.comp_obj, CommRingCat.forgetToRingCat_obj, eq_mpr_eq_cast, m]

        sorry
      --convert this

      --rw [this]

      let testing : Module (X.presheaf.obj U) (X.presheaf.obj V) := by exact (X.sheaf.val.map k).hom.toModule
      have : Nonempty (U.unop) := hU
      have : Nonempty (V.unop) := hV
      let m : Module (X.presheaf.obj U) X.functionField := (X.germToFunctionField (unop U)).hom.toModule
      let m' : Module (X.presheaf.obj V) X.functionField := (X.germToFunctionField (unop V)).hom.toModule
      let test : IsScalarTower (X.presheaf.obj U) (X.presheaf.obj V) ↑X.functionField := by
        simp [m, m']

        sorry

                --AlgebraicGeometry.functionField_isScalarTower X U ⟨z, o⟩

      sorry
    · simp_all [ratPresheaf, ratPresheafNE,TopCat.PresheafNE.presheaf]
  --simp_all [ratPresheaf, ratPresheafNE]
  · by_cases hV : Nonempty ↥(V.unop)
    · simp_all [ratPresheaf, ratPresheafNE,TopCat.PresheafNE.presheaf]
    · simp_all [ratPresheaf, ratPresheafNE,TopCat.PresheafNE.presheaf]

lemma isSheaf_of_integral (X : Scheme) [IsIntegral X] :
    TopCat.Presheaf.IsSheaf (ratPresheafOfModules X).presheaf := by sorry

noncomputable
def sheafOfRationalFunctions (X : Scheme) [IsIntegral X] : X.Modules where
  val := ratPresheafOfModules X
  isSheaf := isSheaf_of_integral X

@[simp]
lemma sheafOfRationalFunctions_nonempty {X : Scheme.{u}} [IsIntegral X] (U : X.Opens)
    [h : Nonempty ↥U] :
    ↑((sheafOfRationalFunctions X).val.obj (op U)) = X.functionField.1 := by
    simp [sheafOfRationalFunctions, ratPresheafOfModules, ratPresheaf, ratPresheafNE,
        TopCat.PresheafNE.presheaf, h]

def sectionNE {X : Scheme.{u}} [IsIntegral X] (f : X.functionField) (U : X.Opens) [h : Nonempty ↥U] :
    (sheafOfRationalFunctions X).val.obj (op U) := sheafOfRationalFunctions_nonempty U ▸ f
--#print sectionNE
def sectionNEToFunctionField {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [h : Nonempty ↥U]
    (s : (sheafOfRationalFunctions X).val.obj (op U)) : X.functionField :=
  (sheafOfRationalFunctions_nonempty U).symm ▸ s

@[simp]
lemma sectionNEsectionNEToFunctionField {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [h : Nonempty ↥U]
  (s : (sheafOfRationalFunctions X).val.obj (op U)) : sectionNE (sectionNEToFunctionField U s) U = s := by
  simp [sectionNE, sectionNEToFunctionField]
  grind

@[simp]
lemma sectionNEToFunctionFieldsectionNE {X : Scheme.{u}} [IsIntegral X] (f : X.functionField)
    (U : X.Opens) [h : Nonempty ↥U] :
    sectionNEToFunctionField U (sectionNE f U) = f := by
  simp [sectionNE, sectionNEToFunctionField]
  grind

lemma ModuleCat.ite_zero {P : Prop} [Decidable P] {R : CommRingCat} {b : ModuleCat R} {c : Type*}
    [l : AddCommGroup c] [n : Module R c] (h : P) :
    --(t : (if _ : P then ModuleCat.of R c else b) = c) :
    (by simp[h] : (if _ : P then ModuleCat.of R c else b) = c) ▸
    ((if _ : P then ModuleCat.of R c else b).isAddCommGroup.toZero.zero) = (0 : c) := by
  unfold_projs
  grind

lemma Ab.ite_zero {P : Prop} [Decidable P] {b : AddCommGrp} {c : Type*}
    [l : AddCommGroup c] (h : P) :
    (by simp[h] : (if _ : P then AddCommGrp.of c else b) = c) ▸
    (0 : (if _ : P then AddCommGrp.of c else b).carrier) = (0 : c) := by
  unfold_projs
  grind


lemma Ab.ite_ne_zero {P : Prop} [Decidable P] {b : AddCommGrp} {c : Type*}
    [l : AddCommGroup c] (h : P) (s : (if _ : P then AddCommGrp.of c else b).carrier) (hs : s ≠ 0) :
    (by simp[h] : (if _ : P then AddCommGrp.of c else b) = c) ▸
    s ≠ (0 : c) := by
  rw [← Ab.ite_zero h (b := b)]
  grind

lemma Ab.ite_add {P : Prop} [Decidable P] {b : AddCommGrp} {c : Type*}
    [l : AddCommGroup c] (h : P) (x y : ↑(if _ : P then AddCommGrp.of c else b)) :
    (by simp[h] : (if _ : P then AddCommGrp.of c else b) = c) ▸
    ((x : (if _ : P then AddCommGrp.of c else b).carrier) + y) =
    (by simp[h] : (if _ : P then AddCommGrp.of c else b) = c) ▸ x +
    (by simp[h] : (if _ : P then AddCommGrp.of c else b) = c) ▸ y := by
  unfold_projs
  grind


/-
The problem here, I think, is that a priori the module structure on this if thing may be different
to the module structure on c
-/
lemma Ab.ite_smul {P : Prop} [Decidable P] {R : CommRingCat} {b : AddCommGrp} {c : Type*}
    [l : AddCommGroup c] [n : Module R c] [AddCommGroup b] [Module R b] (h : P) (x : R)
    (y : ↑(if _ : P then AddCommGrp.of c else b)) :
    letI : Module R ↑(if _ : P then AddCommGrp.of c else b) := module_pos_of_ab R (AddCommGrp.of c) b h
    (by simp[h] : (if _ : P then AddCommGrp.of c else b) = c) ▸
    (x • y) = x • (by simp[h] : (if _ : P then AddCommGrp.of c else b) = c) ▸ y := by
  unfold_projs
  simp [module_pos_of_ab]
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
--#print ModuleCat.ite_smul._proof_1_17

open Classical
@[simp]
lemma sectionNEToFunctionField_zero {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [h : Nonempty ↥U]
    : sectionNEToFunctionField U 0 = 0 := by
  unfold_projs
  dsimp [sectionNEToFunctionField, sheafOfRationalFunctions, sheafOfRationalFunctions,
        ratPresheafOfModules, ratPresheaf, ratPresheafNE,
        TopCat.PresheafNE.presheaf, h]
  generalize_proofs a b
  let h' : Nonempty U := h
  let k : AddCommGroup X.functionField := inferInstance
  let m : Module ↑(X.sheaf.val.obj (op U)) ↑X.functionField := (X.germToFunctionField U).hom.toModule

  have := Ab.ite_zero (P := Nonempty ↥U)
    (b := AddCommGrp.of PUnit.{u + 1})
    (c := X.functionField.1) (l := k) h
  convert this

open Classical
@[simp]
lemma sectionNEToFunctionField_ne_zero {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [h : Nonempty ↥U]
    (s : ↑((sheafOfRationalFunctions X).val.obj (op U))) (hs : s ≠ 0): sectionNEToFunctionField U s ≠ 0 := by
  unfold_projs
  dsimp [sectionNEToFunctionField, sheafOfRationalFunctions, sheafOfRationalFunctions,
        ratPresheafOfModules, ratPresheaf, ratPresheafNE,
        TopCat.PresheafNE.presheaf, h]
  generalize_proofs a b
  let h' : Nonempty U := h
  let k : AddCommGroup X.functionField := inferInstance
  let m : Module ↑(X.sheaf.val.obj (op U)) ↑X.functionField := (X.germToFunctionField U).hom.toModule

  have := Ab.ite_ne_zero (P := Nonempty ↥U)
    (b := AddCommGrp.of PUnit.{u + 1})
    (c := X.functionField.1) (l := k) h s hs
  exact this
  --rw [← this]
  --convert this


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
  erw [Ab.ite_add (P := Nonempty ↥U)
    (b := AddCommGrp.of PUnit.{u + 1})
    (c := X.functionField.1) (l := k) h s s']

@[simp]
lemma sectionNEToFunctionField_smul {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [h : Nonempty ↥U]
    (a : Γ(X, U)) (s : ↑((sheafOfRationalFunctions X).val.obj (op U))) :
    letI : Nonempty U := h
    letI : Algebra Γ(X, U) X.functionField := (X.germToFunctionField U).hom.toAlgebra
    sectionNEToFunctionField U (a • s) = a • sectionNEToFunctionField U s := by
  simp  [sectionNEToFunctionField, sheafOfRationalFunctions, sheafOfRationalFunctions,
        ratPresheafOfModules, ratPresheaf, ratPresheafNE,
        TopCat.PresheafNE.presheaf, h]
  let h' : Nonempty U := h
  let k : AddCommGroup X.functionField := inferInstance
  let m : Module ↑(X.sheaf.val.obj (op U)) ↑X.functionField := (X.germToFunctionField U).hom.toModule
  let o : Module ↑(X.sheaf.val.obj (op U))
    ↑(if x : Nonempty ↥U then AddCommGrp.of ↑X.functionField
      else { carrier := PUnit.{u + 1}, str := PUnit.addCommGroup }) := p X (op U)
  have := Ab.ite_smul (P := Nonempty ↥U) (R := ↑(X.sheaf.val.obj (op U)))
    (b := AddCommGrp.mk PUnit.{u + 1})
    (c := X.functionField.1) (l := k) (n := m) h a s
  simp [module_pos_of_ab, m] at this
  convert this
  simp_all [p, module_pos_of_ab]

@[simp]
lemma sectionNEToFunctionField_res {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) [hU : Nonempty ↥U] (V : X.Opens) [hV : Nonempty ↥V]
    (k : V ≤ U) (s : ↑((sheafOfRationalFunctions X).val.obj (op U))) :
    sectionNEToFunctionField V ((sheafOfRationalFunctions X).val.presheaf.map (homOfLE k).op s) =
    sectionNEToFunctionField U s := by
  simp [sectionNEToFunctionField, sheafOfRationalFunctions, sheafOfRationalFunctions,
        ratPresheafOfModules, ratPresheaf, ratPresheafNE,
        TopCat.PresheafNE.presheaf, hU, hV]
  congr 1
  all_goals try simp_all
  · refine Function.hfunext rfl ?_
    intro a a' h
    simp_all only [heq_eq_eq]
    subst h
    refine Function.hfunext ?_ ?_
    · simp [hU, hV]
    · simp [hU, hV]
  · generalize_proofs a b
    have := CategoryTheory.eqToHom_heq_id_dom _ _ b
    have : ConcreteCategory.hom (eqToHom b) ≍ ConcreteCategory.hom (𝟙 (if Nonempty ↥U then AddCommGrp.of ↑X.functionField else AddCommGrp.of PUnit.{u + 1})) := by sorry
    --have : ConcreteCategory.hom (eqToHom b) ≍ ConcreteCategory.hom <| 𝟙 (if Nonempty ↥U then AddCommGrp.of ↑X.functionField else AddCommGrp.of PUnit.{u + 1}) := sorry
    have : ∀ r, eqToHom b r ≍ 𝟙 (if Nonempty ↥U then AddCommGrp.of ↑X.functionField else AddCommGrp.of PUnit.{u + 1}) r := by

      intro r
      --cases this

      --apply congr_arg_heq
      --have : (ConcreteCategory.hom (eqToHom b)).toFun ≍
  --(ConcreteCategory.hom (𝟙 (if Nonempty ↥U then AddCommGrp.of ↑X.functionField else AddCommGrp.of PUnit.{u + 1}))).toFun := by sorry
      --#check congr_heq (f := (ConcreteCategory.hom (eqToHom b))) (g := (ConcreteCategory.hom (𝟙 (if Nonempty ↥U then AddCommGrp.of ↑X.functionField else AddCommGrp.of PUnit.{u + 1}))))
      --#check dcongr_heq this
      --#check Function.hfunext
      --#check congrArg


      --rw [ConcreteCategory.ext_iff] at this
      --intro r
      --#check congr_heq this (by sorry : r ≍ r)
      --exact congr_arg_heq this
      sorry
    exact this s
