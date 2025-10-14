import Mathlib

open AlgebraicGeometry Opposite CategoryTheory

universe u v w z

variable (X : Scheme.{w}) [IsIntegral X]

/-!

# Sheaf of Rational Functions

In this file, we define the sheaf of rational functions on an integral scheme,
i.e. just the constant sheaf taking every open set to X.functionField.

The idea is we want to show that the sheaf of rational functions is indeed a sheaf. Of course,
in the case of an integral scheme, we 

-/
#check constantSheaf


/-
Hmm, this may be a slight issue. It really seems like we always need to do this
silly case distinction. Of course, in the empty case, there is only one option.

I don
-/
noncomputable
def K : PresheafOfModules X.ringCatSheaf.val where
  obj U := sorry /-by
    by_cases h : Nonempty U.unop
    let k : Module Γ(X, (U.unop)) ↑X.functionField := by exact Algebra.toModule
    exact ModuleCat.of Γ(X, U.unop) X.functionField
    exact ModuleCat.of Γ(X, U.unop) PUnit-/
  map := sorry



--variable (objNe : (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) → Nonempty U.unop → ModuleCat ↑(X.ringCatSheaf.val.obj U))
         --(mapNe : )

         --(mapNE {X Y : Cᵒᵖ} (f : X ⟶ Y) : obj X ⟶ (ModuleCat.restrictScalars (R.map f).hom).obj (obj Y))


/-
I'm not sure whether it's best to use the sheaf of modules infrastructure here
or just to define a sheaf of abelian groups for K.
-/

#check PresheafOfModules
open Opposite
structure PresheafOfModulesNE {X : Type*} [TopologicalSpace X]
    (R : (TopologicalSpace.Opens X)ᵒᵖ ⥤ RingCat.{u}) where
  obj (U : (TopologicalSpace.Opens X)ᵒᵖ) [Nonempty (U.unop)] : ModuleCat.{v} (R.obj U)
  map {U V : (TopologicalSpace.Opens X)ᵒᵖ} [Nonempty U.unop] [Nonempty V.unop]
      (f : U ⟶ V) : obj U ⟶ (ModuleCat.restrictScalars (R.map f).hom).obj (obj V)
  map_id (U : (TopologicalSpace.Opens X)ᵒᵖ) [Nonempty U.unop] :
    map (𝟙 U) = (ModuleCat.restrictScalarsId' (R.map (𝟙 U)).hom
      (congrArg RingCat.Hom.hom (R.map_id U))).inv.app _ := by
        cat_disch
  map_comp {U V W : (TopologicalSpace.Opens X)ᵒᵖ} [Nonempty U.unop]
    [Nonempty V.unop] [Nonempty W.unop] (f : U ⟶ V) (g : V ⟶ W) :
    map (f ≫ g) = map f ≫ (ModuleCat.restrictScalars _).map (map g) ≫
      (ModuleCat.restrictScalarsComp' (R.map f).hom (R.map g).hom (R.map (f ≫ g)).hom
        (congrArg RingCat.Hom.hom <| R.map_comp f g)).inv.app _ := by cat_disch

instance test (U V : X.Opens) (h : U ≤ V) : Algebra Γ(X, V) Γ(X, U) := by sorry

/-
Typeclass synthesis is really struggling with this
-/
/-
instance [IsIntegral X] (U V : X.Opens) (h : U ≤ V) :
  let t := test X U V h
  IsScalarTower Γ(X, V) Γ(X, U) X.functionField := sorry-/


#check IsScalarTower
#check algebraMap

lemma testing {M N α : Type*} [CommRing M] [CommRing N] [CommRing α]
    [Algebra M N] [Algebra N α] [Algebra M α] [IsScalarTower M N α] (m : M) (a : α) :
    m • a = (algebraMap M N m) • a := algebra_compatible_smul N m a


/-
This really should be essentially a one liner, but alas.

I suppose what we could do with
-/

noncomputable
def KNE [IsIntegral X] : PresheafOfModulesNE X.ringCatSheaf.val where
  obj U hU :=
    have : Nonempty U.unop := hU
    let m : Module Γ(X, unop U) X.functionField := Algebra.toModule
    let m' : Module (↑(X.ringCatSheaf.val.obj U)) X.functionField := by exact m
    ModuleCat.of (↑(X.ringCatSheaf.val.obj U)) X.functionField
  map {U V} hU hV f := by
    have : Nonempty U.unop := hU
    let m1 : Module Γ(X, unop U) X.functionField := Algebra.toModule
    let m1' : Module (↑(X.ringCatSheaf.val.obj U)) X.functionField := m1
    have : Nonempty V.unop := hV
    let m : Module Γ(X, unop V) X.functionField := Algebra.toModule
    let m' : Module (↑(X.ringCatSheaf.val.obj V)) X.functionField := m
    apply ModuleCat.ofHom (Y := (ModuleCat.restrictScalars
                (RingCat.Hom.hom (X.ringCatSheaf.val.map f))).obj
                (ModuleCat.of ↑(X.ringCatSheaf.val.obj V) ↥(X.functionField)))
    exact {
      toFun g := g
      map_add' x y := rfl

      map_smul' m x := by
        /-
        This whole business suggests to me there's something wrong with the
        SheafOfModules API, but I can't figure out precisely what the problem is
        other than when working with sheaves, typeclasses no longer work properly.
        -/
        let k : Module ↑(X.sheaf.val.obj U) ↑X.functionField := m1
        let j : Module ↑(X.sheaf.val.obj V) ↑X.functionField := m'
        let i : Algebra ↑(X.sheaf.val.obj U) ↑(X.sheaf.val.obj V) := (X.sheaf.val.map f).hom.toAlgebra
        simp [Scheme.ringCatSheaf] at m ⊢
        have : IsScalarTower ↑(X.sheaf.val.obj U) ↑(X.sheaf.val.obj V) ↑X.functionField := sorry
        exact algebra_compatible_smul (↑(X.sheaf.val.obj V)) m x
    }
  --map_id U hU := by cat_disch
  --map_comp := sorry


--variable (R : (TopologicalSpace.Opens X)ᵒᵖ ⥤ RingCat)
--#check PresheafOfModules R
--#check PresheafOfModulesNE R


/-
There seems to be some funny universe issue here, but I can't tell what it is.
-/
#check ModuleCat.of _ PUnit

set_option maxHeartbeats 0
open Classical in
noncomputable
def PresheafOfModules.mk' {X : Type*} [TopologicalSpace X]
    (R : (TopologicalSpace.Opens X)ᵒᵖ ⥤ RingCat) (F : PresheafOfModulesNE.{_, u, v} R) :
    PresheafOfModules R where
      obj U := (if _ : Nonempty U.unop then F.obj U else ModuleCat.of.{v, u} (R.obj U) PUnit)
      map {U} {V} f := by
        split_ifs
        · exact F.map f
        · exact ModuleCat.ofHom (Y := (ModuleCat.restrictScalars
                (RingCat.Hom.hom (R.map f))).obj
                (ModuleCat.of ↑(R.obj V) PUnit)) 0
        · rename_i hU hV
          have : (unop U).1 = ∅ := by exact Set.not_nonempty_iff_eq_empty'.mp hU
          have := CategoryTheory.leOfHom f.unop
          simp_all
          rw [this] at hV
          simp at hV
        · exact 𝟙 (ModuleCat.of (↑(R.obj U)) PUnit.{_ + 1})
      map_id U := by
        split_ifs
        · rename_i hU
          simp only [hU, F.map_id, ModuleCat.restrictScalarsId'_inv_app, eq_mpr_eq_cast,
            CategoryTheory.Functor.map_id, RingCat.hom_id, ↓reduceDIte, congrArg_cast_hom_right,
            eqToHom_iso_inv_naturality, congrArg_cast_hom_left, eqToHom_trans_assoc, eqToHom_refl,
            Category.id_comp]
        · rename_i hU
          have : Subsingleton
            ((if x : Nonempty ↥(unop U) then F.obj U else ModuleCat.of (↑(R.obj U))
            PUnit.{v + 1}) ⟶ (ModuleCat.restrictScalars (RingCat.Hom.hom (R.map (𝟙 U)))).obj
            (if x : Nonempty ↥(unop U) then F.obj U else
             ModuleCat.of (↑(R.obj U)) PUnit.{v + 1})) := by
              simp [hU]
              rw [@subsingleton_iff]
              exact fun _ _ ↦ eq_of_comp_right_eq fun {X_2} ↦ congrFun rfl

          apply Subsingleton.elim

      map_comp {U V W} f g := by
        split_ifs
        · rename_i hU
          by_cases hW : Nonempty W.unop
          · by_cases hV : Nonempty V.unop
            · simp [hU, hV, hW, F.map_comp, R.map_comp, Functor.map_comp]
              exact?
              ext a
              simp
              rw [@Functor.map_comp]



              sorry
            · simp [hU, hV, hW, F.map_comp, Functor.map_comp]
              sorry

            /-simp only [hW, eq_mpr_eq_cast, ↓reduceDIte, congrArg_cast_hom_left,
            Functor.map_dite, ModuleCat.restrictScalarsComp'_inv_app, Category.assoc]


            ext a
            simp [-nonempty_subtype, hW]-/
          · sorry


        · rename_i hU
          simp [hU]

          sorry
