import Mathlib

open AlgebraicGeometry Opposite CategoryTheory

universe u v w z

variable (X : Scheme.{w})
theorem div_smul_div_comm {G K : Type*}
    [Group G] [Field K] [DistribMulAction G K] [IsScalarTower G K K]
    (g h : G) (a b : K) (hb : b ≠ 0) :
    (g / h) • (a / b) = (g • a) / (h • b) := by
  rw [eq_div_iff_mul_eq (ne_of_apply_ne (h⁻¹ • ·) (by simpa)), smul_mul_smul_comm]
  simp [hb]

#find_home div_smul_div_comm
structure PresheafOfModulesNE {X : Type*} [TopologicalSpace X]
    (R : (TopologicalSpace.Opens X)ᵒᵖ ⥤ RingCat.{u}) where
  obj (U : (TopologicalSpace.Opens X)ᵒᵖ) [Nonempty ↥(U.unop)] : ModuleCat.{v} (R.obj U)
  map {U V : (TopologicalSpace.Opens X)ᵒᵖ} [Nonempty ↥U.unop] [Nonempty ↥V.unop]
      (f : U ⟶ V) : obj U ⟶ (ModuleCat.restrictScalars (R.map f).hom).obj (obj V)
  map_id (U : (TopologicalSpace.Opens X)ᵒᵖ) [Nonempty ↥U.unop] :
    map (𝟙 U) = (ModuleCat.restrictScalarsId' (R.map (𝟙 U)).hom
      (congrArg RingCat.Hom.hom (R.map_id U))).inv.app _ := by
        cat_disch
  map_comp {U V W : (TopologicalSpace.Opens X)ᵒᵖ} [Nonempty ↥U.unop]
    [Nonempty ↥V.unop] [Nonempty ↥W.unop] (f : U ⟶ V) (g : V ⟶ W) :
    map (f ≫ g) = map f ≫ (ModuleCat.restrictScalars _).map (map g) ≫
      (ModuleCat.restrictScalarsComp' (R.map f).hom (R.map g).hom (R.map (f ≫ g)).hom
        (congrArg RingCat.Hom.hom <| R.map_comp f g)).inv.app _ := by cat_disch


set_option maxHeartbeats 0
--set_option synthInstance.maxHeartbeats 0
open Classical in
/--
Alternate construction of a presheaf of modules which allows one to only define the action of the
sheaf on nonempty sets
-/
noncomputable
def PresheafOfModules.mk' {X : Type*} [TopologicalSpace X]
    (R : (TopologicalSpace.Opens X)ᵒᵖ ⥤ RingCat) (F : PresheafOfModulesNE R) :
    PresheafOfModules R where
      obj U := (if _ : Nonempty U.unop then F.obj U else ModuleCat.of (R.obj U) PUnit)
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
        · exact 𝟙 (ModuleCat.of (↑(R.obj U)) PUnit)
      map_id U := by
        split_ifs
        · rename_i hU
          simp only [hU, F.map_id, ModuleCat.restrictScalarsId'_inv_app, eq_mpr_eq_cast,
            CategoryTheory.Functor.map_id, RingCat.hom_id, ↓reduceDIte, congrArg_cast_hom_right,
            eqToHom_iso_inv_naturality, congrArg_cast_hom_left, eqToHom_trans_assoc, eqToHom_refl,
            Category.id_comp]
        · rename_i hU
          refine Subsingleton.elim (h := ?_) _ _
          simp [hU]
          rw [@subsingleton_iff]
          exact fun _ _ ↦ eq_of_comp_right_eq fun {X_2} ↦ congrFun rfl
          /-have : Subsingleton
            ((if x : Nonempty ↥(unop U) then F.obj U else ModuleCat.of (↑(R.obj U))
            PUnit) ⟶ (ModuleCat.restrictScalars (RingCat.Hom.hom (R.map (𝟙 U)))).obj
            (if x : Nonempty ↥(unop U) then F.obj U else
             ModuleCat.of (↑(R.obj U)) PUnit)) := by
              simp [hU]
              rw [@subsingleton_iff]
              exact fun _ _ ↦ eq_of_comp_right_eq fun {X_2} ↦ congrFun rfl-/

          --apply Subsingleton.elim

      map_comp {U V W} f g := by
        split_ifs
        · rename_i hU
          by_cases hV : Nonempty ↥(unop V)
          · by_cases hW : Nonempty ↥(unop W)
            · --ext a
              simp [hU, hV, hW, R.map_comp, PresheafOfModulesNE.map_comp,
               ↓reduceDIte, eqToHom_iso_inv_naturality]
              rw [@eqToHom_comp_iff]
              rw [@eqToHom_trans_assoc]
              ext a
              simp [hU, hV, hW]
              --cat_disch

              --simp_rw [CategoryTheory.Functor.congr_hom_assoc]
              --simp [hU, hV, hW]

              --rw [← CategoryTheory.eqToHom_trans_assoc]


              #check eqToHom_trans_assoc
              #check eqToHom
              /-
              This should be essentially solved from here, but these category theory proofs are
              impossible to read.

              The goal seems to say that (F.map g (F.map f a)) = F.map g (F.map f a), which is
              obviously true, but everything is wrapped in these stupid eqToHoms which make
              things impossible to reason about.
              -/

              sorry


            · simp [hU, hV, hW]
              refine Subsingleton.elim (h := ?_) _ _
              simp [hU, hW]
              rw [@subsingleton_iff]
              exact fun x y ↦ eq_of_comp_right_eq fun {X_2} ↦ congrFun rfl

          · have hW : ¬ Nonempty ↥(unop W) := sorry
            simp [hU, hV, hW]
            refine Subsingleton.elim (h := ?_) _ _
            simp [hU, hW]
            rw [@subsingleton_iff]
            exact fun x y ↦ eq_of_comp_right_eq fun {X_2} ↦ congrFun rfl

        · rename_i hU
          have hV : ¬Nonempty ↥(unop V) := by
            have := le_of_op_hom f
            simp_all
            intro x hx
            have := this hx
            specialize hU x
            exact hU this
          have hW : ¬Nonempty ↥(unop W) := sorry
          simp [hU, hV, hW]
          refine Subsingleton.elim (h := ?_) _ _
          simp [hU, hW]
          rw [@subsingleton_iff]
          exact fun x y ↦ eq_of_comp_right_eq fun {X_2} ↦ congrFun rfl
