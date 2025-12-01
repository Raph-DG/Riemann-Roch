import Mathlib

open AlgebraicGeometry

universe u

variable (X : Scheme.{u}) [IsIntegral X]

/--
This is a lemma I think we'll need at some point, but I don't think it belongs in the first PR
-/
theorem eq_mul_of_stalk_eq_mul (z : X) (U : X.Opens) (h : z ∈ U) (f g u : Γ(X, U)) [Nonempty U]
    (hfg :
      let _ : Algebra ↑Γ(X, U) ↑(X.presheaf.stalk z) := (X.presheaf.germ U z h).hom.toAlgebra
      @algebraMap Γ(X, U) (X.presheaf.stalk z) _ _ (X.presheaf.germ U z h).hom.toAlgebra f =
          (u • (@algebraMap Γ(X, U) (X.presheaf.stalk z) _ _
          (X.presheaf.germ U z h).hom.toAlgebra g) : X.presheaf.stalk z))
    : f = u * g := by
  let alg : Algebra ↑Γ(X, U) ↑(X.presheaf.stalk z) :=
        (X.presheaf.germ U z h).hom.toAlgebra
  have : u • algebraMap (Γ(X, U)) (X.presheaf.stalk z) g =
    algebraMap (Γ(X, U)) (X.presheaf.stalk z) u *
    algebraMap (Γ(X, U)) (X.presheaf.stalk z) g := rfl
  simp_rw [this] at hfg
  have : algebraMap (Γ(X, U)) (X.presheaf.stalk z) u *
    algebraMap (Γ(X, U)) (X.presheaf.stalk z) g =
    algebraMap (Γ(X, U)) (X.presheaf.stalk z) (u * g) := by exact Eq.symm (algebraMap.coe_mul u g)
  rw[this] at hfg
  have : Function.Injective (algebraMap ↑Γ(X, U) ↑(X.presheaf.stalk z)) :=
    AlgebraicGeometry.germ_injective_of_isIntegral X z h
  exact this hfg


/-
The above lemma tells us that two regular functions on U whose stalks at a point are differ by u
must differ by u globally.

We really
-/


/-
From this point, we now have something resembling the sheaf of rational functions on an integral
scheme. For the talk, we need to demonsrate that it is worthwhile developing this less general
thing for the sake of language (i.e. show some real examples where people implicitly assume the
sheaf of rational functions has this form once they know something is integral, then show how
it's easy to work with with all the infrastructure we develop).
-/
















---------------------------------------------------------------------------------------------



/-
Below is an attempt to do something similar without explicitly using the
ofPresheaf constructor for Presheaves of modules.

As far as I can tell, this seems to produce the same hellish proof states that
we were getting before
-/











/-




variable {X : TopCat} (M : TopCat.PresheafNE Ab X)
    {R : (TopologicalSpace.Opens ↑X)ᵒᵖ ⥤ RingCat}
    [(U : (TopologicalSpace.Opens ↑X)ᵒᵖ) → [Nonempty ↥(U.unop)] → Module ↑(R.obj U) ↑(M.objNE U)]
    (map_smul : ∀ ⦃U V : (TopologicalSpace.Opens ↑X)ᵒᵖ⦄ [Nonempty ↥(U.unop)] [Nonempty ↥(V.unop)]
     (f : U ⟶ V) (r : ↑(R.obj U)) (m : ↑(M.objNE U)),
      (ConcreteCategory.hom (M.mapNE f)) (r • m) =
        (ConcreteCategory.hom (R.map f)) r • (ConcreteCategory.hom (M.mapNE f)) m)



open Classical in
noncomputable
def ofPresheafNEobj (U : (TopologicalSpace.Opens ↑X)ᵒᵖ) : ModuleCat ↑(R.obj U) :=
  if _ : Nonempty ↥(U.unop) then ModuleCat.of _ (M.objNE U) else ModuleCat.of (R.obj U) PUnit

def ofPresheafNEMapNE {U V : (TopologicalSpace.Opens ↑X)ᵒᵖ}
    [hU : Nonempty ↥(U.unop)] [hV : Nonempty ↥(V.unop)] (f : U ⟶ V) :
    ofPresheafNEobj M U ⟶ (ModuleCat.restrictScalars (R.map f).hom).obj (ofPresheafNEobj M V) := by
  simp only [ofPresheafNEobj, hU, hV, ↓reduceDIte]
  exact ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (RingCat.Hom.hom (R.map f))).obj
    (ModuleCat.of ↑(R.obj V) ↑(M.objNE V)))
    {
      toFun x := M.mapNE f x
      map_add' := by simp
      map_smul' := fun r m ↦ map_smul f r m
    }

#check PresheafOfModules.ofPresheaf
def ofPresheafNEMapNE_id {U : (TopologicalSpace.Opens ↑X)ᵒᵖ} [hU : Nonempty ↥(U.unop)] :
    ofPresheafNEMapNE M map_smul (𝟙 U) =
    (ModuleCat.restrictScalarsId' (R.map (𝟙 U)).hom
    (congrArg RingCat.Hom.hom (R.map_id U))).inv.app _ := by
  --#check M.mapNE_id
  simp [ofPresheafNEMapNE, M.mapNE_id]



  --ext

  --refine ModuleCat.hom_ext ?_

  /-
  I have absolutely no idea what to do with this
  -/



  sorry


open Classical in
noncomputable
def ofPresheafNEMapLeft {U V : (TopologicalSpace.Opens ↑X)ᵒᵖ}
    [hU : Nonempty ↥(U.unop)] (hV : ¬ Nonempty ↥(V.unop)) (f : U ⟶ V) :
    ofPresheafNEobj M U ⟶ (ModuleCat.restrictScalars (R.map f).hom).obj (ofPresheafNEobj M V) := by
  simp only [ofPresheafNEobj, hU, hV, ↓reduceDIte]
  exact 0


noncomputable
def ofPresheafNEMapRight {U V : (TopologicalSpace.Opens ↑X)ᵒᵖ}
    (hU : ¬ Nonempty ↥(U.unop)) [hV : Nonempty ↥(V.unop)] (f : U ⟶ V) :
    ofPresheafNEobj M U ⟶ (ModuleCat.restrictScalars (R.map f).hom).obj (ofPresheafNEobj M V) := by
  simp only [ofPresheafNEobj, hU, hV, ↓reduceDIte]
  exact 0


noncomputable
def ofPresheafNEMapEmpty {U V : (TopologicalSpace.Opens ↑X)ᵒᵖ}
    (hU : ¬ Nonempty ↥(U.unop)) (hV : ¬ Nonempty ↥(V.unop)) (f : U ⟶ V) :
    ofPresheafNEobj M U ⟶ (ModuleCat.restrictScalars (R.map f).hom).obj (ofPresheafNEobj M V) := by
  simp only [ofPresheafNEobj, hU, hV, ↓reduceDIte]
  exact 0

#check PresheafOfModules.ofPresheaf
open Classical in
noncomputable def ofPresheafNE : PresheafOfModules R := sorry
  --refine PresheafOfModules.ofPresheaf
  --· sorry
  --· sorry

  /-obj U := if _ : Nonempty ↥(U.unop) then ModuleCat.of _ (M.objNE U) else ModuleCat.of (R.obj U) PUnit
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  map {U V} f := by
    split_ifs
    · apply ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (RingCat.Hom.hom (R.map f))).obj (ModuleCat.of ↑(R.obj V) ↑(M.objNE V)))
      exact {
        toFun x := M.mapNE f x
        map_add' := by simp
        map_smul' := fun r m ↦ map_smul f r m
      }
    · exact 0
    · exact 0
    · exact 0
  map_id := by
    intro U
    split_ifs

    · rename_i h
      have := M.mapNE_id U
      --simp [M.mapNE_id U]

      sorry
    · sorry
  map_comp := sorry

  /-ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.map f).hom).obj (ModuleCat.of _ (M.objNE V)))
    { toFun := fun x ↦ M.map f x
      map_add' := by simp
      map_smul' := fun r m ↦ map_smul f r m }-/-/
#check PresheafOfModules.ofPresheaf-/






open Scheme
lemma secondMapFun_surjective (U : X.Opens)
    (ϖ : X.presheaf.stalk P) (hϖ : Irreducible ϖ) (hP' : coheight P = 1) (o : P ∈ U) :
    ∀ z ∈ U, ∃ (V : X.Opens) (_ : V ≤ U) (_ : z ∈ V), 
    --IsLocallySurjective <| secondMapFun h' D P U ϖ hϖ hP' o := by
  have : Nonempty ↥(unop (op U)) := by use P
  intro y
  by_cases h : y = 0
  · simp [h]
    use 0
    /-
    This holds by being a module homomorphism which we haven't shown yet.
    -/
    sorry
  simp [skyscraperAb, skyscraperSheaf, skyscraperPresheaf, o] at y
  have : y ≠ 0 := sorry

  obtain ⟨x, hx⟩ := residue_surjective X P y
  have : IsDiscreteValuationRing ↑(X.presheaf.stalk P) := sorry
  have : x ≠ 0 := sorry

  obtain ⟨n, u, hun⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible this hϖ
  let ans : ↑((lineBundle h' D).val.obj (op U)) := {
    val := sectionNE
      ((algebraMap ↑(X.presheaf.stalk P) ↑X.functionField) ↑u * (algebraMap ↑(X.presheaf.stalk P)
       ↑X.functionField) ϖ ^ (n - D P)) U

    property := by
      simp [LinearLocalPredicate.submodule, LinearLocalPredicateNE.lineBundleProp,
      LinearLocalPredicateNE.toLinearLocalPredicate, LinearLocalPredicateNE.lineBundleP]
      intro x hx hs
      simp_all
      intro z
      by_cases zin : z ∈ U
      · simp [restrict_apply, zin]
        by_cases zch : coheight z = 1
        · simp [div_eq_ord_of_coheight_eq_one _ _ z zch]
          /-
          Hmm, if z = P, then this will work

          However, otherwise we really have no idea. So this really is only locally surjective.
          What a time to be alive.
          -/
          #check ord
          --suffices (ord z zch) ((algebraMap ↑(X.presheaf.stalk P) ↑X.functionField) ↑u) * (ord z zch) ((algebraMap ↑(X.presheaf.stalk P) ↑X.functionField) ϖ) ^ (↑n - D P) 
          sorry

        · simp [div_eq_zero_of_coheight_ne_one _  _ z zch]
          /-
          Amazingly, we actually need here that outside codimension 1, D z ≥ 0, the
          first time we have needed any conditions outside codimension 1.
          -/
          sorry
      · simp [zin]

  

  /-
  Proof: X.residue is surjective by some lemma in the library already.

  So, take x in the residue field and l a section of X.residue over x. Then l can be represented
  as u ϖ^n for n ≥ 0 by a library lemma. Then we claim u * ϖ (n - D P) will map to the right thing
  and this should be provable without too much effort.
  -/
  sorry



/-
The stalk of a sheaf of `𝒪ₓ` modules at `p` is a module over the stalk `𝒪ₓ` at `p`.
-/
/-
While this stuff is worthwhile to have eventually, it it just not useful for us yet. 

instance instModuleSheafOfModulesStalk {X : Scheme.{u}} (F : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk F.val.presheaf x).carrier := by
  unfold TopCat.Presheaf.stalk
  unfold TopCat.Presheaf.stalkFunctor
  simp
  let test (U : (TopologicalSpace.Opens X)ᵒᵖ) : Module (X.presheaf.obj U) (F.val.obj U) := by infer_instance



  sorry-/

/-noncomputable
def moduleStalk {X : Scheme.{u}} (F : X.Modules) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  .of (X.presheaf.stalk x) (TopCat.Presheaf.stalk F.val.presheaf x).carrier

noncomputable
def SheafOfModules.fiber {X : Scheme.{u}} (F : X.Modules) (x : X) : ModuleCat (X.residueField x) :=
  (ModuleCat.extendScalars (X.residue x).hom).obj (moduleStalk F x)-/