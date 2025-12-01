import Mathlib

universe u

open AlgebraicGeometry Opposite

variable {X : Scheme.{u}}

namespace RationalSheaf

def S (U : X.Opens) : Submonoid Γ(X, U) where
  carrier := {s | ∀ x : X, (hx : x ∈ U) → X.presheaf.germ U x hx s ∈ nonZeroDivisors _}
  mul_mem' := sorry
  one_mem' := sorry


lemma ne_zero_iff_germ_ne_zero [IsIntegral X] {U : X.Opens} [hU : Nonempty U] (s : Γ(X, U)) :
    s ≠ 0 ↔ ∀ {x : X} (hx : x ∈ U), X.presheaf.germ U x hx s ≠ 0 := by
  constructor
  · intro h x hx
    have := AlgebraicGeometry.germ_injective_of_isIntegral X x hx
    exact
      (map_ne_zero_iff (CategoryTheory.ConcreteCategory.hom (X.presheaf.germ U x hx)) this).mpr h
  · intro h seq0
    rw [seq0] at h
    obtain ⟨x, hx⟩ := hU
    specialize h hx
    aesop

open CategoryTheory

noncomputable
def map {U V : X.Opens} (k : V ≤ U) : Localization (S U) →+* Localization (S V) := by
  apply IsLocalization.map (T := S V) (Localization (S V)) (X.presheaf.map (homOfLE k).op).hom (M := S U)
  intro x hx y hy
  rw[TopCat.Presheaf.germ_res_apply]
  exact hx y (k hy)


lemma locMap_integral_iso [IsIntegral X] (U V : X.Opens) [Nonempty U] : Function.Bijective <| map (by simp : V ⊓ U ≤ U) := by
  have : (V ⊓ U).1.Nonempty ↔ V.1.Nonempty := by
    /-
    Follows from X being integral
    -/
    sorry

  /-

  -/

  simp [map]

  sorry



lemma S_integral [IsIntegral X] (U : X.Opens) [Nonempty U] : S U = nonZeroDivisors Γ(X, U) := by
  have : (S U).carrier = {s | ∀ x : X, (hx : x ∈ U) → X.presheaf.germ U x hx s ≠ 0} := by

    sorry

  suffices (S U).carrier = (nonZeroDivisors ↑Γ(X, U)).carrier by
    ext a
    exact Eq.to_iff (congrFun this a)
  rw [this]
  ext a
  simp

  sorry

noncomputable
def K : TopCat.Presheaf CommRingCat X where
  obj U := .of <| Localization <| S (unop U)
  map {U V} k := CommRingCat.ofHom <| map (leOfHom k.unop)
  map_id := sorry
  map_comp := sorry


noncomputable
def KSheaf := CategoryTheory.GrothendieckTopology.sheafify (Opens.grothendieckTopology X) K

#check PresheafOfModules.ofPresheaf

instance (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) :
    Module ↑(X.ringCatSheaf.val.obj U) ↑((KSheaf ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat Ab).obj U) := sorry

noncomputable
def KMod : PresheafOfModules X.ringCatSheaf.val := by
  apply PresheafOfModules.ofPresheaf <| KSheaf ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat Ab

  sorry


noncomputable
def 𝒦 : SheafOfModules X.ringCatSheaf where
  val := KMod
  isSheaf :=
    /-
    This follows from KMod being a sheaf
    -/
    sorry


section Integral

variable [IsIntegral X]

def functionFieldToK (U : X.Opens) : X.functionField →+* Localization (S U) := by
  suffices ∀ V : X.Opens, (genericPoint X) ∈ V → Γ(X, V) → Localization (S U) by sorry

  sorry

def functionFieldToSheaf (U : X.Opens) : X.functionField → 𝒦.val.obj (op U) := sorry -- functionFieldToK U ≫ 

/--
The map from `X.functionField` to `𝒦(U)` is surjective
-/
lemma functionFieldToSheaf_surjective (U : X.Opens) :
    Function.Surjective <| functionFieldToSheaf U := sorry

lemma functionFieldToSheaf_injective_of_nonempty (U : X.Opens) [Nonempty U] :
    Function.Injective <| functionFieldToSheaf U := sorry

end Integral


end RationalSheaf
