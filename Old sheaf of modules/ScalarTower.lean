import Mathlib

open AlgebraicGeometry CategoryTheory Opposite

universe u

variable (X : Scheme.{u})
  {U V : (TopologicalSpace.Opens ↥X)ᵒᵖ} (r : U ⟶ V)

instance k : Algebra Γ(X, U.unop) Γ(X, V.unop) :=
    (X.ringCatSheaf.val.map r).hom.toAlgebra

/-
This is really god awful, there has to be a better way...
-/
instance [IsIntegral X] [hU : Nonempty U.unop] [hV : Nonempty V.unop] :
    let k' := k X r
    IsScalarTower Γ(X, U.unop) Γ(X, V.unop) X.functionField := by
  let k' := k X r
  let aU : Algebra Γ(X, U.unop) X.functionField :=
    instAlgebraCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensFunctionFieldOfNonemptyToScheme
      X (Opposite.unop U)
  let aV : Algebra Γ(X, V.unop) X.functionField := instAlgebraCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensFunctionFieldOfNonemptyToScheme
      X (Opposite.unop V)
  apply IsScalarTower.of_algebraMap_eq'
  simp_rw [RingHom.algebraMap_toAlgebra]
  change _ = (X.sheaf.val.map r ≫ _).hom
  have ans := TopCat.Presheaf.germ_res X.sheaf.val (unop r)
    (genericPoint X) (((genericPoint_spec X).mem_open_set_iff V.unop.2).mpr
    (by simpa using hV))
  rw[CommRingCat.hom_ext_iff] at ans
  convert ans
  · exact CommRingCat.Hom.ext (id (Eq.symm ans))
  · exact CommRingCat.Hom.ext ans


--variable [Nonempty U.unop] [Nonempty V.unop]
--#synth IsScalarTower Γ(X, U.unop) Γ(X, V.unop) X.functionField
