import Mathilb

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
