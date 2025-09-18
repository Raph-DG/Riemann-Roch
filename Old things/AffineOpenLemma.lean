import Mathlib

open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isAffineOpen_mem_and_subset {X : Scheme.{u}} {x : X}
    {U : X.Opens} (hxU : x ∈ U) : ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W.1 ⊆ U := by
  obtain ⟨R, f, hf⟩ := AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset hxU
  exact ⟨Scheme.Hom.opensRange f (H := hf.1),
    ⟨AlgebraicGeometry.isAffineOpen_opensRange f (H := hf.1), hf.2.1, hf.2.2⟩⟩
