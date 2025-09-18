import Mathlib
import RiemannRoch.Misc.AffineOpenLemma

universe u

open AlgebraicGeometry

variable {X : Scheme.{u}}

instance [IsIntegral X] {x : X} : IsDomain (X.presheaf.stalk x) :=
  Function.Injective.isDomain _ (IsFractionRing.injective (X.presheaf.stalk x) (X.functionField))

instance [IsLocallyNoetherian X] {x : X} : IsNoetherianRing (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hU2, hU3⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by aesop)
  have := AlgebraicGeometry.IsAffineOpen.isLocalization_stalk hU ⟨x, hU2⟩
  exact @IsLocalization.isNoetherianRing _ _ (hU.primeIdealOf ⟨x, hU2⟩).asIdeal.primeCompl
        (X.presheaf.stalk x) _ (X.presheaf.algebra_section_stalk ⟨x, hU2⟩)
        this (IsLocallyNoetherian.component_noetherian ⟨U, hU⟩)
