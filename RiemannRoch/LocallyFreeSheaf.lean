import Mathlib

open AlgebraicGeometry
universe u


--class IsLocallyFree {X }

-- M.over (X i) ≅ (X i).

/-
class IsInvertibleSheaf {X : Scheme.{u}} (F : SheafOfModules X.ringCatSheaf) : Prop where
  trivialises : ∃ 𝒰 : X.OpenCover, ∀ j : 𝒰.J, F.over (Set.range (𝒰.map j))  -/


/-
We should define a locally free sheaf as a quasicoherent sheaf whose 'relations' field is trivial for
all the presentations in the `QuasicoherentData` structure.
Then we probably want to also define `FiniteLocallyFree` or something as something having
finitely many `generators`. We will also define invertible sheaves in a similar way

Then I guess we should battle test this definition by trying to prove things about invertible sheaves,
I think we probably want to:
  · Show how to produce a divisor from a section of an invertible sheaf
  · Show that different sections pro

-/
