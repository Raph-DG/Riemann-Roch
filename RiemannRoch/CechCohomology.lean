import Mathlib

open AlgebraicGeometry CategoryTheory
/-!
# Cech cohomology

In this file we define a skeleton of the lemmas we need about Cech cohomology.
Since this is currently being developed by Kenny Lau, we're mainly treating this
as a black box for the time being.

As such, this will be the least developed of the files for some time, and we will
only update thsi file as we need lemmas or definitions in the statement and proof of
Riemann-Roch.
-/

namespace CechCohomology

/--
A stand in for the Euler characteristic of a sheaf F on a space, defined as:
χ(F) = ∑ (i : ℕ), (-1)^i h^i(X, F).

This is currently just a black box that produces an integer given a sheaf F. Currently it's
definitely at the wronng level of generality.
-/
def χ {X : Scheme}
  (F : SheafOfModules ((sheafCompose (Opens.grothendieckTopology ↥X)
  (forget₂ CommRingCat RingCat)).obj X.sheaf))
  : ℤ := sorry


--def χ {Y : TopCat} (F : TopCat.Presheaf AddCommGrp Y) : ℤ := sorry

end CechCohomology
