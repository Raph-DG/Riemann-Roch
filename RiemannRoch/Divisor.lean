import Mathlib
import RiemannRoch.CodimLemma
import RiemannRoch.AlgebraicCycle

/-!
# Weil Divisors

In this file we define the notion of Weil divisors and construct the sheaf 𝒪(D), defining it on U
to be rational functions such that (f) + D ≥ 0 on U.

This definition gives good results on Noetherian, integral separated schemes which are regular in
codimension 1. Since our main goal is proving Riemann Roch for curves this should be enough power
for us, but we should in the future extend these results.
-/


open AlgebraicGeometry

open CategoryTheory
open Opposite.op
open Order
open AlgebraicCycle
open Opposite

universe u v
variable (R : Type*)
         [CommRing R]
         (i : ℕ)
         {X Y : Scheme.{u}}
         [IsIntegral X]
         [IsLocallyNoetherian X]

def AlgebraicGeometry.Scheme.dimension (X : Scheme.{u}) : ℕ∞ := sorry

/--
This is a slightly nonstandard definition of what it means to be catenary, and it is
mainly stated here because we will need this assumption to show that principal divisors
(defined with respect to the coheight) are indeed divisors (i.e. cycles of dimension n-1).
-/
class Catenary (X : Scheme.{u}) where
  dimension_coheight (x : X) : coheight x = X.dimension - height x

/--
Below we define the sheaf 𝒪(D) associated with a Weil divisor. We note that strictly speaking you
don't need the input cycle to be a divisor, so in this definition we just assume D is an arbitrary
cycle.
-/
def AlgebraicCycle.lineBundle (D : AlgebraicCycle X) (U : X.Opens) :=
  WithZero {s : (X.functionField)ˣ | Function.locallyFinsuppWithin.restrict (V := U) ((div s (by simp)) + D) (by simp) ≥ 0 }

instance (D : AlgebraicCycle X) (U : X.Opens) : AddCommGroup (D.lineBundle U) where
  add f g := by sorry
  add_assoc := sorry
  zero := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
  neg := sorry
  sub_eq_add_neg := sorry
  zsmul := sorry
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  neg_add_cancel := sorry
  add_comm := sorry

instance (D : AlgebraicCycle X) (U : X.Opens) :
         Module (X.sheaf.val.obj (op U)) (D.lineBundle U) := sorry

def AlgebraicCycle.lineBundleSheaf (D : AlgebraicCycle X) :
  SheafOfModules ((sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf) where
    val := {
      obj U := by
        simp
        sorry
        --exact ModuleCat.of (X.sheaf.val.obj U) (D.rationalSections (Opposite.unop U))
      map := sorry
      map_id := sorry
      map_comp := sorry
    }
    isSheaf := sorry
/-
TODO: This currently takes in an algebraic cycle as the input argument, but really
should take in a Weil divisor. Or, at the very least, we should make it so this notation
accepts Weil divisors without having to put .1.

Of course, we can just write $D.1 here, I'm not sure if I like this or not.
-/
macro:max "𝒪(" D:term ")": term =>
  `(AlgebraicCycle.lineBundleSheaf $D)

def WeilDivisor (X : Scheme.{u}) := HomogeneousAddSubgroup X (X.dimension - 1)


variable [Catenary X]
