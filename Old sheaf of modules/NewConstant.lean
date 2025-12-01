import Mathlib

open CategoryTheory AlgebraicGeometry

variable (X : Scheme) [IsIntegral X]

/-
As much as I think this more abstract definition is nice, there is essentially nothing developed
for constant sheaves, so I think it's going to be annoying to work with this.
-/
noncomputable
def ratSheaf : TopCat.Sheaf Ab X := (constantSheaf (Opens.grothendieckTopology X) Ab).obj
    (.of X.functionField)




--#check (constantSheaf (Opens.grothendieckTopology X) Ab).obj (.of X.functionField)
