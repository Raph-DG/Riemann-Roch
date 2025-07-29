import Mathlib

open AlgebraicGeometry CategoryTheory Limits

universe w v v' v'' u u' u''

--variable {C : Type u} [Category.{v} C] (J : Type u') [Category.{v'} J]
  --(A : Type u'') [Category.{v''} A]

variable {R α : Type*} [Ring R] [AddRightCancelSemigroup α] [One α] {c : ComplexShape α}
   (C : HomologicalComplex (ModuleCat R) c) (j : α)

noncomputable
def negOnePow (i : α) : ℤˣ := open Classical in if Even i then 1 else -1

namespace HomologicalComplex

noncomputable
def eulerChar₁ : ℤ := finsum (fun i : α ↦ negOnePow i • Module.finrank R (C.X i))

noncomputable
def eulerChar₂ : ℤ := finsum (fun i : α ↦ negOnePow i • Module.finrank R (C.homology i))

/--
This needs assumptions:
  - R needs to be commutative?
  - All C.X i need to be projective of finite rank
  - Only finitely many C.X i can be nonzero
-/
theorem eulerChar₁_eq_eulerChar₂ : C.eulerChar₁ = C.eulerChar₂ := sorry

end HomologicalComplex
