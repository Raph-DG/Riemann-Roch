import Mathlib

/-!

# Domain of definition of an element of the function field

In this file we define the notion of the domain of definition of an element of
the function field of an integral scheme. Namely, given `f : X.functionField` for
`X : Scheme` with `[IsIntegral X]`, the domain of definition `U` is defined to be
the largest set on which "`f ∈ Γ(X, U)`". By `f ∈ Γ(X, U)`, we mean there exists a
section `f' ∈ Γ(X, U)` such that `germToFunctionField f' = f`.
-/

open AlgebraicGeometry Scheme

universe u

variable {X : Scheme.{u}} [IsIntegral X] (f : X.functionField)

#check AlgebraicGeometry.Scheme.RationalMap.ofFunctionField
#check AlgebraicGeometry.Scheme.RationalMap.fromFunctionField
/-
Right, so I think this is replicating work a little bit, because we already have rational maps.
So probably the correct thing to do here is to define the correspondance between elements of the
function field and rational maps to `P¹`.
-/
def domainOfDefinition (f : X.functionField) : X.Opens :=
    sSup {V : X.Opens | ∃ (_ : Nonempty V) (g : Γ(X, V)), X.germToFunctionField V g = f}

structure isDefined (f : X.functionField) (U : X.Opens) where
  ne : Nonempty U
  ex : ∃ f' : Γ(X, U), germToFunctionField X U f' = f

lemma domainOfDefinition_spec (f : X.functionField) :
    Maximal (isDefined f) (domainOfDefinition f) := sorry

lemma domainOfDefinition_mul (f g : X.functionField) :
    domainOfDefinition (f * g) = domainOfDefinition f ⊓ domainOfDefinition g := sorry
