import Mathlib

/-!
# IsFreeAbelian

Here we define a proposition `IsFreeAbelian` to say that a given abelian group is free. This is
implemented much like IsTensorProduct and IsSymmetricAlgebra, by saying that the lift of the
structure map from "the" free abelian group is bijective.

We then define a degree function, which is just the sum of all the coeffients.

Currently this definition is slightly annoying to use since we have to supply a map.
I think it would make more sense to say the condition implies finite support in the
case of a compact space.
-/

class IsFreeAbelian {α β : Type*} [AddCommGroup β] (ι : α → β) where
  bij : Function.Bijective (FreeAbelianGroup.lift ι)

lemma FreeAbelianGroup.IsFreeAbelian (α : Type*) : IsFreeAbelian (FreeAbelianGroup.of (α := α)) := sorry

namespace IsFreeAbelian

variable {α β : Type*} [AddCommGroup β] (ι : α → β) [h : IsFreeAbelian ι]

noncomputable def equiv : FreeAbelianGroup α ≃+ β :=
  AddEquiv.ofBijective _ (h.bij)

noncomputable
def degree (b : β) : ℤ :=
  let f := FreeAbelianGroup.toFinsupp <| h.equiv.symm.toAddHom b
  ∑ x ∈ f.support, f x


end IsFreeAbelian
