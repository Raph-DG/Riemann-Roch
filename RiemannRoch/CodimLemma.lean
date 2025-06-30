import Mathlib
--import Batteries.Tactic.ShowUnused

open Filter Metric Real Set Topology

open AlgebraicGeometry
open LocallyRingedSpace
open CategoryTheory
open Opposite.op
open Module
open Order
open Ring
open TopologicalSpace

/-!
# Lemas about codimension

The goal of this file is to prove that the codimension of a point is equal to the krull dimension
of the stalk at that point.

To do this, we first show that the codimension of a point can be computed in any affine open set.
We then use that the codimension in an affine scheme is simply the height of the corresponding
prime ideal.

We then note that the points of Rp are just the primes of R with q ⊆ p, so the height of p computed
here is the same as the height computed in R. But the height of p in Rp is the krull dimension of
Rp, and so we're done.
-/

universe u v
variable (R : Type*)
         [CommRing R]
         (i : ℕ)
         {X Y : Scheme.{u}}


/-
We define a preorder instance on a scheme X saying x ≤ y if y generalises x. This ought to
correspond to x ≤ y ↔ closure {x} ⊆ closure {y},
-/
instance instanceSchemePreord {X : Scheme} : Preorder X := specializationPreorder X

namespace IrreducibleCloseds

/--
The map from irreducible closeds of an open subset to the whole space defined to be the
closure of the image under the associated open embedding.
-/
def openEmbeddingMap {U X : Type*} [TopologicalSpace X] [TopologicalSpace U]
  (f : U → X) (h : IsOpenEmbedding f) (h2 : Continuous f) :
  IrreducibleCloseds U → {V : IrreducibleCloseds X | f ⁻¹' V ≠ ∅} := by
  intro T
  have := closure (f '' T.1)
  refine ⟨⟨closure (f '' T.1), ?_ , ?_⟩, ?_⟩
  · apply IsIrreducible.closure

    apply IsIrreducible.image
    exact T.is_irreducible'
    exact Continuous.continuousOn h2
  · exact isClosed_closure
  · simp
    sorry

/--


TODO: clean up this proof
-/
lemma openEmbeddingMap_injective {U X : Type*} [TopologicalSpace X] [TopologicalSpace U]
  (f : U → X) (h : IsOpenEmbedding f) (h2 : Continuous f) :
  Function.Injective <| IrreducibleCloseds.openEmbeddingMap f h h2 := by
  intro V W hVW
  simp[IrreducibleCloseds.openEmbeddingMap] at hVW
  have lem (V : IrreducibleCloseds U) : f ⁻¹' (f '' V) = V := by
    apply Function.Injective.preimage_image
    have := h.1
    exact this.injective
  have : f ⁻¹' closure (f '' V) = f ⁻¹' closure (f '' W) := congrArg (preimage f) hVW

  rw[IsOpenMap.preimage_closure_eq_closure_preimage (IsOpenEmbedding.isOpenMap h) h2,
     IsOpenMap.preimage_closure_eq_closure_preimage (IsOpenEmbedding.isOpenMap h) h2] at this

  rw[lem, lem] at this
  have hV : closure V = V.1 := by
    apply IsClosed.closure_eq
    exact IrreducibleCloseds.isClosed V
  rw[hV] at this
  have hW : closure W = W.1 := by
    apply IsClosed.closure_eq
    exact IrreducibleCloseds.isClosed W
  rw[hW] at this
  exact IrreducibleCloseds.ext_iff.mpr this


lemma openEmbeddingMap_surjective {U X : Type*} [TopologicalSpace X] [TopologicalSpace U]
  (f : U → X) (h : IsOpenEmbedding f) (h2 : Continuous f) :
  Function.Surjective <| IrreducibleCloseds.openEmbeddingMap f h h2 := by
  intro V
  let preim : IrreducibleCloseds U := {
    carrier := f ⁻¹' V
    is_irreducible' := sorry
    is_closed' := sorry
  }
  use preim
  simp[IrreducibleCloseds.openEmbeddingMap , preim]
  ext x
  simp
  /-
  This should be the lemma we need
  -/
  #check subset_closure_inter_of_isPreirreducible_of_isOpen

  sorry

end IrreducibleCloseds

def _root_.IrreducibleCloseds.order_iso_embedding {U X : Type*} [TopologicalSpace X] [TopologicalSpace U]
  (f : U → X) (h : IsOpenEmbedding f) : {V : IrreducibleCloseds X | f ⁻¹' V ≠ ∅} ≃o IrreducibleCloseds U where
    toFun T := {
      carrier := f ⁻¹' T
      is_irreducible' := by
        have := T.1.2
        rw[IsIrreducible.eq_1]
        constructor
        · have := T.2
          simp only [ne_eq, mem_setOf_eq] at this
          exact nonempty_iff_ne_empty.mpr this
        · apply IsPreirreducible.preimage
          · exact IsIrreducible.isPreirreducible this
          · exact h
      is_closed' := by
        have := T.1.3
        apply IsClosed.preimage
        exact IsOpenEmbedding.continuous h
        exact this
    }
    invFun T := {
      val := {
        carrier := closure (f '' T)
        is_irreducible' := by
          have := T.2
          apply IsIrreducible.closure
          apply IsIrreducible.image this
          apply Continuous.continuousOn
          exact IsOpenEmbedding.continuous h
        is_closed' := by
          exact isClosed_closure
      }
      property := by
        simp
        suffices (f ⁻¹' closure (f '' ↑T)).Nonempty by exact nonempty_iff_ne_empty.mp this
        suffices (f ⁻¹' (f '' ↑T)).Nonempty by sorry
        suffices (f ⁻¹' (f '' univ)).Nonempty by sorry
        rw[Set.preimage_image_univ]
        sorry
    }
    left_inv := sorry
    right_inv := sorry
    map_rel_iff' := sorry

lemma slo {Y : Type*} [TopologicalSpace Y] {a : Y} {U : Set Y} (h : closure {a} ⊆ U) : a ∈ U := by
  rw[subset_def] at h
  specialize h a
  have : a ∈ closure {a} := by exact Specializes.mem_closure fun ⦃U⦄ a ↦ a
  specialize h this
  exact h


lemma _root_.Order.coheight_inter {Y : Type*} [TopologicalSpace Y] (T : IrreducibleCloseds Y)
   (U : TopologicalSpace.Opens Y)
  (h : T.1 ∩ U ≠ ∅) :
  coheight T = coheight (α := {K : IrreducibleCloseds Y // K.1 ∩ U ≠ ∅}) ⟨T, h⟩ := by sorry
#check OrderEmbedding

lemma _root_.Order.coheight_eq_of_order_embedding {α β : Type*} [Preorder α] [Preorder β]
  (f : α ↪o β) (a : α) (h : ∀ b ≥ f a, ∃ a', b = f a') : coheight a = coheight (f a) := by
    apply eq_of_le_of_le
    · apply Order.coheight_le_coheight_apply_of_strictMono
      exact OrderEmbedding.strictMono f
    · simp[coheight, height]
      --intro p hp
      --obtain ⟨a', ha'⟩ := h p.last hp
      intro p hp
      induction p using RelSeries.inductionOn generalizing a
      · simp_all
      · rename_i p x hx ih
        simp

        obtain ⟨a', ha'⟩ := h (p.cons x hx).last hp
        specialize ih a h


        sorry


@[stacks 02I4]
lemma _root_.AlgebraicGeometry.coheight_eq_embedding {U X : Scheme} {Z : U} (f : U ⟶ X)
  [k : IsOpenImmersion f] : Order.coheight (f.base Z) = Order.coheight Z := by

  rw[← Order.coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm (f.base Z)]
  rw[← Order.coheight_orderIso (irreducibleSetEquivPoints (α := U)).symm Z]

  let rest := Order.coheight_orderIso (IrreducibleCloseds.order_iso_embedding f.base k.base_open).symm

  specialize rest ((irreducibleSetEquivPoints (α := U)).symm Z)
  rw[← rest]

  let g : {V : IrreducibleCloseds X | ⇑(ConcreteCategory.hom f.base) ⁻¹' ↑V ≠ ∅}  ↪o IrreducibleCloseds X := {
    toFun V := V
    inj' := Subtype.val_injective
    map_rel_iff' := Iff.symm ge_iff_le
  }

  have := Order.coheight_eq_of_order_embedding g ⟨(irreducibleSetEquivPoints (α := X)).symm (f.base Z), sorry⟩ sorry
  simp[g] at this
  rw [← this]

  congr
  simp[IrreducibleCloseds.order_iso_embedding, irreducibleSetEquivPoints, OrderIso.symm]

  have : f.base '' closure {Z} = closure {f.base Z} := by

    have : IsOpenEmbedding f.base := sorry



    ext x
    constructor
    · rintro ⟨m, hm⟩
      simp_all
      rw[← hm.2]
      sorry
    · intro hx
      simp_all

      sorry
  rw[this]
  exact closure_closure.symm


@[stacks 02IZ]
lemma _root_.AlgebraicGeometry.stalk_dim_of_codim {X : Scheme} (Z : X) {d : ℕ}
  (hZ : Order.coheight Z = d) : ringKrullDim (X.presheaf.stalk Z) = d := by sorry
  /-have : ∃ W : X.Opens, IsAffineOpen W ∧ closure {Z} ⊆ W := by
    obtain ⟨R, f, hf⟩ := AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset
      (U := ⊤) (x := Z) (by aesop)
    have := hf.1
    let W : X.Opens := {
      carrier := Set.range (f.base)
      is_open' := AlgebraicGeometry.IsOpenImmersion.isOpen_range (H := hf.1) f
    }
    use W
    constructor
    · have : IsAffineOpen (⊤ : (Spec R).Opens) := isAffineOpen_top (Spec R)
      have := AlgebraicGeometry.IsAffineOpen.image_of_isOpenImmersion (X := Spec R) (U := ⊤) (H := hf.1) this f
      have rwl : f ''ᵁ ⊤ = W := by aesop
      rwa[rwl] at this
    · sorry
      --exact hf.2.1-/
  /-
  obtain ⟨R, f, hf⟩ := AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset
    (U := ⊤) (x := Z) (by aesop)




  --have hZ' : Z ∈ W := sorry
  rw[← coheight_eq_embedding ⟨W, hW.1⟩ (hW.2)] at hZ

  have := AlgebraicGeometry.IsAffineOpen.isLocalization_stalk hW.1 ⟨Z, hZ'⟩

  have := @IsLocalization.AtPrime.orderIsoOfPrime _ _ _ _ (X.presheaf.algebra_section_stalk ⟨Z, _⟩) _ _ this
  simp[ringKrullDim]



  have := Order.krullDim_eq_of_orderIso this
  rw[Order.krullDim_eq_of_orderIso <| PrimeSpectrum.equivSubtype (X.presheaf.stalk Z)]
  simp_all only



  let ip := irreducibleSetEquivPoints (α := W)
  let pc := OrderIso.trans ((OrderIso.dualDual ((IrreducibleCloseds (PrimeSpectrum Γ(X, W)))))) (OrderIso.dual <| PrimeSpectrum.pointsEquivIrreducibleCloseds Γ(X, W)).symm


  let ic := TopologicalSpace.IrreducibleCloseds.orderIsoSubtype (PrimeSpectrum ↑Γ(X, W))


  have := Order.coheight_orderIso ip.symm ⟨Z, slo hW.right⟩
  rw[← this] at hZ




  have := Order.coheight_orderIso pc.symm

  have := Order.coheight_orderIso pc.symm

  have := Order.coheight_orderIso ic
  sorry-/
