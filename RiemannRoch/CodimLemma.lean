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
  (f : U → X) (h : Continuous f) :
  IrreducibleCloseds U → {V : IrreducibleCloseds X | f ⁻¹' V ≠ ∅} := by
  intro T
  refine ⟨⟨closure (f '' T.1), IsIrreducible.closure <|
           IsIrreducible.image T.is_irreducible' f (Continuous.continuousOn h),
           isClosed_closure⟩, ?_⟩
  · suffices (closure T.1).Nonempty from nonempty_iff_ne_empty.mp
      (Nonempty.mono (closure_subset_preimage_closure_image h (s := T)) this)
    exact closure_nonempty_iff.mpr T.2.nonempty

lemma openEmbeddingMap_injective {U X : Type*} [TopologicalSpace X] [TopologicalSpace U]
    (f : U → X) (h : IsOpenEmbedding f) (h2 : Continuous f) :
    Function.Injective <| IrreducibleCloseds.openEmbeddingMap f h2 := by
  intro V W hVW
  simp only [ne_eq, coe_setOf, openEmbeddingMap, mem_setOf_eq, Subtype.mk.injEq,
    IrreducibleCloseds.mk.injEq] at hVW
  have : f ⁻¹' closure (f '' V) = f ⁻¹' closure (f '' W) := congrArg (preimage f) hVW
  simp only [h.isOpenMap.preimage_closure_eq_closure_preimage h2,
       Function.Injective.preimage_image h.1.injective _,
       V.isClosed.closure_eq, W.isClosed.closure_eq] at this
  exact IrreducibleCloseds.ext_iff.mpr this


lemma openEmbeddingMap_surjective {U X : Type*} [TopologicalSpace X] [TopologicalSpace U]
    (f : U → X) (h : IsOpenEmbedding f) (h2 : Continuous f) :
    Function.Surjective <| IrreducibleCloseds.openEmbeddingMap f h2 := by
  intro V
  let preim : IrreducibleCloseds U := {
    carrier := f ⁻¹' V
    is_irreducible' := ⟨nonempty_iff_ne_empty.mpr V.2,
      IsPreirreducible.preimage (IsIrreducible.isPreirreducible V.1.2) h⟩
    is_closed' := V.1.3.preimage h2
  }
  use preim
  simp only [ne_eq, coe_setOf, openEmbeddingMap, mem_setOf_eq, preim]
  have : (V.1.1 ∩ range f).Nonempty := by
    have := V.2
    dsimp at this
    rw[← Set.preimage_inter_range] at this
    have : (f ⁻¹' (↑↑V ∩ range f)).Nonempty := nonempty_iff_ne_empty.mpr this
    exact Set.nonempty_of_nonempty_preimage this
  have lem := subset_closure_inter_of_isPreirreducible_of_isOpen (S := V.1.1) (U := range f)
    (IsIrreducible.isPreirreducible V.1.2) (h.isOpen_range) this
  apply eq_of_le_of_le
  · suffices closure (f '' (f ⁻¹' ↑↑V)) ⊆ V from this
    suffices f '' (f ⁻¹' ↑↑V) ⊆ V by
      exact (IsClosed.closure_subset_iff (IrreducibleCloseds.isClosed V.1)).mpr this
    exact image_preimage_subset f ↑↑V
  · suffices V.1.1 ⊆ closure (f '' (f ⁻¹' V.1.1)) from this
    convert lem
    exact image_preimage_eq_inter_range

lemma openEmbeddingMap_bijective {U X : Type*} [TopologicalSpace X] [TopologicalSpace U]
  (f : U → X) (h : IsOpenEmbedding f) (h2 : Continuous f) :
  Function.Bijective <| IrreducibleCloseds.openEmbeddingMap f h2 :=
  ⟨openEmbeddingMap_injective f h h2, openEmbeddingMap_surjective f h h2⟩

lemma openEmbeddingMap_mono {U X : Type*} [TopologicalSpace X] [TopologicalSpace U]
  (f : U → X) (h2 : Continuous f) :
  Monotone <| IrreducibleCloseds.openEmbeddingMap f h2 := fun _ _ s ↦ closure_mono (image_mono s)

lemma openEmbeddingMap_strictMono {U X : Type*} [TopologicalSpace X] [TopologicalSpace U]
  (f : U → X) (h : IsOpenEmbedding f) (h2 : Continuous f) :
  StrictMono <| IrreducibleCloseds.openEmbeddingMap f h2 := Monotone.strictMono_of_injective
   (openEmbeddingMap_mono f h2) (openEmbeddingMap_injective f h h2)

noncomputable
def order_iso_embedding {U X : Type*} [TopologicalSpace X] [TopologicalSpace U]
  (f : U → X) (h1 : IsOpenEmbedding f) (h2 : Continuous f) :
  IrreducibleCloseds U ≃o {V : IrreducibleCloseds X | f ⁻¹' V ≠ ∅} := by
  refine ⟨Equiv.ofBijective (openEmbeddingMap f h2) (openEmbeddingMap_bijective f h1 h2), ?_⟩
  have := openEmbeddingMap_mono f h2 -- What's going on here?
  refine fun a b ↦ ⟨fun h ↦ ?_, fun a_1 ↦ this a_1⟩
  · have eq : f ⁻¹' closure (f '' a.carrier) ≤ f ⁻¹' closure (f '' b.carrier) := fun _ b ↦ h b
    have (c : IrreducibleCloseds U) : c.carrier = f ⁻¹' (closure (f '' c.carrier)) := by
      suffices closure c.carrier = f ⁻¹' (closure (f '' c.carrier)) by
        nth_rewrite 1 [← IsClosed.closure_eq c.3]
        exact this
      apply Topology.IsEmbedding.closure_eq_preimage_closure_image h1.isEmbedding c
    rwa [← this a, ← this b] at eq

lemma _root_.Order.coheight_eq_of_order_embedding {α β : Type*} [Preorder α] [Preorder β]
    (f : α ↪o β) (a : α) (h : ∀ p : LTSeries β, p.head = f a → ∃ p' : LTSeries α, p'.head = a ∧
    p = p'.map f (OrderEmbedding.strictMono f)) : coheight a = coheight (f a) := by
    apply eq_of_le_of_le <|
      Order.coheight_le_coheight_apply_of_strictMono _ (OrderEmbedding.strictMono f) _
    refine coheight_le_iff'.mpr (fun p hp ↦ ?_)
    choose p' hp' using (h p hp)
    exact hp'.2 ▸ LTSeries.map_length p' f (OrderEmbedding.strictMono f) ▸
          (Order.coheight_eq_iSup_head_eq a) ▸
          (ciSup_pos hp'.1 : (⨆ (_ : RelSeries.head p' = a), p'.length : ℕ∞) = p'.length) ▸
          le_iSup (α := ℕ∞) (fun p ↦ ⨆ (_ : RelSeries.head p = a), p.length) p'


@[stacks 02I4]
lemma _root_.AlgebraicGeometry.coheight_eq_embedding {U X : Scheme} {Z : U} (f : U ⟶ X)
  [k : IsOpenImmersion f] : Order.coheight (f.base Z) = Order.coheight Z := by

  rw[← Order.coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm (f.base Z),
     ← Order.coheight_orderIso (irreducibleSetEquivPoints (α := U)).symm Z,
     ← Order.coheight_orderIso
    (IrreducibleCloseds.order_iso_embedding f.base k.base_open (Scheme.Hom.continuous f))
    ((irreducibleSetEquivPoints (α := U)).symm Z)]

  let g : {V : IrreducibleCloseds X | ⇑(ConcreteCategory.hom f.base) ⁻¹' ↑V ≠ ∅} ↪o
      IrreducibleCloseds X := {
    toFun V := V
    inj' := Subtype.val_injective
    map_rel_iff' := Iff.symm ge_iff_le
  }

  let a := (order_iso_embedding f.base k.base_open (Scheme.Hom.continuous f))
      (irreducibleSetEquivPoints.symm Z)

  have : ∀ p : LTSeries (IrreducibleCloseds X), p.head = g a →
         ∃ p' : LTSeries ({V : IrreducibleCloseds X | ⇑(ConcreteCategory.hom f.base) ⁻¹' ↑V ≠ ∅}),
           p'.head = a ∧ p = p'.map g (OrderEmbedding.strictMono g) := fun p hp ↦ by
    let p' : LTSeries {V : IrreducibleCloseds X | ⇑(ConcreteCategory.hom f.base) ⁻¹' ↑V ≠ ∅} := {
      length := p.length
      toFun i := {
        val := p i
        property := by
          suffices  ¬⇑(ConcreteCategory.hom f.base) ⁻¹' a = ∅ by
            rw[← Ne, ← nonempty_iff_ne_empty] at this
            exact nonempty_iff_ne_empty.mp <|
              Nonempty.mono (fun _ b ↦ (hp ▸ LTSeries.head_le p i) b) this
          exact a.2
      }
      step := p.step
    }
    exact ⟨p', SetCoe.ext hp, rfl⟩
  have := coheight_eq_of_order_embedding g
     ((order_iso_embedding f.base k.base_open (Scheme.Hom.continuous f))
     (irreducibleSetEquivPoints.symm Z)) this
  convert this.symm
  simp only [irreducibleSetEquivPoints, ne_eq, coe_setOf, mem_setOf_eq, order_iso_embedding,
    RelIso.coe_fn_mk, Equiv.ofBijective_apply, openEmbeddingMap]
  suffices closure {f.base Z} = closure ((f.base) '' (closure {Z})) from
    IrreducibleCloseds.ext_iff.mpr this
  simp [closure_image_closure (Scheme.Hom.continuous f)]

@[stacks 02IZ]
lemma _root_.AlgebraicGeometry.stalk_dim_of_codim {X : Scheme} (Z : X) :
  ringKrullDim (X.presheaf.stalk Z) = Order.coheight Z := by

  obtain ⟨R, f, hf⟩ := AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset
    (U := ⊤) (x := Z) (by aesop)
  obtain ⟨y, hy⟩ := Set.mem_range.mp hf.2.1

  have := hf.1
  have := hy ▸ coheight_eq_embedding f (Z := y)

  rw[this]
  suffices ringKrullDim ((Spec R).presheaf.stalk y) = coheight y from
    this ▸ Order.krullDim_eq_of_orderIso
    (hy ▸ PrimeSpectrum.comapEquiv (asIso (Scheme.Hom.stalkMap f y)).commRingCatIsoToRingEquiv)

  let k : Algebra ↑R ↑((Spec R).presheaf.stalk y) := StructureSheaf.stalkAlgebra (↑R) y
  have : IsLocalization.AtPrime (↑((Spec R).presheaf.stalk y)) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R y

  rw [IsLocalization.AtPrime.ringKrullDim_eq_height y.asIdeal ((Spec R).presheaf.stalk y),
     Ideal.height_eq_primeHeight y.asIdeal, Ideal.primeHeight]
  apply WithBot.coe_eq_coe.mpr
  congr
  ext
  simp only [PrimeSpectrum.instPartialOrder, PartialOrder.lift, PrimeSpectrum.le_iff_specializes,
    OrderDual.instPreorder, OrderDual.instLE, instanceSchemePreord, specializationPreorder]
