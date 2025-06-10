import Mathlib
import RiemannRoch.OrderOfVanishing
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

universe u v
variable (R : Type*)
         [CommRing R]
         (i : ℕ)
         {X Y : Scheme.{u}}

instance instanceSchemePreord {X : Scheme} : Preorder X := specializationPreorder X


variable (f : X ⟶ Y)
         (x : X)
         (z : Y)


def nj {X : Type*} [TopologicalSpace X] (U : Set X) (h : IsOpen U) :
  {V : IrreducibleCloseds X | V.carrier ∩ U ≠ ∅} ≃o IrreducibleCloseds U where
    toFun T := {
      carrier := Subtype.val ⁻¹' (T.1.carrier)
      is_irreducible' := by
        have := T.1.2
        have : IsPreirreducible (X := U) (Subtype.val ⁻¹' (T.1.carrier)) := by
          apply IsPreirreducible.preimage
          · exact IsIrreducible.isPreirreducible this
          · exact IsOpen.isOpenEmbedding_subtypeVal h
        rw[IsIrreducible.eq_1]
        constructor
        · obtain ⟨T, hT⟩ := T
          simp at hT
          simp[Subtype.preimage_coe_nonempty]
          suffices U ∩ T.carrier ≠ ∅ by exact nonempty_iff_ne_empty.mpr this
          simp
          rw[inter_comm]
          exact hT
        · exact this
      is_closed' := by
        have := T.1.3
        exact IsClosed.preimage_val this
    }
    invFun T := {
      val := {
        carrier := closure (Subtype.val '' T.1)
        is_irreducible' := by
          have := T.2
          apply IsIrreducible.closure
          apply IsIrreducible.image this
          apply Continuous.continuousOn
          exact continuous_subtype_val
        is_closed' := by
          exact isClosed_closure
      }
      property := by
        simp
        suffices Subtype.val '' T.carrier ∩ U ≠ ∅ by
          rw[← nonempty_iff_ne_empty] at this
          have makelemma {s t : Set X} (h1 : s ⊆ t) (h2 : Nonempty s) : Nonempty t := by
            obtain ⟨g, hg⟩ := h2
            use g
            exact h1 hg
          have h1 : Subtype.val '' T.carrier ∩ U ⊆ closure (Subtype.val '' T.carrier) ∩ U := by
            apply inter_subset_inter
            · exact subset_closure
            · rfl
          specialize makelemma h1
          sorry


                    /-suffices Subtype.val '' T.carrier ⊆ closure (Subtype.val '' T.carrier)
            by exact inter_subset_inter this fun ⦃a⦄ a ↦ a
          exact subset_closure-/

        rw[Set.image_val_inter_self_left_eq_coe]
        have : T.carrier.Nonempty := by
          apply IsIrreducible.nonempty
          exact T.2
        suffices (Subtype.val '' (T.carrier)).Nonempty by exact nonempty_iff_ne_empty.mp this
        exact Set.Nonempty.image _ this
    }
    left_inv :=

      sorry
    right_inv := sorry
    map_rel_iff' := sorry


@[stacks 02I4]
lemma fifi {X : Scheme} {Z : X} (U : X.affineOpens) (hU : Z ∈ U.1) :
  Order.height (α := U) ⟨Z, hU⟩ = Order.height Z := by sorry

/-
  The idea of this proof is that codim(Y, X) = codim(Y ∩ U, U) (stacks 02I4). So, we can replace
  Z by an affine open neighbourhood. Then, we know that any irreducible closed subset of U = Spec R
  (i.e. a prime ideal of R) passing through Z corresponds to a prime ideal of Rₚ. So, the codimension
  of Z must be the same as the dimension of Rₚ, which shows our result.
  -/

/-
Here we're just relating the two notions of height we have. Note that p ⊆ q ↔ p ⤳ q,
so this statement should essentially just be true by definition.
-/
def specializes_iff_ideal_le {X : Scheme} [IsAffine X] (p : X) :
  Ideal.primeHeight (IsAffineOpen.primeIdealOf (U := ⊤) (AlgebraicGeometry.isAffineOpen_top X) ⟨p, trivial⟩).1 = Order.height p := by
  have (q r : X) : p ⤳ r ↔ IsAffineOpen.primeIdealOf (U := ⊤) (AlgebraicGeometry.isAffineOpen_top X) ⟨q, trivial⟩ ≤ IsAffineOpen.primeIdealOf (U := ⊤) (AlgebraicGeometry.isAffineOpen_top X) ⟨r, trivial⟩ := sorry

  /-
  simp[Ideal.primeHeight, Order.height]
  unfold LE.le
  unfold Preorder.toLE
  simp[instanceSchemePreord, specializationPreorder, PartialOrder.toPreorder]-/

  sorry


@[stacks 02IZ]
lemma ringKrullDim_of_height {X : Scheme} (Z : X) {d : ℕ} (hZ : Order.height Z = d) : ringKrullDim (X.presheaf.stalk Z) = d := by
  have : ∃ W : X.Opens, IsAffineOpen W ∧ Z ∈ W := by
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
    · exact hf.2.1

  obtain ⟨W, hW⟩ := this
  rw[← fifi ⟨W, hW.1⟩ (hW.2)] at hZ

  have := AlgebraicGeometry.IsAffineOpen.isLocalization_stalk hW.1 ⟨Z, hW.2⟩

  have := @IsLocalization.AtPrime.orderIsoOfPrime _ _ _ _ (X.presheaf.algebra_section_stalk ⟨Z, _⟩) _ _ this
  simp[ringKrullDim]

  --#check IsLocalization.AtPrime.orderIsoOfPrime (X.presheaf.stalk Z) ((hW.left.primeIdealOf ⟨Z, hW.right⟩).asIdeal) --((hW.left.primeIdealOf ⟨Z, hW.right⟩).asIdeal.primeCompl) ((X.presheaf.stalk Z))
  have := Order.krullDim_eq_of_orderIso this

  /-
  We now want to say that the points of this local ring correspond to the primes contained in
  primeIdealOf Z. Surely this has to exist somewhere.
  -/

  sorry

instance {X : Scheme} [IsLocallyNoetherian X] {Z : X} : IsNoetherianRing (X.presheaf.stalk Z) := by
  have : ∃ U : X.affineOpens, Z ∈ U.1 := sorry
  obtain ⟨U, hU⟩ := this
  have := AlgebraicGeometry.IsAffineOpen.isLocalization_stalk U.2 ⟨Z, hU⟩
  apply @IsLocalization.isNoetherianRing _ _ (U.2.primeIdealOf ⟨Z, hU⟩).asIdeal.primeCompl (X.presheaf.stalk Z) _ (X.presheaf.algebra_section_stalk ⟨Z, hU⟩) this
  exact IsLocallyNoetherian.component_noetherian U


instance {X : Scheme} [IsIntegral X] {Z : X} : IsDomain (X.presheaf.stalk Z) :=
  Function.Injective.isDomain _ (IsFractionRing.injective (X.presheaf.stalk Z) (X.functionField))

/-
Note in this case that the height being 1 is the right condition, because namely this means that
the difference between the dimension function on X (which exists because X is integral and so has
a generic point) and the dimension function at Z is 1. So this is equivalent to the dimension of Z
being the dimension of X - 1.
-/
open Multiplicative
noncomputable
def _root_.AlgebraicGeometry.Scheme.ord {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  (Z : X) (hZ : Order.height Z = 1) : X.functionField →*₀ ℤₘ₀ :=
  have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk Z) := by
    rw[Ring.krullDimLE_iff, ringKrullDim_of_height Z hZ]
  Ring.ordFrac (X.presheaf.stalk Z)
