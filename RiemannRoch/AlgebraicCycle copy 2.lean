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



class TopologicalSpace.isDimensionFunction {Z : Type*} [TopologicalSpace Z] (δ : Z → ℤ) where
  increase : ∀ x y : Z, x ⤳ y ∧ x ≠ y → δ (x) > δ (y)
  step : ∀ x y : Z, @CovBy Z (specializationPreorder Z).toLT x y → δ x = δ y + 1

structure dimensionFunction (Z : Type*) [TopologicalSpace Z] where
  δ : Z → ℤ
  dimFun : isDimensionFunction δ


def TopologicalSpace.toIrreducibleSubClosed {Z : Type*} [TopologicalSpace Z]
  (T T' : TopologicalSpace.IrreducibleCloseds Z) (h : T.carrier ⊆ T'.carrier) :
    TopologicalSpace.IrreducibleCloseds T' where
      carrier := fun z ↦ T.carrier z
      is_irreducible' := by
        have := T.2
        sorry
      is_closed' := sorry

/-
We should take this definition of the induced subspace of T' out of this definition and make it
into its own thing.

In fact, it will probably be useful to have some more stuff about codimension
-/
class TopologicalSpace.Catenary (Z : Type*) [TopologicalSpace Z] : Prop where
  catenary : ∀ T T' : TopologicalSpace.IrreducibleCloseds Z, (o : T.carrier ⊂ T'.carrier) →
    Order.coheight (α := TopologicalSpace.IrreducibleCloseds T') (TopologicalSpace.toIrreducibleSubClosed T T' o.le) ≠ ⊤

@[stacks 02J8]
class AlgebraicGeometry.UniversallyCatenary (S : Scheme) [IsLocallyNoetherian S] where
    universal {X : Scheme} (f : X ⟶ S) [LocallyOfFiniteType f] : Catenary X

/--
Canonically defined dimnension function on a scheme of finite type over
a universally catenary scheme with a dimension function δ.
-/
def AlgebraicGeometry.ioio {S X : Scheme} [IsLocallyNoetherian S] [UniversallyCatenary S]
  (δ : dimensionFunction S) (f : X ⟶ S) [LocallyOfFiniteType f] : dimensionFunction X := sorry

--@[stacks 02JW]

namespace DimensionFunction




end DimensionFunction
/-
We define a preorder instance on a scheme X saying x ≤ y if y generalises x. This ought to
correspond to x ≤ y ↔ closure {x} ⊆ closure {y},
-/
instance instanceSchemePreord {X : Scheme} : Preorder X := specializationPreorder X

/--
An algebraic cycle on a scheme X is defined to be a function from X to
ℤ with locally finite support.
-/
abbrev AlgebraicCycle (X : Scheme) := Function.locallyFinsuppWithin (⊤ : Set X) ℤ

namespace AlgebraicCycle

variable (f : X ⟶ Y)
         (c : AlgebraicCycle X)
         (x : X)
         (z : Y)


/--
The cycle containing a single point with a chosen coefficient
-/
noncomputable
def single (coeff : ℤ) : AlgebraicCycle X where
  toFun := Set.indicator {x} (Function.const X coeff)
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' := by
    intro z hz
    use ⊤
    constructor
    · exact Filter.univ_mem' fun a ↦ trivial
    · rw[← Function.const_def]
      simp only [top_eq_univ, support_indicator, univ_inter]
      exact toFinite ({x} ∩ Function.support fun x ↦ coeff)

/--
Implementation detail for the pushforward; the support of a cycle on X intersected with the preimage
of a point z : Y along a morphism f : X ⟶ Y.
-/
def preimageSupport : Set X :=
  f.base ⁻¹' {z} ∩ c.support

/--
Implementation detail for the pushforward; the support of a cycle on X intersected with the preimage
of a point z : Y along a quasicompact morphism f : X ⟶ Y is finite.
-/
def preimageSupportFinite [qf : QuasiCompact f] :
 (preimageSupport f c z).Finite := by
  have cpct : IsCompact (f.base ⁻¹' {z}) := QuasiCompact.isCompact_preimage_singleton f z
  rw[isCompact_iff_finite_subcover] at cpct

  let cov : f.base ⁻¹' {z} → Set X := by
    intro x
    choose U hU using c.supportLocallyFiniteWithinDomain' x (by simp)
    exact U

  have covSpec (x : f.base ⁻¹' {z}) : cov x ∈ 𝓝 ↑x ∧ (cov x ∩ Function.support c.toFun).Finite :=
    Classical.choose_spec (c.supportLocallyFiniteWithinDomain' (↑x) (of_eq_true (by simp)))

  let openCov : f.base ⁻¹' {z} → Set X := by
    intro x
    have cs := (covSpec x).1
    rw[_root_.mem_nhds_iff] at cs
    choose U hU using cs
    exact U

  have openCovSpec (x : f.base ⁻¹' {z}) : openCov x ⊆ cov x ∧
      IsOpen (openCov x) ∧ ↑x ∈ (openCov x) := by
    simp_all [Classical.choose_spec (Eq.mp (congrArg (fun _a ↦ _a)
              (propext _root_.mem_nhds_iff)) ((covSpec x).1)),
              top_eq_univ, and_self, cov, openCov]

  have covOpen (x : f.base ⁻¹' {z}) : IsOpen (openCov x) := (openCovSpec x).2.1

  have covCovs : f.base ⁻¹' {z} ⊆ ⋃ i, openCov i := by
    rw[subset_def]
    intro x hx
    have := (openCovSpec ⟨x, hx⟩).2.2
    exact mem_iUnion_of_mem ⟨x, hx⟩ this

  specialize cpct openCov covOpen covCovs

  choose V hV using cpct

  simp only [preimageSupport, Function.locallyFinsuppWithin.support]

  have openCovSpec' : ∀ x : f.base ⁻¹' {z}, (openCov x ∩ Function.support c.toFun).Finite := by
    intro x
    have cs2 := (covSpec x).2
    have ocs1 := (openCovSpec x).1
    have : openCov x ∩ Function.support c.toFun ⊆ cov x ∩ Function.support c.toFun := by
      exact inter_subset_inter ocs1 fun ⦃a⦄ a ↦ a
    (expose_names; exact Finite.subset cs2 this)

  have VSpec : ∀ x ∈ V, (openCov x ∩ Function.support c.toFun).Finite := fun x a ↦ openCovSpec' x

  have m : (⋃ x ∈ V, (openCov x ∩ Function.support c.toFun)).Finite := by
    have : ∀ (i : { x // x ∈ V }), Finite ↑((fun x ↦ openCov ↑x ∩ Function.support c.toFun) i) :=
      fun i ↦ openCovSpec' ↑i
    have := Set.finite_iUnion (ι := V) (f := fun x => openCov x ∩ Function.support c.toFun) this
    simp at this
    rwa[Eq.symm (iUnion_subtype (Membership.mem V) fun x ↦ openCov ↑x ∩ Function.support c.toFun)]


  have : (f.base ⁻¹' {z} ∩ Function.support c) ⊆ (⋃ x ∈ V, openCov x ∩ Function.support c) := by
    rw[Eq.symm (iUnion₂_inter (fun i j ↦ openCov i) (Function.support ⇑c))]
    apply inter_subset_inter _ (fun ⦃a⦄ a ↦ a)
    exact hV

  exact Finite.subset m this

open Classical in
/--
The degree of a morphism f : X ⟶ Y at a point x : X is defined to be the rank of the field extension
of the residue field of x over the residue field of (f x).

Note that this degree is finite if (and only if?) the dimensions of x and f x correspond.
-/
noncomputable
def _root_.AlgebraicGeometry.LocallyRingedSpace.Hom.degree : ℕ := @Module.finrank
    (IsLocalRing.ResidueField (Y.presheaf.stalk (f.base x)))
    (IsLocalRing.ResidueField (X.presheaf.stalk x))
    (by infer_instance)
    (by infer_instance)
    (by have := RingHom.toAlgebra (IsLocalRing.ResidueField.map (f.stalkMap x).hom); exact Algebra.toModule)


open Classical in
/--
Implementation detail for pushforward.

IF THE CONJECTURED "ONLY IF" IN THE ABOVE STATEMENT HOLDS, THEN THIS DEFINITION IS PRECISELY THE
SAME AS DEGREE WITH AN UNECESSARY CASE DISTINCTION ADDED IN
-/
noncomputable
def mapAux {Y : Scheme} (δₓ : X → ℤ) [TopologicalSpace.isDimensionFunction δₓ]
  (δₐy : Y → ℤ) [TopologicalSpace.isDimensionFunction δₐy] (f : X ⟶ Y) (x : X) : ℤ :=
  if δₓ x = δₐy (f.base x) then Hom.degree f x else 0

lemma map_locally_finite {Y : Scheme} (δₓ : X → ℤ) [TopologicalSpace.isDimensionFunction δₓ] (δy : Y → ℤ) [TopologicalSpace.isDimensionFunction δy]
  (f : X ⟶ Y) [qc : QuasiCompact f] (c : AlgebraicCycle X) :
  ∀ z ∈ (⊤ : Set Y), ∃ t ∈ 𝓝 z, (t ∩ Function.support fun z ↦
  ∑ x ∈ (preimageSupportFinite f c z).toFinset, (c x) * mapAux δₓ δy f x).Finite := by
  intro y hy
  have : ∃ W : Y.Opens, IsAffineOpen W ∧ y ∈ W := by

    obtain ⟨R, f, hf⟩ := AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset
      (U := ⊤) (x := y) (by aesop)
    have := hf.1
    let W : Y.Opens := {
      carrier := Set.range (f.base)
      is_open' := AlgebraicGeometry.IsOpenImmersion.isOpen_range (H := hf.1) f
    }
    use W
    constructor
    · have : IsAffineOpen (⊤ : (Spec R).Opens) := by exact isAffineOpen_top (Spec R)
      have := AlgebraicGeometry.IsAffineOpen.image_of_isOpenImmersion (X := Spec R) (U := ⊤) (H := hf.1) this f
      have rwl : f ''ᵁ ⊤ = W := by aesop
      rwa[rwl] at this
    · exact hf.2.1

  obtain ⟨W, hW⟩ := this
  have affineCompact : IsCompact W.carrier := AlgebraicGeometry.IsAffineOpen.isCompact hW.1
  use W
  constructor
  · refine IsOpen.mem_nhds ?_ ?_
    · exact Opens.isOpen W
    · exact hW.2
  · have cpct : IsCompact (f.base ⁻¹' W) := qc.1 W.carrier W.is_open' affineCompact

    rw[isCompact_iff_finite_subcover] at cpct

    let cov : f.base ⁻¹' W → Set X := by
      intro x
      choose U hU using c.supportLocallyFiniteWithinDomain' x (by simp)
      exact U

    have covSpec : ∀ x : f.base ⁻¹' W, cov x ∈ 𝓝 ↑x ∧ (cov x ∩ Function.support c.toFun).Finite := by
      intro x
      exact Classical.choose_spec (c.supportLocallyFiniteWithinDomain' (↑x) (of_eq_true (by simp)))

    let openCov : f.base ⁻¹' W → Set X := by
      intro x
      have cs := (covSpec x).1
      rw[_root_.mem_nhds_iff] at cs
      choose U hU using cs
      exact U

    have openCovSpec : ∀ x : f.base ⁻¹' W, openCov x ⊆ cov x ∧ IsOpen (openCov x) ∧ ↑x ∈ (openCov x) := by
      intro x
      have := Classical.choose_spec (Eq.mp (congrArg (fun _a ↦ _a) (propext _root_.mem_nhds_iff)) ((covSpec x).1))
      aesop

    have covOpen : ∀ x : f.base ⁻¹' W, IsOpen (openCov x) := by
      intro x
      specialize openCovSpec x
      exact openCovSpec.2.1

    have covCovs : f.base ⁻¹' W ⊆ ⋃ i, openCov i := by
      rw[subset_def]
      intro x hx
      have := (openCovSpec ⟨x, hx⟩).2.2
      exact mem_iUnion_of_mem ⟨x, hx⟩ this

    specialize cpct openCov covOpen covCovs

    choose V hV using cpct

    have openCovSpec' : ∀ x : f.base ⁻¹' W, (openCov x ∩ Function.support c.toFun).Finite := by
      intro x
      have cs2 := (covSpec x).2
      have ocs1 := (openCovSpec x).1
      have : openCov x ∩ Function.support c.toFun ⊆ cov x ∩ Function.support c.toFun := by
        exact inter_subset_inter ocs1 fun ⦃a⦄ a ↦ a
      (expose_names; exact Finite.subset cs2 this)

    have VSpec : ∀ x ∈ V, (openCov x ∩ Function.support c.toFun).Finite := fun x a ↦ openCovSpec' x

    have : (⋃ x ∈ V, (openCov x ∩ Function.support c.toFun)).Finite := by
      have : ∀ (i : { x // x ∈ V }), Finite ↑((fun x ↦ openCov ↑x ∩ Function.support c.toFun) i) := by
        exact fun i ↦ openCovSpec' ↑i
      have := Set.finite_iUnion (ι := V) (f := fun x => openCov x ∩ Function.support c.toFun) this
      have obv : (⋃ x ∈ V, openCov x ∩ Function.support c.toFun) = (⋃ i : V, openCov ↑i ∩ Function.support c.toFun) := by
        exact
          Eq.symm (iUnion_subtype (Membership.mem V) fun x ↦ openCov ↑x ∩ Function.support c.toFun)
      rw[obv]
      exact this

    have : (f.base ⁻¹' W ∩ Function.support c) ⊆ (⋃ x ∈ V, openCov x ∩ Function.support c) := by
      have : (⋃ x ∈ V, openCov x ∩ Function.support c) = ((⋃ x ∈ V, openCov x) ∩ Function.support c) := by
        exact Eq.symm (iUnion₂_inter (fun i j ↦ openCov i) (Function.support ⇑c))
      rw[this]
      suffices f.base ⁻¹' W ⊆ ⋃ x ∈ V, openCov x by exact inter_subset_inter hV fun ⦃a⦄ a ↦ a
      exact hV

    have pbfinite : (f.base ⁻¹' W ∩ Function.support c).Finite := by
      (expose_names; exact Finite.subset this_1 this)

    suffices (W.carrier ∩ {z : Y | (preimageSupport f c z).Nonempty}).Finite by
      apply Finite.subset this
      apply inter_subset_inter Set.Subset.rfl
      intro x
      simp
      contrapose!
      intro aux
      rw [Finset.sum_eq_zero]
      intro x hx
      simp only [Finite.mem_toFinset, aux] at hx
      simp only [mem_empty_iff_false] at hx

    have : W.carrier ∩ {z | (preimageSupport f c z).Nonempty} ⊆ f.base '' (f.base ⁻¹' ((W.carrier ∩ {z | (preimageSupport f c z).Nonempty})) ∩ c.support) := by
      intro a ha
      rw [@image_preimage_inter]
      suffices a ∈ f.base '' c.support by
        exact mem_inter ha this
      have := ha.2.some_mem
      simp[preimageSupport] at this
      simp
      use ha.2.some
      constructor
      · exact this.2
      · exact this.1

    apply Finite.subset _ this
    apply Finite.image
    rw[preimage_inter]
    have : f.base ⁻¹' W.carrier ∩ f.base ⁻¹' {z | (preimageSupport f c z).Nonempty} ∩ c.support ⊆ f.base ⁻¹' W.carrier ∩ (⋃ z : Y, preimageSupport f c z) := by
      intro p hp
      simp[preimageSupport] at hp ⊢
      constructor
      · exact hp.1.1
      · exact hp.2

    apply Finite.subset _ this
    rw[inter_iUnion]
    simp[preimageSupport]
    suffices (⋃ i : Y, f.base ⁻¹' W.carrier ∩ c.support).Finite by
      apply Finite.subset this
      simp
      intro y x hx
      simp at hx ⊢
      constructor
      · exact hx.1
      · constructor
        · exact Nonempty.intro y
        · exact hx.2.2

    suffices (f.base ⁻¹' W.carrier ∩ c.support).Finite by
      apply Finite.subset this
      intro a ha
      simp at ha ⊢
      constructor
      · exact ha.1
      · exact ha.2.2
    exact pbfinite


open Classical in
noncomputable
def map {Y : Scheme} (δₓ : X → ℤ) [TopologicalSpace.isDimensionFunction δₓ] (δy : Y → ℤ) [TopologicalSpace.isDimensionFunction δy]
  (f : X ⟶ Y) [qc : QuasiCompact f] (c : AlgebraicCycle X) : AlgebraicCycle Y where
  toFun z := (∑ x ∈ (preimageSupportFinite f c z).toFinset, (c x) * mapAux δₓ δy f x)
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' := fun z a ↦ map_locally_finite δₓ δy f c z a

@[simp]
lemma map_id (δₓ : X → ℤ) [TopologicalSpace.isDimensionFunction δₓ] (c : AlgebraicCycle X) :
    map δₓ δₓ (𝟙 X) c = c := by
   ext z
   have : (c z ≠ 0 ∧ (preimageSupportFinite (𝟙 X) c z).toFinset = {z}) ∨
          (c z = 0 ∧ (preimageSupportFinite (𝟙 X) c z).toFinset = ∅) := by
    simp[preimageSupportFinite, preimageSupport, Finite.toFinset]
    by_cases o : c z = 0
    · exact Or.inr o
    · apply Or.inl
      refine ⟨o, ?_⟩
      ext a
      simp
      intro h
      rw[h]
      exact o
   suffices (map δₓ δₓ (𝟙 X) c).toFun z = c.toFun z by exact this
   obtain h | h := this
   · simp[map, mapAux]
     rw[h.2]
     simp[Hom.degree]
     rfl
   · simp[map, mapAux]
     rw[h.2]
     simp[Hom.degree]
     exact h.1.symm


def _root_.IrreducibleCloseds.order_iso_restriction {X : Type*} [TopologicalSpace X] (U : Set X)
  (h : IsOpen U) : {V : IrreducibleCloseds X | V.carrier ∩ U ≠ ∅} ≃o IrreducibleCloseds U where
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
          have := Set.Nonempty.coe_sort this
          specialize makelemma h1 this
          exact nonempty_iff_ne_empty'.mp makelemma
        rw[Set.image_val_inter_self_left_eq_coe]
        have : T.carrier.Nonempty := by
          apply IsIrreducible.nonempty
          exact T.2
        suffices (Subtype.val '' (T.carrier)).Nonempty by exact nonempty_iff_ne_empty.mp this
        exact Set.Nonempty.image _ this
    }
    left_inv := by
      simp[Function.LeftInverse]
      intro T hT

      suffices closure (U ∩ T.carrier) = T by exact IrreducibleCloseds.ext_iff.mpr this
      have := T.2

      #check IsPreirreducible.subset_irreducible
      /-
      We need to use the fact that X is irreducible here
      -/
      sorry
    right_inv := sorry
    map_rel_iff' := sorry


@[stacks 02I4]
lemma _root_.AlgebraicGeometry.height_eq_restrict {X : Scheme} {Z : X} (U : X.affineOpens) (hZ : Z ∈ U.1) :
  Order.height (α := U) ⟨Z, hZ⟩ = Order.height Z := by
  have h1 := (irreducibleSetEquivPoints (α := X)).symm
  --rw[← Order.height_orderIso h1 Z]
  have s : (h1 Z).1 ⊆ U := sorry


  have := (IrreducibleCloseds.order_iso_restriction U.1.1 U.1.2).symm
  have := Order.height_orderIso this sorry
  --#check Z
  --#check Order.height_orderIso (IrreducibleCloseds.order_iso_restriction U.1.1 U.1.2) ⟨Z, hZ⟩
  sorry

/-
  The idea of this proof is that codim(Y, X) = codim(Y ∩ U, U) (stacks 02I4). So, we can replace
  Z by an affine open neighbourhood. Then, we know that any irreducible closed subset of U = Spec R
  (i.e. a prime ideal of R) passing through Z corresponds to a prime ideal of Rₚ. So, the codimension
  of Z must be the same as the dimension of Rₚ, which shows our result.
  -/


@[stacks 02IZ]
lemma _root_.AlgebraicGeometry.stalk_dim_of_codim {X : Scheme} (Z : X) {d : ℕ}
  (hZ : Order.height Z = d) : ringKrullDim (X.presheaf.stalk Z) = d := by
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
  rw[← _root_.AlgebraicGeometry.height_eq_restrict ⟨W, hW.1⟩ (hW.2)] at hZ

  have := AlgebraicGeometry.IsAffineOpen.isLocalization_stalk hW.1 ⟨Z, hW.2⟩

  have := @IsLocalization.AtPrime.orderIsoOfPrime _ _ _ _ (X.presheaf.algebra_section_stalk ⟨Z, _⟩) _ _ this
  simp[ringKrullDim]

  have := Order.krullDim_eq_of_orderIso this
  rw[Order.krullDim_eq_of_orderIso <| PrimeSpectrum.equivSubtype (X.presheaf.stalk Z)]
  rw[this]
  have := irreducibleSetEquivPoints (α := X)
  have := PrimeSpectrum.pointsEquivIrreducibleCloseds Γ(X, W)
  have := TopologicalSpace.IrreducibleCloseds.orderIsoSubtype (PrimeSpectrum ↑Γ(X, W))

  have r := PrimeSpectrum.vanishingIdeal_isClosed_isIrreducible (R := Γ(X, W))
  let isoNeeded : {z // z ∈ W} ≃o PrimeSpectrum ↑Γ(X, W) := sorry
  have := Order.height_orderIso isoNeeded ⟨Z, hW.right⟩

  sorry

instance {X : Scheme} [IsLocallyNoetherian X] {Z : X} : IsNoetherianRing (X.presheaf.stalk Z) := by
  have : ∃ U : X.affineOpens, Z ∈ U.1 := by
    obtain ⟨R, f, hf, hZ, hU⟩ := AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset
      (U := ⊤) (x := Z) (by aesop)
    let U : X.Opens := {
      carrier := range ⇑(ConcreteCategory.hom f.base)
      is_open' := IsOpenImmersion.isOpen_range f
    }
    have V : X.affineOpens := {
      val := U
      property := by

        sorry
    }
    sorry
  obtain ⟨U, hU⟩ := this
  have := AlgebraicGeometry.IsAffineOpen.isLocalization_stalk U.2 ⟨Z, hU⟩
  apply @IsLocalization.isNoetherianRing _ _ (U.2.primeIdealOf ⟨Z, hU⟩).asIdeal.primeCompl (X.presheaf.stalk Z) _ (X.presheaf.algebra_section_stalk ⟨Z, hU⟩) this
  exact IsLocallyNoetherian.component_noetherian U


instance {X : Scheme} [IsIntegral X] {Z : X} : IsDomain (X.presheaf.stalk Z) :=
  Function.Injective.isDomain _ (IsFractionRing.injective (X.presheaf.stalk Z) (X.functionField))


open Multiplicative
noncomputable
def _root_.AlgebraicGeometry.Scheme.ord {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  (Z : X) (hZ : Order.height Z = 1) : X.functionField →*₀ ℤₘ₀ :=
  have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk Z) := by
    rw[Ring.krullDimLE_iff, stalk_dim_of_codim Z hZ]
  Ring.ordFrac (X.presheaf.stalk Z)

/-
I'm not enitrely sure if this works or not. I think since we're working on an intetgral scheme,
we really should have that there is no mixing of dimension and this should work fine
-/
noncomputable
def div [IsIntegral X] [h : IsLocallyNoetherian X]
  (f : X.functionField) (hf : f ≠ 0) : AlgebraicCycle X where
    -- TODO: Fix this definition with the new definition of order
    toFun Z := if h : Order.height Z = 1 then WithZero.unzero hf (AlgebraicGeometry.Scheme.ord Z h f) else 0
    supportWithinDomain' := by simp
    supportLocallyFiniteWithinDomain' := by
      intro z hz

      have : ∃ U : X.Opens, ∃ f' : Γ(X, U), ∃ hU : Nonempty U,
        X.germToFunctionField U f' = f ∧ IsUnit f' := by
        /-
        This is really just the universal property of colimits + the fact that the map is
        injective, so there should be nothing to say here.
        -/
        #check AlgebraicGeometry.Scheme.RationalMap.fromFunctionField

        sorry
      obtain ⟨U, f', hU, hf'⟩ := this
      /-
      We want to say here that the order of vanishing of f is trivial on all points of U.
      This just follows from the order of vanshing being a homomorphism.
      -/
      have : ∀ y ∈ U, ∀ h : height y = 1, _root_.AlgebraicGeometry.Scheme.ord y h f = 0 := sorry
      by_cases h : z ∈ U
      · /-
        This case should be easy, note that f' should not have any zeros or poles in U. So, we should
        just make a lemma saying the order of vanishing of a unit in some open set must be trivial
        on that set.
        -/
        use U
        constructor
        · rw [@_root_.mem_nhds_iff]
          use U
          simp[h]
          exact U.2
        ·
          sorry
        /-
        Trivial nonsense
        -/

      · let XU := (⊤ : Set X) \ U
        have properClosed : XU ≠ ⊤ ∧ IsClosed XU := sorry

        have (y : X) (h : Order.height y = 1)
          (hy : _root_.AlgebraicGeometry.Scheme.ord y h f ≠ 0) : closure {y} ⊆ XU :=

          sorry
        have (y : X) (h : Order.height y = 1)
          (hy : _root_.AlgebraicGeometry.Scheme.ord y h f ≠ 0) : Prop := by
          --#check (this y h hy) (closure {y})
          sorry

        /-have (y : X) (h : Order.height y = 1)
          (hy : _root_.AlgebraicGeometry.Scheme.ord f hf y h ≠ 0) :
          (this y h hy) (closure {y}) ∈ irreducibleComponents XU := sorry-/
        /-
        Want to  say that any such y is an irreducible component of X \ U, but this doesn't seem
        to typecheck

        have (y : X) (h : Order.height y = 1)
          (hy : _root_.AlgebraicGeometry.Scheme.ord f hf y h ≠ 0) :
          (this y h hy) (closure {y}) ∈ irreducibleComponents XU := sorry

        From here we should be basically done, we'll get that the set of irreducible components
        is finite from our Noetherian hypothesis. Then, we just need to relate that back to the
        points by picking generic points.
        -/


        /-


        Here we should say that if y has nontrivial order of vanishing, its closure must be
        an irreducible component of X \ U.

        Now we want to use TopologicalSpace.NoetherianSpace.finite_irreducibleComponents to conclude
        that the set of such points must be finite (we will also have to invoke some structure
        on the map taking generic points to their closures).
        -/
        --#check irreducibleComponent
        sorry



      /-
      Since f is an element of the function field, it is equivalently given by a section of 𝒪ˣ(U)
      for some nonempty open subset U (this should be more or less by definition, but of course there
      may be some API to develop here connecting up the different equivalent ways of talking
      about function fields). Well, I suppose technically f should correspond to 𝒪(U) for some U,
      and then we can further specialise to where f has no zeros, again this depends on how things
      are set up slightly.

      Then, in U f has no zeros or poles, which is a lemma we should prove. This means that the
      points where f has zeros or poles must occur within X \ U. This X \ U is a proper closed
      subset of X since U is nonempty, meaning that any point in X \ U has codimension at most 1,
      (since, such a point is a specialization of the generic point, which is not in U). Hence,
      any prime divisor where f has nontrivial order of vanishing must be an irreducible component
      of X \ U.

      But we know that since X is locally Noetherian, any closed subset has finitely many
      irreducible components, and so we win.
      -/

    /-locfin := by
      have := h.1

      /-
      Stacks project 31.26.4

      Note that we need X locally Noetherian for local finiteness
      -/
      sorry-/

theorem div_homomorphism [IsIntegral X] [h : IsLocallyNoetherian X]
  (f : X.functionField) (hf : f ≠ 0) (g : X.functionField) (hg : g ≠ 0) :
  div (f * g) (by simp_all) = div f hf + div g hg := by
  ext a
  suffices (div (f*g) (by simp_all)).toFun a = (div f hf).toFun a + (div g hg).toFun a by exact this
  simp[div]
  split_ifs
  · rename_i ha
    exact Scheme.ord_additive f hf g hg a ha
  · rfl


structure LocallyFiniteClosedFamily (X : Scheme.{u}) where
  {ι : Type}
  B : ι → Scheme.{u}
  δx : X → ℤ
  hδx : TopologicalSpace.isDimensionFunction δx
  (δ : (i : ι) → B i → ℤ)
  hδ : ∀ i, TopologicalSpace.isDimensionFunction (δ i)
  hB : ∀ i : ι, IsIntegral (B i)
  hB' : ∀ i : ι, IsLocallyNoetherian (B i)
  W : (i : ι) → B i ⟶ X
  qcW : ∀ i, QuasiCompact (W i)
  ciW : ∀ i : ι, IsClosedImmersion (W i)
  f : (i : ι) → (B i).functionField
  hf : ∀ i : ι, f i ≠ 0
  hW : LocallyFinite (fun i : ι ↦ (map (δ i) δx (W i) (div (f i) (hf i))).support)

def _root_.LocallyFiniteClosedFamily.ofRat (δ : X → ℤ) (hδ : isDimensionFunction δ)  [ix : IsIntegral X]
  (g : X.functionField) (hg : g ≠ 0) [iln : IsLocallyNoetherian X] : LocallyFiniteClosedFamily X where
  ι := Fin 1
  B := fun _ ↦ X
  δx := δ
  hδx := hδ
  δ i := δ
  hδ i := hδ
  hB i := ix
  hB' i := iln
  W i := 𝟙 X
  qcW i := (quasiCompact_iff (𝟙 X)).mpr fun U a a ↦ a
  ciW i := IsClosedImmersion.instOfIsIsoScheme (𝟙 X)
  f i := g
  hf i := hg
  hW := by
    simp[map_id, LocallyFinite]
    have := (div g hg).3
    intro x
    specialize this x (by aesop)
    obtain ⟨t, ht⟩ := this
    use t
    refine ⟨ht.1, ?_⟩
    suffices Finite (Fin 1) by exact toFinite {i | (Function.locallyFinsuppWithin.support (div g hg) ∩ t).Nonempty}
    exact Finite.of_subsingleton


variable {ι : Type*} (B : ι → Scheme) (δx : X → ℤ) [hδx : TopologicalSpace.isDimensionFunction δx]
    (δ : (i : ι) → B i → ℤ) [hδ : ∀ i, TopologicalSpace.isDimensionFunction (δ i)]
    [hB : ∀ i : ι, IsIntegral (B i)]
    [hB' : ∀ i : ι, IsLocallyNoetherian (B i)]
    (W : (i : ι) → B i ⟶ X) [qcW : ∀ i, QuasiCompact (W i)]
    (f : (i : ι) → (B i).functionField) (hf : ∀ i : ι, f i ≠ 0)
    (hW : LocallyFinite (fun i : ι ↦ (map (δ i) δx (W i) (div (f i) (hf i))).support))

variable (F : LocallyFiniteClosedFamily X)
include hW in
theorem singletonFinite (z : X) :
    {i : ι | ((map (δ i) δx (W i) (div (f i) (hf i))).support ∩ {z}).Nonempty}.Finite := by
  choose U hU using hW z
  have : {z} ⊆ U := singleton_subset_iff.mpr (mem_of_mem_nhds hU.1)
  have : {i | (Function.locallyFinsuppWithin.support (map (δ i) δx (W i) (div (f i) (hf i))) ∩ {z}).Nonempty} ⊆
      {i | ((fun i ↦ Function.locallyFinsuppWithin.support (map (δ i) δx (W i) (div (f i) (hf i)))) i ∩ U).Nonempty} := by
    simp[this]
    intro k l
    simp[Function.locallyFinsuppWithin.support, Function.support]
    rw [@inter_nonempty_iff_exists_right]
    use z
    constructor
    · exact this rfl
    · exact l
  exact Finite.subset hU.2 this


set_option maxHeartbeats 0
/--
Given a family of closed subschemes of X (represented as an ι indexed collection of closed immersions
W i from B i to X) which is locally finite, we define a principal cycle to be a cycle expressed as
the sum of the pushforwards of div (f i), where f is a family of rational functions on (B i).
-/
noncomputable
  def principalCycle : AlgebraicCycle X where
    toFun z :=
      ∑ i ∈ (singletonFinite B δx δ W f hf hW z).toFinset,
      (∑ x ∈ (preimageSupportFinite (W i) (div (f i) (hf i)) z).toFinset,
      mapAux (δ i) δx (W i) x)
    supportWithinDomain' := by simp
    supportLocallyFiniteWithinDomain' := by
      intro z hz
      let fino (i : ι) := map_locally_finite (δ i) δx (W i) (div (f i) (hf i)) --(f i)
      let un := ⋃ (i : (singletonFinite B δx δ W f hf hW z).toFinset), (fino i z hz).choose
      #check Exists.choose_spec
      /-
      This should just use choose_spec and the fact that finite unions preserve these properties
      -/
      have : un ∈ 𝓝 z ∧ ∀ i : ι, (un ∩ Function.support fun z ↦ ∑ x ∈ (preimageSupportFinite (W i) (div (f i) (hf i)) z).toFinset, mapAux (δ i) δx (W i) x).Finite := sorry
      use un
      constructor
      · exact this.1
      · suffices (un ∩ (⋃ (i ∈ (singletonFinite B δx δ W f hf hW z).toFinset),
        (Function.support (fun z ↦ ∑ x ∈ (preimageSupportFinite (W i) (div (f i) (hf i)) z).toFinset,
          mapAux (δ i) δx (W i) x)))).Finite by
          suffices (un ∩ Function.support fun z ↦ ∑ i ∈ (singletonFinite B δx δ W f hf hW z).toFinset, ∑ x ∈ (preimageSupportFinite (W i) (div (f i) (hf i)) z).toFinset, mapAux (δ i) δx (W i) x) ⊆ un ∩ (⋃ (i ∈ (singletonFinite B δx δ W f hf hW z).toFinset), (Function.support (fun z ↦ ∑ x ∈ (preimageSupportFinite (W i) (div (f i) (hf i)) z).toFinset, mapAux (δ i) δx (W i) x))) by sorry
          refine inter_subset_inter (fun ⦃a⦄ a ↦ a) ?_
          --(singletonFinite B δx hδx δ hδ hB hB' W qcW f hf hW z).toFinset ?_


          convert Finset.support_sum (s := (singletonFinite B δx δ W f hf hW z).toFinset) (f := fun i z' ↦ ∑ x ∈ (preimageSupportFinite (W i) (div (f i) (hf i)) z').toFinset, mapAux (δ i) δx (W i) x)

          sorry
        suffices (⋃ (i ∈ (singletonFinite B δx δ W f hf hW z).toFinset), un ∩ ((Function.support (fun z ↦ ∑ x ∈ (preimageSupportFinite (W i) (div (f i) (hf i)) z).toFinset, mapAux (δ i) δx (W i) x)))).Finite by sorry

        have := this.2
        refine Finite.biUnion' ?_ fun i hi ↦ this i
        apply Set.finite_mem_finset




/-
Note that here we are not actually using the fact that the morphisms in our family are closed immersions.
I think we'll need this in theorems and to make sure that this is indeed an equivalence relation however.
-/
noncomputable
def is_rationally_equivalent (D₁ D₂ : AlgebraicCycle X) : Prop :=
  ∃ F : LocallyFiniteClosedFamily X, D₁ - D₂ =
    have := F.hδx
    have := F.hδ
    have := F.hB
    have := F.hB'
    have := F.qcW
    principalCycle F.B F.δx F.δ F.W F.f F.hf F.hW



--set_option pp.universes true
/-
This is more or less just the statement that
-/
theorem equiv_of_ratEquiv (δ : X → ℤ) (hδ : isDimensionFunction.{u} δ) [IsIntegral X] [IsLocallyNoetherian X] :
  IsEquiv (AlgebraicCycle X) (is_rationally_equivalent (X := X)) where
  refl := by
    simp[is_rationally_equivalent]
    let F : LocallyFiniteClosedFamily X := LocallyFiniteClosedFamily.ofRat δ hδ 1 (one_ne_zero)
    use F

    /-
    Universe issues here thar need sorting out!!!
    Should be able to use F here, but something funny is going on
    -/
    --use F
    sorry
  trans := by
    simp[is_rationally_equivalent]

    intro a b c F1 hab F2 hbc
    /-
    We need here that the sum of principal cycles is again principal. The idea is we want to take our new family to be the
    union of the old two families, and for the new rational functions to be the products of the given rational functions
    if they live on the same component, otherwise to be just the function that was there originally.

    Should be locally finite by the fact that a finite union of locally finite collections should be locally finite.


    -/


    sorry
  symm := sorry




/-
We now have some notion of algebraic cycles on a scheme, and we have some
properties which let us discuss rational equivalence (more or less)

Define :-
  Algebraic cycles :-
  - Graded pieces (probably using dimension function stratification)
  - Specialisation to the case of divisors (linear equilavence & so on)
  - Characterisation in cases we care about as free abelian group of prime divisors (instead of
    the more bulky general definition we have now)
  - Characterisation in case of curves as divisors being sums of points

  Invertible sheaves:-
  - Invertible sheaves
  - Defining the Picard group of invertible sheaves
  - Rational sections of sheaves
  - Existence of rational sections on (at least) integral schemes
  - Weil divisor associated to an invertible sheaf
  - Showing that the map previously defined is a homomorphim
  - Showing when this map gives an isomorphism between the picard group and the divisor class group
  - Definition of O_Y for Y ∈ X.

  Cohomology:-
  For Riemann-Roch, we only need the following:
  - The Euler Characteristic of a sheaf
  - Proof that the Euler characteristic is additive
  - Above requires long exact sequence associated to a sheaf
  - Cohomology of skyscraper sheaf

  Things to note:
  - One can feasibly do this without developing Cech cohomology, by showing
    the skyscraper is flasque and that the
  - It's unclear to me whether we need some notion of Serre vanishing for a
    form of the Euler characteristic formula. I think it should still hold,
    since the rank-nullity theorem still holds in this case. That said,
    the meaning of the infinite sum would still be a bit mysterious.
    Possibly best to do this with Serre finiteness, which ought to fall
    out of Cech cohomology definition almost immediately
  - One thing is, we could define the Euler characteristic for the case we need to be
    h0 - h1. Then, to prove this notion of EC is additive, we just need to show Serre vanishing
    for curves. I think agian this is easiest to do w/ Cech cohomology.
  Cech Cohomology:
  - Cech cohomology with respect to a cover
  - Show that a curve always has an affine cover with two pieces
  - Compute cohomology of a skyscraper by taking an affine cover
    with 1 open containing supported point
  -
  -

Could define :-
  - Axiomitisation of intersection form - might be good if we want to do
    asymptotic RR
  -



-/
#check (3 : ℕ∞) - ⊤

end AlgebraicCycle
