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
    universal : ∀ X : Scheme, ∀ f : X ⟶ S, LocallyOfFiniteType f → Catenary X

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
      simp
      exact toFinite ({x} ∩ Function.support fun x ↦ coeff)

/-
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
  have cpct : IsCompact (f.base ⁻¹' {z}) := by exact QuasiCompact.isCompact_preimage_singleton f z
  rw[isCompact_iff_finite_subcover] at cpct

  let cov : f.base ⁻¹' {z} → Set X := by
    intro x
    choose U hU using c.supportLocallyFiniteWithinDomain' x (by simp)
    exact U

  have covSpec : ∀ x : f.base ⁻¹' {z}, cov x ∈ 𝓝 ↑x ∧ (cov x ∩ Function.support c.toFun).Finite := by
    intro x
    exact Classical.choose_spec (c.supportLocallyFiniteWithinDomain' (↑x) (of_eq_true (by simp)))

  let openCov : f.base ⁻¹' {z} → Set X := by
    intro x
    have cs := (covSpec x).1
    rw[_root_.mem_nhds_iff] at cs
    choose U hU using cs
    exact U

  have openCovSpec : ∀ x : f.base ⁻¹' {z}, openCov x ⊆ cov x ∧ IsOpen (openCov x) ∧ ↑x ∈ (openCov x) := by
    intro x
    have := Classical.choose_spec (Eq.mp (congrArg (fun _a ↦ _a) (propext _root_.mem_nhds_iff)) ((covSpec x).1))
    aesop

  have covOpen : ∀ x : f.base ⁻¹' {z}, IsOpen (openCov x) := by
    intro x
    specialize openCovSpec x
    exact openCovSpec.2.1

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

  have : (⋃ x ∈ V, (openCov x ∩ Function.support c.toFun)).Finite := by
    have : ∀ (i : { x // x ∈ V }), Finite ↑((fun x ↦ openCov ↑x ∩ Function.support c.toFun) i) := by
      exact fun i ↦ openCovSpec' ↑i
    have := Set.finite_iUnion (ι := V) (f := fun x => openCov x ∩ Function.support c.toFun) this
    simp at this
    have obv : (⋃ x ∈ V, openCov x ∩ Function.support c.toFun) = (⋃ i : V, openCov ↑i ∩ Function.support c.toFun) := by
      exact
        Eq.symm (iUnion_subtype (Membership.mem V) fun x ↦ openCov ↑x ∩ Function.support c.toFun)
    rw[obv]
    exact this

  have : (f.base ⁻¹' {z} ∩ Function.support c) ⊆ (⋃ x ∈ V, openCov x ∩ Function.support c) := by
    have : (⋃ x ∈ V, openCov x ∩ Function.support c) = ((⋃ x ∈ V, openCov x) ∩ Function.support c) := by
      exact Eq.symm (iUnion₂_inter (fun i j ↦ openCov i) (Function.support ⇑c))
    rw[this]
    suffices f.base ⁻¹' {z} ⊆ ⋃ x ∈ V, openCov x by exact inter_subset_inter hV fun ⦃a⦄ a ↦ a
    exact hV

  (expose_names; exact Finite.subset this_1 this)


/--
UNCLEAR IF THIS NEEDS TO BE ITS OWN DEFINITION.
-/
noncomputable
def _root_.AlgebraicGeometry.LocallyRingedSpace.Hom.residueMap {X Y : LocallyRingedSpace} (f : X ⟶ Y)
  (x : ↑X.toTopCat) :
    IsLocalRing.ResidueField (Y.presheaf.stalk (f.base x)) →+*
    IsLocalRing.ResidueField (X.presheaf.stalk x) :=
  IsLocalRing.ResidueField.map (f.stalkMap x).hom
  --IsLocalRing.ResidueField.map (AlgebraicGeometry.LocallyRingedSpace.Hom.stalkMap f x).hom

/-
variable {R S : Type*} [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
  [Algebra R S] [Algebra.HasGoingDown R S] {p : Ideal R} {q : Ideal S} [p.IsPrime] [q.IsPrime] (h : q.LiesOver p)
#check p • (Localization.AtPrime q) -/

instance {R S : Type*} [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
  [Algebra R S] [Algebra.HasGoingDown R S] {p : Ideal R} {q : Ideal S} [p.IsPrime] [q.IsPrime] : CommRing ((Localization.AtPrime q) ⧸ (p • (⊤ : Submodule R (Localization.AtPrime q)))) := sorry
/-
This is necessary for proving that the pushforward is functorial.
-/
@[stacks 00ON]
lemma _root_.Algebra.dimension_sum_of_going_down {R S : Type*} [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
  [Algebra R S] [Algebra.HasGoingDown R S] {p : Ideal R} {q : Ideal S} [p.IsPrime] [q.IsPrime] (h : q.LiesOver p) :
  ringKrullDim (Localization.AtPrime q) = ringKrullDim (Localization.AtPrime p) + ringKrullDim ((Localization.AtPrime q) ⧸ (p • (⊤ : Submodule R (Localization.AtPrime q)))) := sorry

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



lemma _root_.AlgebraicGeometry.LocallyRingedSpace.Hom.degree_comp {X Y Z : Scheme}
  [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (f : X ⟶ Y)
  (g : Y ⟶ Z) (x : X) : Hom.degree (f ≫ g) x = Hom.degree f x * Hom.degree g (f.base x) := by
  simp[Hom.degree]

  sorry

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

lemma mapAux_comp {Y Z : Scheme} (δx : X → ℤ) [TopologicalSpace.isDimensionFunction δx]
  (δy : Y → ℤ) (δz : Z → ℤ) [TopologicalSpace.isDimensionFunction δy] [TopologicalSpace.isDimensionFunction δz]
  (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : mapAux δx δz (f ≫ g) x = (mapAux δx δy f x) * (mapAux δy δz g (f.base x)) := by
  simp[mapAux]
  --split_ifs
  --simp[Hom.degree]

  sorry

--set_option profiler true


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

lemma ext (c : AlgebraicCycle X) (c' : AlgebraicCycle X) : c = c' ↔ c.toFun = c'.toFun := by
  rw[Function.locallyFinsuppWithin.ext_iff]
  exact Iff.symm funext_iff


--#check CategoryTheory.CategoryStruct.id
lemma map_id (δₓ : X → ℤ) [TopologicalSpace.isDimensionFunction δₓ] (c : AlgebraicCycle X) :
    map δₓ δₓ (𝟙 X) c = c := by
   rw[ext]
   ext z
   have : (c z ≠ 0 ∧ (preimageSupportFinite (𝟙 X) c z).toFinset = {z}) ∨ (c z = 0 ∧ (preimageSupportFinite (𝟙 X) c z).toFinset = ∅) := by
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
   obtain h | h := this
   · simp[map, mapAux]
     rw[h.2]
     simp[Hom.degree]
     rfl
   · simp[map, mapAux]
     rw[h.2]
     simp[Hom.degree]
     exact h.1.symm
/-
In order to show that map is functorial, we need to have some lemma
-/
lemma map_comp {Y Z : Scheme} (δₓ : X → ℤ) [TopologicalSpace.isDimensionFunction δₓ] (δy : Y → ℤ) [TopologicalSpace.isDimensionFunction δy]
  (δz : Z → ℤ) [TopologicalSpace.isDimensionFunction δz]
  (f : X ⟶ Y) [qcf : QuasiCompact f] (g : Y ⟶ Z) [qcg : QuasiCompact g]
  (c : AlgebraicCycle X) (c' : AlgebraicCycle Y) : map δy δz g (map δₓ δy f c) = map δₓ δz (f ≫ g) c := by
  simp[ext]
  ext a
  simp[map]
  --suffices
  suffices ∑ x ∈ (preimageSupportFinite g (map δₓ δy f c) a).toFinset, (map δₓ δy f c) x * mapAux δy δz g x = ∑ x ∈ (preimageSupportFinite (f ≫ g) c a).toFinset, c x * mapAux δₓ δz (f ≫ g) x by exact
    this --∑ x ∈ (preimageSupport f c x).Finite
  suffices ∑ x ∈ (preimageSupportFinite g (map δₓ δy f c) a).toFinset, (∑ y ∈ (preimageSupportFinite f c x).toFinset, c y * mapAux δₓ δy f y) * mapAux δy δz g x = ∑ x ∈ (preimageSupportFinite (f ≫ g) c a).toFinset, c x * mapAux δₓ δz (f ≫ g) x by exact this
  simp[mapAux_comp δₓ δy δz f g]

  sorry

variable {R} {M : Type*} [AddCommMonoid M] [Module R M]
--#check AlgebraicGeometry.Scheme

def quotientExactf (a b : R) :
    (R ⧸ Submodule.span (R := R) (M := R) {a}) →ₗ[R] (R ⧸ Submodule.span (R := R) (M := R) {a * b}) :=
  let j := (Submodule.span (R := R) (M := R) {a*b}).mkQ ∘ₗ LinearMap.mul R R b
  let m := Submodule.liftQ (p := Submodule.span (R := R) (M := R) {a}) j
  have : Submodule.span R {a} ≤ LinearMap.ker j := by
    simp[j]
    rw [@Ideal.span_singleton_le_iff_mem]
    rw [@LinearMap.mem_ker]
    suffices Submodule.mkQ (Ideal.span {a * b}) ((LinearMap.mul R R) ↑b ↑a) = 0 by exact this
    simp only [LinearMap.mul_apply_apply]
    suffices (Submodule.mkQ (Ideal.span {a * b})) (a * b) = 0 by
      have r : a * b = b * a := by exact CommMonoid.mul_comm a b
      rw[← r]
      exact this
    aesop
  m this

def injectivef {a b : R} (hb : b ∈ nonZeroDivisors R) : Function.Injective (quotientExactf a b) := by
  suffices LinearMap.ker (quotientExactf a b) = ⊥ by exact LinearMap.ker_eq_bot.mp this
  simp[quotientExactf]
  apply Submodule.ker_liftQ_eq_bot'
  ext x
  constructor
  · intro hx
    rw[@LinearMap.mem_ker]
    suffices (Submodule.mkQ (Ideal.span {a * b}) (b * x)) = 0 by
      exact this
    suffices (Submodule.mkQ (Ideal.span {a * b}) (x * b)) = 0 by
      have co : x * b = b * x := by exact CommMonoid.mul_comm x ↑b
      rw[← co]
      exact this

    rw [@Submodule.mkQ_apply]
    rw [@Submodule.Quotient.mk_eq_zero]
    rw [@Ideal.mem_span_singleton]
    rw [propext (dvd_cancel_right_mem_nonZeroDivisors hb)]
    exact Ideal.mem_span_singleton.mp hx
  · intro hx
    have : (Submodule.mkQ (Ideal.span {a * b})) (x * b) = 0 := by
      rw [@LinearMap.mem_ker] at hx
      rw [@LinearMap.comp_apply] at hx
      rw [LinearMap.mul_apply_apply] at hx
      have : x * b = b * x := by exact CommMonoid.mul_comm x b
      rwa[← this] at hx
    rw [@Submodule.mkQ_apply] at this
    rw [@Submodule.Quotient.mk_eq_zero] at this
    rw [@Ideal.mem_span_singleton] at this
    rw [@Ideal.mem_span_singleton]
    exact (propext (dvd_cancel_right_mem_nonZeroDivisors hb)).mp this


def quotientExactg (a b : R) :
  (R ⧸ Submodule.span (R := R) (M := R) {a*b}) →ₗ[R] (R ⧸ Submodule.span (R := R) (M := R) {b}) :=
    let j := (Submodule.span (R := R) (M := R) {b}).mkQ
    let m := Submodule.liftQ (p := Submodule.span (R := R) (M := R) {a * b}) j
    have : Submodule.span R {a * b} ≤ LinearMap.ker j := by
      simp[j]
      rw [@Ideal.span_singleton_le_span_singleton]
      exact dvd_mul_left b a
    m this

def surjectiveg {a b : R} (ha : a ∈ nonZeroDivisors R) (hb : b ∈ nonZeroDivisors R) :
  Function.Surjective (quotientExactg a b) := by
  simp[quotientExactg, Submodule.mkQ_surjective]
  let f : R →ₗ[R] R := LinearMap.mul R R (a * b)
  have hf : LinearMap.range f = Ideal.span {a * b} := by
    simp[f]
    ext x
    constructor
    · intro hx
      simp_all
      obtain ⟨y, hy⟩ := hx
      rw [← hy]
      rw [@Ideal.mem_span_singleton]
      exact dvd_mul_right (a * b) y
    · intro hx
      simp_all
      rw [@Ideal.mem_span_singleton] at hx
      rw [@dvd_def] at hx
      obtain ⟨y, hy⟩ := hx
      use y
      exact hy.symm
  suffices Function.Surjective ⇑(Submodule.liftQ (LinearMap.range f) (Submodule.mkQ (Ideal.span {b}))
      (hf ▸ _root_.id (Eq.refl (Submodule.mkQ (Ideal.span {b}))) ▸ quotientExactg._proof_19 a b)) by

    sorry

  apply LinearMap.surjective_range_liftQ
  apply Submodule.mkQ_surjective


def quotientExact {a b : R} (ha : a ∈ nonZeroDivisors R) (hb : b ∈ nonZeroDivisors R) :
  Function.Exact (quotientExactf a b) (quotientExactg a b) := by
  intro r
  constructor
  · intro hr
    have : (b : R ⧸ Submodule.span R {a * b}) ∣ r := sorry
    rw[@dvd_def] at this
    obtain ⟨c, hc⟩ := this

    simp_all[quotientExactg, quotientExactf]
    let c' : R ⧸ Ideal.span {a} := by

      sorry
    use c'
    sorry
  · intro hr
    have : (b : R ⧸ Submodule.span R {a * b}) ∣ r := sorry
    simp[quotientExactg]
    /-
    This should basically be solved from this point, we just need some lemma saying that this
    quotient map sends multiples of b to 0 (which should be true by definition).

    The fact simp can't solve this may be a red flag about our definitions.
    -/
    sorry


variable (R)
noncomputable
def orderOfVanishing' (x : R) := Module.length R (R ⧸ Submodule.span (R := R) (M := R) {x})

/-
This says that the order of vanishing is a group homomorphism from Rˣ to ℤ. We should be able to
define an extension of this homomorphism to the
-/
theorem orderOfVanishing'_additive {a b : R} (ha : a ∈ nonZeroDivisors R) (hb : b ∈ nonZeroDivisors R) : orderOfVanishing' R (a*b) = orderOfVanishing' R a + orderOfVanishing' R b :=
  Module.length_eq_add_of_exact (quotientExactf a b) (quotientExactg a b) (injectivef hb) (surjectiveg ha hb) (quotientExact ha hb)


/-
Would be nice to be able to use something like IsLocalization.lift here to get the homomorphism
properties of all the notions of ord for free.
-/
--#check IsLocalization.lift

theorem orderOfVanishing'_finite [IsNoetherianRing R]
         [IsLocalRing R] [IsDomain R] [IsLocalRing R]
         (hR : ringKrullDim R ≤ 1) {x : R} (hx : x ∈ nonZeroDivisors R) :
         IsFiniteLength R (R ⧸ Ideal.span {x}) := by
  rw[isFiniteLength_iff_isNoetherian_isArtinian]
  constructor
  · exact isNoetherian_quotient (Ideal.span {x})
  · by_cases o : IsArtinianRing R
    · exact isArtinian_of_quotient_of_artinian (Ideal.span {x})
    · have := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hx
      have : ringKrullDim (R ⧸ Ideal.span {x}) ≤ 0 := by
        have : ringKrullDim (R ⧸ Ideal.span {x}) + 1 ≤ 1 := by exact Preorder.le_trans (ringKrullDim (R ⧸ Ideal.span {x}) + 1) (ringKrullDim R) 1 this hR
        by_cases o : ringKrullDim (R ⧸ Ideal.span {x}) = ⊤
        · simp_all
          have rwlem : (⊤ : WithBot (ℕ∞)) + 1 = ⊤ := rfl
          simp[rwlem] at this
          have thing : 1 ≠ (⊤ : WithBot ℕ∞) := by exact ne_of_beq_false rfl
          exact False.elim (thing this)
        · -- The following is awful and I think we should make some lemmas which make arithmetic
          -- with WithBot ℕ∞ a bit easier.
          by_cases o' : ringKrullDim (R ⧸ Ideal.span {x}) = ⊥
          · rw[o']
            exact OrderBot.bot_le 0
          · obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp o'
            have c : d ≠ ⊤ := by
              rw[← hd] at o
              exact fun a ↦ o (congrArg WithBot.some a)
            obtain ⟨d', hd'⟩ := WithTop.ne_top_iff_exists.mp c
            suffices d ≤ 0 by
              rw[← hd]
              exact WithBot.coe_le_zero.mpr this
            suffices d' ≤ 0 by
              rw[← hd']
              aesop
            have : d + 1 ≤ 1 := by
              rw[←hd] at this
              exact WithBot.coe_le_one.mp this
            have : d' + 1 ≤ 1 := by
              rw[← hd'] at this
              exact ENat.coe_le_coe.mp this
            omega
      have : Ring.KrullDimLE 0 (R ⧸ Ideal.span {x}) := by
        exact (krullDimLE_iff 0 (PrimeSpectrum (R ⧸ Ideal.span {x}))).mpr this
      have : IsArtinianRing (R ⧸ Ideal.span {x}) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

      have : IsArtinian (R ⧸ Ideal.span {x}) ((R ⧸ Ideal.span {x})) := this
      apply (OrderEmbedding.wellFoundedLT (β := Submodule (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x})) _)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro N
        refine {toAddSubmonoid := N.toAddSubmonoid, smul_mem' := ?_}
        intro c x hx
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        show r • x ∈ N
        apply N.smul_mem _ hx
      · intro N1 N2 h
        rwa[Submodule.ext_iff] at h ⊢
      · intro N1 N2
        rfl


variable [IsNoetherianRing R]
         [IsLocalRing R]
         (hR : ringKrullDim R = 1)
         {K : Type*}
         [Field K]
         [Algebra R K]
         [IsDomain R]
         [m : IsFractionRing R K] in

noncomputable
def orderOfVanishing (x : K) (hx : x ≠ 0) : ℤ :=
  let r := IsLocalization.sec (nonZeroDivisors R) x
  let a := r.1
  let b := r.2
  have : a ∈ nonZeroDivisors R := by
    suffices a ≠ 0 by aesop
    exact IsLocalization.sec_fst_ne_zero hx
  have fina := Module.length_ne_top_iff.mpr $ orderOfVanishing'_finite R hR.le this

  have finb := Module.length_ne_top_iff.mpr $ orderOfVanishing'_finite R hR.le b.2
  let m := (orderOfVanishing' R a).untop fina
  let n := (orderOfVanishing' R b).untop finb
  m - n

#check Order.coheight

@[stacks 02I4]
lemma fifi {X : Scheme} {Z : X} (U : X.affineOpens) (hU : Z ∈ U.1) :
  Order.height (α := U) ⟨Z, hU⟩ = Order.height Z := by

  /-
  Take the map T ↦ T' mapping T to its intersection with U. This defines a bijective inclusion
  preserving map between the sets of closed irreducible subsets of U and the closed irreducibles
  which meet U in X. This should give us what we want by invariance of krull dim under isomorphisms.

  Translating this to the language of generic points, we want to say that if  b ⤳ Z in X then
  b ⤳ Z in U. Well, U ∈ nhds Z, meaning that for any point y above it in the specialization order,
  U ∈ nhds y, so Bob's your uncle

  Suppose you've given
  -/
  have : U.1.1 ∈ 𝓝 Z := by
    rw [@_root_.mem_nhds_iff]
    use U
    constructor
    · rfl
    · constructor
      · exact U.1.isOpen
      · exact hU
  have {V : X} (hV : V ⤳ Z) : V ∈ U.1 := by
    simp[Specializes] at hV
    have : U.1.1 ∈ 𝓝 V := by
      rw [@le_def] at hV
      exact hV U this
    rw[@_root_.mem_nhds_iff] at this
    obtain ⟨t, ht⟩ := this
    exact ht.1 ht.2.2
  rw[height, height, le_antisymm_iff, iSup_le_iff]
  constructor
  · intro s n hs
    sorry
  · intro n h
    use n
    simp

    sorry

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
lemma foofo {X : Scheme} (Z : X) (d : ℕ) (hZ : Order.height Z = d) : ringKrullDim (X.presheaf.stalk Z) = d := by
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



  #check Spec
  #check IsAffineOpen.primeIdealOf
  have := AlgebraicGeometry.IsAffineOpen.isLocalization_stalk hW.1 ⟨Z, hW.2⟩



  /-
  We now want to say that the points of this local ring correspond to the primes contained in
  primeIdealOf Z. Surely this has to exist somewhere.
  -/



  sorry

instance {X : Scheme} [IsLocallyNoetherian X] {Z : X} : IsNoetherianRing (X.presheaf.stalk Z) := sorry

instance {X : Scheme} [IsIntegral X] {Z : X} : IsDomain (X.presheaf.stalk Z) := sorry

noncomputable
def _root_.AlgebraicGeometry.Scheme.ord {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  (f : X.functionField) (hf : f ≠ 0) (Z : X) (hZ : Order.height Z = 1) : ℤ :=
  orderOfVanishing (X.presheaf.stalk Z) (foofo Z 1 hZ) f hf

theorem _root_.AlgebraicGeometry.Scheme.ord_additive {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  (f : X.functionField) (hf : f ≠ 0) (g : X.functionField) (hg : g ≠ 0) (Z : X) (hZ : Order.height Z = 1) :
  Scheme.ord (f*g) (by simp_all) Z (by simp_all) = Scheme.ord f hf Z hZ + Scheme.ord g hg Z hZ := by
  simp[Scheme.ord]

  sorry


/-
I'm not enitrely sure if this works or not. I think since we're working on an intetgral scheme,
we really should have that there is no mixing of dimension and this should work fine
-/
noncomputable
def div [IsIntegral X] [h : IsLocallyNoetherian X]
  (f : X.functionField) (hf : f ≠ 0) : AlgebraicCycle X where
    toFun Z := if h : Order.height Z = 1 then _root_.AlgebraicGeometry.Scheme.ord f hf Z h else 0
    supportWithinDomain' := by simp
    supportLocallyFiniteWithinDomain' := by
      intro z hz
      have : ∃ U : X.Opens, ∃ f' : Γ(X, U), ∃ hU : Nonempty U, X.germToFunctionField U f' = f ∧ IsUnit f' := sorry
      obtain ⟨U, f', hU, hf'⟩ := this
      /-
      We want to say here that the order of vanishing of f is trivial on all points of U
      -/
      have : ∀ y : U, ∀ h : height y.1 = 1, _root_.AlgebraicGeometry.Scheme.ord f hf y h = 0 := sorry
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
        sorry
      · let XU := (⊤ : Set X) \ U
        have properClosed : XU ≠ ⊤ ∧ IsClosed XU := sorry

        have (y : X) (h : Order.height y = 1)
          (hy : _root_.AlgebraicGeometry.Scheme.ord f hf y h ≠ 0) : closure {y} ⊆ XU := sorry

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


/-
structure LocallyFiniteClosedFamily (X : Scheme) where
  {ι : Type*}
  B : ι → Scheme
  δx : X → ℤ
  [hδx : TopologicalSpace.isDimensionFunction δx]
  (δ : (i : ι) → B i → ℤ)
  [hδ : ∀ i, TopologicalSpace.isDimensionFunction (δ i)]
  [hB : ∀ i : ι, IsIntegral (B i)]
  [hB' : ∀ i : ι, IsLocallyNoetherian (B i)]
  W : (i : ι) → B i ⟶ X
  [qcW : ∀ i, QuasiCompact (W i)]
  [hW : ∀ i : ι, IsClosedImmersion (W i)]
  hW' : LocallyFinite (fun i : ι ↦ _root_.closure (Set.range (W i).base.hom.toFun))
  f : (i : ι) → (B i).functionField

variable (F : LocallyFiniteClosedFamily X)-/


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
      · suffices (un ∩ (⋃ (i ∈ (singletonFinite B δx hδx δ hδ hB hB' W qcW f hf hW z).toFinset),
        (Function.support (fun z ↦ ∑ x ∈ (preimageSupportFinite (W i) (div (f i) (hf i)) z).toFinset,
          mapAux (δ i) δx (W i) x)))).Finite by
          suffices (un ∩ Function.support fun z ↦ ∑ i ∈ (singletonFinite B δx hδx δ hδ hB hB' W qcW f hf hW z).toFinset, ∑ x ∈ (preimageSupportFinite (W i) (div (f i) (hf i)) z).toFinset, mapAux (δ i) δx (W i) x) ⊆ un ∩ (⋃ (i ∈ (singletonFinite B δx hδx δ hδ hB hB' W qcW f hf hW z).toFinset), (Function.support (fun z ↦ ∑ x ∈ (preimageSupportFinite (W i) (div (f i) (hf i)) z).toFinset, mapAux (δ i) δx (W i) x))) by sorry
          refine inter_subset_inter (fun ⦃a⦄ a ↦ a) ?_
          --(singletonFinite B δx hδx δ hδ hB hB' W qcW f hf hW z).toFinset ?_


          convert Finset.support_sum (s := (singletonFinite B δx hδx δ hδ hB hB' W qcW f hf hW z).toFinset) (f := fun i z' ↦ ∑ x ∈ (preimageSupportFinite (W i) (div (f i) (hf i)) z').toFinset, mapAux (δ i) δx (W i) x)

          /-
          What's going on here??
          -/

          --apply Finset.support_sum
          --#check Function.support
          sorry
        suffices (⋃ (i ∈ (singletonFinite B δx hδx δ hδ hB hB' W qcW f hf hW z).toFinset), un ∩ ((Function.support (fun z ↦ ∑ x ∈ (preimageSupportFinite (W i) (div (f i) (hf i)) z).toFinset, mapAux (δ i) δx (W i) x)))).Finite by sorry

        have := this.2
        refine Finite.biUnion' ?_ fun i hi ↦ this i
        apply Set.finite_mem_finset




/-
Note that here we are not actually using the fact that the morphisms in our family are closed immersions.
I think we'll need this in theorems and to make sure that this is indeed an equivalence relation however.
-/
noncomputable
def is_rationally_equivalent (D₁ D₂ : AlgebraicCycle X) : Prop :=
  ∃ F : LocallyFiniteClosedFamily X, D₁ - D₂ = principalCycle F.B F.δx F.hδx F.δ F.hδ F.hB F.hB' F.W F.qcW F.f F.hf F.hW



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

end AlgebraicCycle
