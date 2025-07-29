import Mathlib
--import RiemannRoch.NewModuleLength
import Batteries.Tactic.ShowUnused

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
variable (R : Type v)
         [CommRing R]
         (i : ℕ)
         {X : Scheme}


class TopologicalSpace.dimensionFunction {Z : Type*} [TopologicalSpace Z] (δ : Z → ℤ) where
  increase : ∀ x y : Z, x ⤳ y ∧ x ≠ y → δ (x) > δ (y)
  step : ∀ x y : Z, @CovBy Z (specializationPreorder Z).toLT x y



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
#check Algebra.trdeg

@[stacks 02J8]
class AlgebraicGeometry.UniversallyCatenary {S : Scheme} [IsLocallyNoetherian S] where
    universal : ∀ X : Scheme, ∀ f : X ⟶ S, LocallyOfFiniteType f → Catenary X

--@[stacks 02JW]

namespace DimensionFunction




end DimensionFunction
/-
We define a preorder instance on a scheme X saying x ≤ y if y generalises x. This ought to
correspond to x ≤ y ↔ closure {x} ⊆ closure {y},
-/
instance {X : Scheme} : Preorder X := specializationPreorder X

abbrev AlgebraicCycle (X : Scheme) := Function.locallyFinsuppWithin (⊤ : Set X) ℤ

namespace AlgebraicCycle


noncomputable
def single (x : X) (coeff : ℤ) : AlgebraicCycle X where
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

-- S set
def preimageSupport {Y : Scheme} (f : X ⟶ Y) (c : AlgebraicCycle X) (z : Y) : Set X :=
  f.base ⁻¹' {z} ∩ c.support

/-
Proof:
We wish to show that the intersection of the preimage of z with the support of c is finite.

Since f is quasicompact, the preimage of f is compact. Cover the preimage of f by taking
neighbourhoods such that each U only hits our cycle c in finitely many places.

By compactness, this must have a finite subcover. So, the preimage of z is covered by a finite
number of sets, each intersecting our c in finitely many points. So, this means that on each of
these neighbourhoods, only finitely many
-/
def preimageSupportFinite {Y : Scheme} (f : X ⟶ Y) [qf : QuasiCompact f] (c : AlgebraicCycle X)
  (z : Y) : (preimageSupport f c z).Finite := by
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


noncomputable
def _root_.AlgebraicGeometry.LocallyRingedSpace.Hom.residueMap {X Y : LocallyRingedSpace} (f : X.Hom Y)
  (x : ↑X.toTopCat) :
    IsLocalRing.ResidueField (Y.presheaf.stalk (f.base x)) →+*
    IsLocalRing.ResidueField (X.presheaf.stalk x) :=
  IsLocalRing.ResidueField.map (AlgebraicGeometry.LocallyRingedSpace.Hom.stalkMap f x).hom


open Classical in
noncomputable
def _root_.AlgebraicGeometry.LocallyRingedSpace.Hom.degree {X Y : Scheme} (f : X ⟶ Y)
  (x : X) : ℕ := @Module.finrank
    (IsLocalRing.ResidueField (Y.presheaf.stalk (f.base x)))
    (IsLocalRing.ResidueField (X.presheaf.stalk x))
    (by infer_instance)
    (by infer_instance)
    (by have := RingHom.toAlgebra (f.residueMap x); exact Algebra.toModule)

open Classical in
noncomputable
def mapAux {Y : Scheme} (δₓ : X → ℤ) [dimensionFunction δₓ]
  (δₐy : Y → ℤ) [dimensionFunction δₐy] (f : X ⟶ Y) (x : X) : ℤ :=
  if δₓ x = δₐy (f.base x) then Hom.degree f x else 0


open Classical in
noncomputable
def map {Y : Scheme} (δₓ : X → ℤ) [dimensionFunction δₓ] (δy : Y → ℤ) [dimensionFunction δy]
  (f : X ⟶ Y) [qc : QuasiCompact f] (c : AlgebraicCycle X) : AlgebraicCycle Y where
  toFun z := (∑ x ∈ (preimageSupportFinite f c z).toFinset, mapAux δₓ δy f x)
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' := by
    intro y hy
    /-
    Idea: Take some open affine neighbourhood of y, then this must be quasicompact since affine
    schemes are quasicompact. This should suffice as our open set, and the local finiteness
    argument should be pretty similar to the one above in preimageSupportFinite.

    In more detail, we want to show that our affine open neighbourhood U of y intersects the
    support of toFun defined above in finitely many places. In other words, we want to show that
    there are finitely many places where our pushed forward cycle is supported on U.

    The claim on stacks project is that f ⁻¹' V ∩ c.support is finite by "a simple topological
    argument which we omit". The argument here should be that f⁻¹' V is compact, and we can cover
    this by taking sets that intersect c.support in finitely many places, and so there must be
    a finite subcover of this thing still covering f ⁻¹' V. This is very similar to what's done
    above.

     Note that in the above definition,
    we're summing over f ⁻¹' z ∩ c.support for every z.
    -/
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
    · /-
      We wish to show that around any point, there are finitely many places where the pushforward
      is supported. To show this, take an arbitrary point z : Y and take an arbitrary open compact
      set around it. The pullback of this is compact by definition of f being quasicompact, and
      so there are finitely many places where this pullback of our chosen set meets the cycle we're
      pushing forward (say c). Since this set ought to be the union of the pullbacks of all the
      points in U, we should get our result.
      -/
      have cpct : IsCompact (f.base ⁻¹' W) := qc.1 W.carrier W.is_open' affineCompact
         --exact QuasiCompact.isCompact_preimage_singleton f z
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

      simp only [preimageSupport, Function.locallyFinsuppWithin.support]

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
        --simp at this
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

      have : (f.base ⁻¹' W ∩ Function.support c).Finite := by

        sorry

      suffices (W.carrier ∩ {z : Y | (preimageSupport f c z).Nonempty}).Finite by
        simp[preimageSupportFinite]

        apply Finite.subset this
        suffices Function.support (fun z ↦ (∑ x ∈ (preimageSupportFinite f c z).toFinset, mapAux δₓ δy f x)) ⊆ {z | (preimageSupport f c z).Nonempty} by exact inter_subset_inter (fun ⦃a⦄ a ↦ a) this

        simp only [preimageSupportFinite, preimageSupport, toFinset]

        sorry

      suffices (f.base '' (f.base ⁻¹' W.carrier ∩ (⋃ z : Y, preimageSupport f c z))).Finite by

        sorry

      apply Finite.image
      have r : f.base ⁻¹' W.carrier ∩ (⋃ z : Y, f.base ⁻¹' {z}) ⊆ f.base ⁻¹' W.carrier := sorry
      suffices (f.base ⁻¹' W ∩ Function.support c).Finite by sorry
      exact this


variable {R} {M : Type*} [AddCommMonoid M] [Module R M]


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

theorem orderOfVanishing'_additive {a b : R} (ha : a ∈ nonZeroDivisors R) (hb : b ∈ nonZeroDivisors R) : orderOfVanishing' R (a*b) = orderOfVanishing' R a + orderOfVanishing' R b :=
    Module.length_eq_add_of_exact (quotientExactf ha hb) (quotientExactg a b) (injectivef hb) (surjectiveg ha hb) (quotientExact ha hb)



theorem orderOfVanishing'_finite' [IsNoetherianRing R]
         [IsLocalRing R] [IsDomain R] [IsLocalRing R]
         [DimensionLEOne R] {x : R} (hx : x ∈ nonZeroDivisors R) : IsFiniteLength R (R ⧸ Ideal.span {x}) := by
  /-
  This is now more or less sorry free, this only relies on DimensionLEOne being equivalent to the
  dimension being ≤ 1.
  -/
  have translation : ringKrullDim R ≤ 1 := by sorry
  rw[isFiniteLength_iff_isNoetherian_isArtinian]
  constructor
  · exact isNoetherian_quotient (Ideal.span {x})
  · by_cases o : IsArtinianRing R
    · exact isArtinian_of_quotient_of_artinian (Ideal.span {x})
    · have := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hx
      have : ringKrullDim (R ⧸ Ideal.span {x}) ≤ 0 := by
        have : ringKrullDim (R ⧸ Ideal.span {x}) + 1 ≤ 1 := by exact Preorder.le_trans (ringKrullDim (R ⧸ Ideal.span {x}) + 1) (ringKrullDim R) 1 this translation
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
         [DimensionLEOne R]
         {K : Type v}
         [Field K]
         [Algebra R K]
         [IsDomain R]
         [m : IsFractionRing R K] in
noncomputable
def orderOfVanishing (x : Kˣ) : ℤ := by

  let thing := m.surj' x.1
  /-
  This choice sort of makes sense in the sense that fractions do not uniquely determine elements,
  however we ought to have some canonical form for elements of the function field to take corresponding
  to killing off all common factors, right?

  I think irreducible fractions require a UFD, so this might be the best we have. In that case,
  we may need to prove that this is indeed well defined (we would probably need to do that anyway
  tbh).

  It
  -/

  -- use IsLocalization.sec
  --#check IsLocalization.sec (nonZeroDivisors R) K
  #check IsFractionRing
  choose frac hfrac using thing

  have : frac.1 ∈ nonZeroDivisors R := sorry
  --have ex2 : ∃ b : ℕ, orderOfVanishing' R frac.2 = b := sorry
  --choose a ha using (orderOfVanishing'_finite R ⟨frac.1, this⟩)
  --choose b hb using (orderOfVanishing'_finite R frac.2)
  let a := WithTop.untop (orderOfVanishing' R frac.1) (by sorry)
  let b := WithTop.untop (orderOfVanishing' R frac.2) (by sorry)
  exact (a : ℤ) - (b : ℤ)

/-
Again, we probably need to be slightly careful about this Order.coheight here, but potentially
it's fine since we're talking about integral schemes.
-/
def orderOfVanishingScheme {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  (f : X.functionField) (Z : X) (hZ : Order.coheight Z = 1) : ℤ :=

  sorry

/-
I'm not enitrely sure if this works or not. I think since we're working on an intetgral scheme,
we really should have that there is no mixing of dimension and this should work fine
-/
noncomputable
def div {X : Scheme.{u}} [IsIntegral X] [h : IsLocallyNoetherian X]
  (f : X.functionField) : AlgebraicCycle X where
    toFun Z := if h : Order.coheight Z = 1 then orderOfVanishingScheme f Z h else 0
    supportWithinDomain' := by simp
    supportLocallyFiniteWithinDomain' := sorry

    /-locfin := by
      have := h.1

      /-
      Stacks project 31.26.4

      Note that we need X locally Noetherian for local finiteness
      -/
      sorry-/


/-
noncomputable
def cycleUnion {ι : Type*} {B : ι → Scheme} (f : (i : ι) → AlgebraicCycle (B i)) :
  AlgebraicCycle (∐ B) where
    toFun :=
      have : (∐ B).toPresheafedSpace.carrier.carrier =
             Σ i : ι, (B i).toPresheafedSpace.carrier.carrier := by
        --refine type_eq_of_heq ?_

        sorry

      --rw[this]

      this ▸ (fun ⟨i, z⟩ ↦ (f i) z)

    supportWithinDomain' := by simp
    supportLocallyFiniteWithinDomain' := sorry-/

/-
noncomputable
def principalCycle {ι : Type*} (B : ι → Scheme) (hB : ∀ i : ι, IsIntegral (B i))
  (hB' : ∀ i : ι, IsLocallyNoetherian (B i)) (W : (i : ι) → B i ⟶ X)
  (f : (i : ι) → (B i).functionField) : AlgebraicCycle X :=
    let m : (∐ B) ⟶ X := Limits.Sigma.desc W
    let D : AlgebraicCycle (∐ B) := cycleUnion (fun i ↦ div (f i))
    map m D
    --(fun i : ι ↦ cycleMap (W i) (div (f i))) --(by sorry)-/


/-
Ok this might require some thought. So we're trying to do something similar do our definition of map,
but with the added complication that not only are we taking the pullback along some quasifinite map,
but we're summing up a locally finite family as well.

Ok, so our hW assumption says there is some neighbourhood of our point z which only hits the
pushforward of finitely many of our principal divisors. So we just take that finite set of things
that are hit in a neighbourhood around the point and sum over that.


We now have a definition which makes some choice. Of course, it shouldn't depend on that choice,
but nevertheless it would probably have better definitional properties to take U to just be the
intersection of {z} with our family we're saying is locally finite. This is finite precisley
because of this choice argument below, but we have much better control over the set itself.
-/

def singletonFinite {ι : Type*} (B : ι → Scheme) (δₓ : X → ℤ) [dimensionFunction δₓ]
    (δ : (i : ι) → B i → ℤ) [∀ i, dimensionFunction (δ i)]
    (hB : ∀ i : ι, IsIntegral (B i))
    (hB' : ∀ i : ι, IsLocallyNoetherian (B i)) (W : (i : ι) → B i ⟶ X) [∀ i, QuasiCompact (W i)]
    (f : (i : ι) → (B i).functionField)
    (hW : LocallyFinite (fun i : ι ↦ (map (δ i) δₓ (W i) (div (f i))).support)) (z : X):
    {i : ι | ((map (δ i) δₓ (W i) (div (f i))).support ∩ {z}).Nonempty}.Finite := by
  choose U hU using hW z
  have : {z} ⊆ U := by sorry
  have : {i | (Function.locallyFinsuppWithin.support (map (δ i) δₓ (W i) (div (f i))) ∩ {z}).Nonempty} ⊆
      {i | ((fun i ↦ Function.locallyFinsuppWithin.support (map (δ i) δₓ (W i) (div (f i)))) i ∩ U).Nonempty} := by
    simp[this]
    intro k l

    sorry
  exact Finite.subset hU.2 this




    -- Should be obvious from here, since the intersection with U is known to have the desired
    -- property

   --{Y : Scheme} (f : X ⟶ Y) (c : AlgebraicCycle X) (z : Y) : Set X :=
  --f.base ⁻¹' {z} ∩ c.support

noncomputable
  def principalCycle {ι : Type*} (B : ι → Scheme) (δₓ : X → ℤ) [dimensionFunction δₓ]
    (δ : (i : ι) → B i → ℤ) [∀ i, dimensionFunction (δ i)]
    (hB : ∀ i : ι, IsIntegral (B i))
    (hB' : ∀ i : ι, IsLocallyNoetherian (B i)) (W : (i : ι) → B i ⟶ X) [∀ i, QuasiCompact (W i)]
    (f : (i : ι) → (B i).functionField)
    (hW : LocallyFinite (fun i : ι ↦ (map (δ i) δₓ (W i) (div (f i))).support))
  : AlgebraicCycle X where
    toFun z :=
      ∑ i ∈ (singletonFinite B δₓ δ hB hB' W f hW z).toFinset, (∑ x ∈ (preimageSupportFinite (W i) (div (f i)) z).toFinset, mapAux (δ i) δₓ (W i) x)
    supportWithinDomain' := by simp
    supportLocallyFiniteWithinDomain' := sorry

structure LocallyFiniteClosedFamily (ι : Type*) where
  B : ι → Scheme
  hB : ∀ i : ι, IsIntegral (B i)
  hB' : ∀ i : ι, IsLocallyNoetherian (B i)
  W : (i : ι) → B i ⟶ X
  hW' : LocallyFinite (fun i : ι ↦ _root_.closure (Set.range (W i).base.hom.toFun))
  f : (i : ι) → (B i).functionField
/-
This is a fairly stupid way to say two cycles are rationally equivalent, but nevertheless
-/
noncomputable
def rationallyEquivalent (D₁ D₂ : AlgebraicCycle X) : Prop :=
  ∃ ι, ∃ F : LocallyFiniteClosedFamily ι, D₁ - D₂ = principalCycle F.B F.hB F.hB' F.W F.f

theorem equiv_of_ratEquiv : IsEquiv (AlgebraicCycle X) (rationallyEquivalent (X := X)) where
  refl := sorry
  trans := sorry
  symm := sorry

#check IsEquiv
/-
We need some way of talking about locally finite families of algebraic
cycles to make the previous definition sensible
-/



end AlgebraicCycle
