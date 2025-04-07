import Mathlib
import RiemannRoch.NewModuleLength
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

/-
We define a preorder instance on a scheme X saying x ≤ y if y generalises x. This ought to
correspond to x ≤ y ↔ closure {x} ⊆ closure {y},
-/
instance {X : Scheme} : Preorder X := specializationPreorder X /-where
  le x y := y ⤳ x
  le_refl := by
    exact fun a ⦃U⦄ a ↦ a
  le_trans := by
    exact fun a b c a_1 a_2 ⦃U⦄ a ↦ a_2 (a_1 a)-/

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

def preimageSupportFinite {Y : Scheme} (f : X ⟶ Y) [qf : QuasiCompact f] (c : AlgebraicCycle X)
  (z : Y) : (preimageSupport f c z).Finite := by
  have cpct : IsCompact (f.base ⁻¹' {z}) := by exact QuasiCompact.isCompact_preimage_singleton f z
  rw[isCompact_iff_finite_subcover] at cpct
  let cov : f.base ⁻¹' {z} → Set X := sorry
  let covOpen : (∀ (i : ↑(⇑(ConcreteCategory.hom f.base) ⁻¹' {z})), IsOpen (cov i)) := sorry
  let covCovs : ⇑(ConcreteCategory.hom f.base) ⁻¹' {z} ⊆ ⋃ i, cov i := sorry
  specialize cpct cov covOpen covCovs


  /-
  Proof:
    We want to say that the preimage of z is compact using our compactness assumption. Then, for
    every point in the preimage, take some neighbourhood intersecting c.support in finitely
    many places. This forms a cover of the preimage of z, and so by assumption there is some
  -/
  simp[preimageSupport, Function.locallyFinsuppWithin.support]




  sorry

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
-- k function

open Classical in
noncomputable
def mapAux {Y : Scheme} (δₓ : X → ℤ) [dimensionFunction δₓ]
  (δₐy : Y → ℤ) [dimensionFunction δₐy] (f : X ⟶ Y) (x : X) : ℤ :=
  if δₓ x = δₐy (f.base x) then Hom.degree f x else 0


open Classical in
noncomputable
def cycleMap {Y : Scheme} (δₓ : X → ℤ) [dimensionFunction δₓ] (δₐy : Y → ℤ) [dimensionFunction δₐy]
  (f : X ⟶ Y) [QuasiCompact f] (c : AlgebraicCycle X) : AlgebraicCycle Y where
  toFun z := (∑ x ∈ (preimageSupportFinite f c z).toFinset, mapAux δₓ δₐy f x)
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' := sorry -- Should be a relatively simple topological argument


  --IsLocalRing.ResidueField.lift (RingHom.comp (IsLocalRing.residue (X.presheaf.stalk x))
   --(AlgebraicGeometry.LocallyRingedSpace.Hom.stalkMap f x).hom)


/-
open Classical in
noncomputable
def cycleMap {Y : Scheme} (f : X ⟶ Y) (c : AlgebraicCycle X) : AlgebraicCycle Y where
  toFun := by
    intro z
    by_cases o : ∃ x, z = f.base x
    · choose x hx using o
      by_cases l : coheight z = coheight x
      · exact (@Module.finrank (IsLocalRing.ResidueField (Y.presheaf.stalk (f.base x)))
              (IsLocalRing.ResidueField (X.presheaf.stalk x))
              (by infer_instance)
              (by infer_instance)
              (by have :=
               RingHom.toAlgebra (AlgebraicGeometry.LocallyRingedSpace.Hom.residueMap f.toLRSHom x);
                  exact Algebra.toModule)).cast
      · exact 0
    · exact 0
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' := sorry-/



variable {R} in
def quotientSequence (a b : nonZeroDivisors R) : CategoryTheory.ShortComplex (ModuleCat R) where
  X₁ := ModuleCat.of R (R ⧸ (Ideal.span {a.1}))
  X₂ := ModuleCat.of R (R ⧸ (Ideal.span {a.1*b.1}))
  X₃ := ModuleCat.of R (R ⧸ (Ideal.span {b.1}))
  f :=
    let fl : R ⧸ (Ideal.span {a.1}) →ₗ[R] R ⧸ (Ideal.span {a.1*b.1}) :=
      let f : R →ₗ[R] R ⧸ (Ideal.span {a.1*b.1}) :=
        Submodule.mkQ (Ideal.span {a.1 * b.1}) ∘ₗ
        IsLinearMap.mk' (fun r : R ↦ b.1 * r) (IsLinearMap.isLinearMap_smul b.1)
      have hf : Ideal.span {a.1} ≤ LinearMap.ker f := sorry
      Submodule.liftQ (Ideal.span {a.1}) f hf
    ModuleCat.ofHom fl
  g := sorry
  zero := sorry
variable {R} in
theorem quotientSequence_exact (a b : nonZeroDivisors R) : (quotientSequence a b).ShortExact := sorry

noncomputable
def orderOfVanishing' (x : nonZeroDivisors R) := Module.length R (R ⧸ Ideal.span {x.1})

theorem orderOfVanishing'_additive (a b : nonZeroDivisors R) :
  orderOfVanishing' R (a*b) = orderOfVanishing' R a + orderOfVanishing' R b :=
   Module.length_additive <| quotientSequence_exact a b

theorem orderOfVanishing'_finite' [IsNoetherianRing R]
         [IsLocalRing R] [IsDomain R]
         [DimensionLEOne R] (x : nonZeroDivisors R) : IsFiniteLength R (R ⧸ Ideal.span {x.1}) := by

  rw[isFiniteLength_iff_isNoetherian_isArtinian]
  constructor
  · obtain ⟨val, property⟩ := x
    simp_all only
    simp_all only [mem_nonZeroDivisors_iff_ne_zero, ne_eq]
    exact isNoetherian_quotient (Ideal.span {val})
  · obtain ⟨val, property⟩ := x
    simp_all only
    simp_all only [mem_nonZeroDivisors_iff_ne_zero, ne_eq]
    #check IsField
    by_cases o : IsField R
    · have : Ideal.span {val} = R := by sorry
      have : (0 : R ⧸ Ideal.span {val}) = 1 := by sorry


      sorry
    · /-
      R has dimension 1
      have : dim (R ⧸ Ideal.span {val}) = dim R - 1
      dim = 0 therefore artinian
      -/

      sorry
    /-
    If R has dimension 0, this follows since a dimension 0 noetherian ring is artinian and hence
    has finite length, and so because lengths are additive we get that I and R/I are also finite
    length as R modules. Note that since R is a domain, if it had dimension 0 it would be a field

    If R has dimension 1, we know that since R is a domain and x is non-zero that
    dim (R ⧸ x) = dim R - 1. So, we then have that dim (R ⧸ x) = 0, and Bob's your uncle.
    -/

/-
This is true by some module length API that will be added very soon
-/
theorem orderOfVanishing'_finite [IsNoetherianRing R]
         [IsLocalRing R]
         [DimensionLEOne R] (x : nonZeroDivisors R) :
    ∃ a : ℕ, orderOfVanishing' R x = a := by
  sorry

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
  choose frac hfrac using thing
  have : frac.1 ∈ nonZeroDivisors R := sorry
  have ex2 : ∃ b : ℕ, orderOfVanishing' R frac.2 = b := sorry
  choose a ha using (orderOfVanishing'_finite R ⟨frac.1, this⟩)
  choose b hb using (orderOfVanishing'_finite R frac.2)
  exact (a : ℤ) - (b : ℤ)

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
    supportLocallyFiniteWithinDomain' := sorry


noncomputable
def principalCycle {ι : Type*} (B : ι → Scheme) (hB : ∀ i : ι, IsIntegral (B i))
  (hB' : ∀ i : ι, IsLocallyNoetherian (B i)) (W : (i : ι) → B i ⟶ X)
  (f : (i : ι) → (B i).functionField) : AlgebraicCycle X :=
    let m : (∐ B) ⟶ X := Limits.Sigma.desc W
    let D : AlgebraicCycle (∐ B) := cycleUnion (fun i ↦ div (f i))
    cycleMap m D
    --(fun i : ι ↦ cycleMap (W i) (div (f i))) --(by sorry)



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




variable {R} in
def quotientSequence (a b : nonZeroDivisors R) : CategoryTheory.ShortComplex (ModuleCat R) where
  X₁ := ModuleCat.of R (R ⧸ (Ideal.span {a.1}))
  X₂ := ModuleCat.of R (R ⧸ (Ideal.span {a.1*b.1}))
  X₃ := ModuleCat.of R (R ⧸ (Ideal.span {b.1}))
  f :=
    let fl : R ⧸ (Ideal.span {a.1}) →ₗ[R] R ⧸ (Ideal.span {a.1*b.1}) :=
      let f : R →ₗ[R] R ⧸ (Ideal.span {a.1*b.1}) :=
        Submodule.mkQ (Ideal.span {a.1 * b.1}) ∘ₗ
        IsLinearMap.mk' (fun r : R ↦ b.1 * r) (IsLinearMap.isLinearMap_smul b.1)
      have hf : Ideal.span {a.1} ≤ LinearMap.ker f := sorry
      Submodule.liftQ (Ideal.span {a.1}) f hf
    ModuleCat.ofHom fl
  g := sorry
  zero := sorry

variable {R} in
theorem quotientSequence_exact (a b : nonZeroDivisors R) : (quotientSequence a b).ShortExact := sorry

variable [IsNoetherianRing R]
         [IsLocalRing R]
         [DimensionLEOne R]
         --(hR : ∃ r : R, ∀ s : R, r * s ≠ 1)
        -- #check Ideal.isMaximal
         (hR : (0 : Ideal R).IsPrime)
         -- We have that dimension is ≤ 1 now (meaning all primes are maximal), but we also need that
         -- this maximal ideal is not the zero ring, i.e. that we really do have a chain 0 < m,
         -- i.e. that R is not a field. Indeed, we could just mandate that we have some non trivial
         -- maximal ideal.

         /-
         Actually, note that the above reasoning is wrong. To see this, note that if 0 is not prime,
         then we won't have such a prime. This happens if m is composed of nilpotents.
         -/

         {K : Type v}
         [Field K]
         [Algebra R K]
         [IsDomain R]
         [m : IsFractionRing R K]


noncomputable
def orderOfVanishing' (x : nonZeroDivisors R) := Module.length R (R ⧸ Ideal.span {x.1})

/-
So this, I think, will change with the change to the module length API (we also need to change
around some of the assumptions made about the ring R).
-/
theorem orderOfVanishing'_additive (a b : nonZeroDivisors R) :
  orderOfVanishing' R (a*b) = orderOfVanishing' R a + orderOfVanishing' R b :=
   Module.length_additive <| quotientSequence_exact a b


/-
Note that in our context, we actually know these lengths are finite, so we just need to have that
written here
-/

theorem orderOfVanishing'_finite (x : nonZeroDivisors R) :
    ∃ a : ℕ, orderOfVanishing' R x = a := by
  -- This is nontrivial and will require a fair bit more stuff
  sorry



/-
This is a mildly strange definition of the order of vanishing. It should be correct, but using
choice 3 times doesn't give me much hope that it will be usable, and I'd also prefer not to
have the definition made in tactic mode.

It might be better for definition's sake to just have this be defined unconditionally as an
integer (and it outputs e.g. 0 if it's infinite), then to have a theorem saying that we get nice
results when we have good rings.
-/
noncomputable
def orderOfVanishing (x : Kˣ) : ℤ := by
  let thing := m.surj' x.1
  choose frac hfrac using thing
  have : frac.1 ∈ nonZeroDivisors R := sorry
  have ex2 : ∃ b : ℕ, orderOfVanishing' R frac.2 = b := sorry
  choose a ha using (orderOfVanishing'_finite R ⟨frac.1, this⟩)
  choose b hb using (orderOfVanishing'_finite R frac.2)
  exact (a : ℤ) - (b : ℤ)
/-
At this point we have a definition of the order of vanishing as a function into ℤ, which should be
enough to define principal divisors.
-/


/-
This shows that the map Kˣ → Div X is a homomorphism of groups, meaning that principal divisors
form a group (this will be easy once we acrually have a sensible definition of order of vanishing)
-/
theorem orderOfVanishing_additive (f g : Kˣ) :
  orderOfVanishing R (f*g) = orderOfVanishing R f + orderOfVanishing R g := sorry


instance NoetherianLocal [IsNoetherian X] (x : X) : IsNoetherianRing (X.presheaf.stalk x) := sorry

-- The definition given should work once I refactor things to be relying less on assumptions about
-- the underlying ring
noncomputable
def order [IsIntegral X] [IsNoetherian X] (f : X.functionField) (x : X) : ℤ := sorry
  --orderOfVanishing (X.presheaf.stalk x) f


/-
Here we can define the graded pieces of the Chow group of a scheme (or here just a topological
space) by taking the free abelian group on irreducible closed subsets of codimension i.

This is mainly for generality's sake - here we can hopefully port over what we develop about
Weil divisors to equally apply in the case of, e.g. Riemann surfaces, where we don't have (or at
least it's not totally natural to use the language of) a scheme structure. Note that by the work on
ideal sheaves by Andrew, we can recover the scheme structure whenever we want since we just take
the structure sheaf to be the corresponding ideal sheaf.
-/
structure PrimeCycle (i : ℕ) (X : Type*) [TopologicalSpace X] where
  space : TopologicalSpace.IrreducibleCloseds X
  codim : Order.coheight space = i -- The coheight here is a way of computing the codimension of our space



/-
Note the order of vanishing is only finite for a dimension 1 Noetherian local ring (or at least
that's the most general result we're using).
-/
def orderOfVanishingScheme {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  (f : X.functionField) (Z : X) (hZ : Order.coheight Z = 1) : ℤ :=

  sorry
  --orderOfVanishing (X.presheaf.stalk Z) f
  /-
  We want the above definition
  -/


/-
I think we should have some function like this, but it's unclear to me exactly what the signature
should be since we sometimes don't want to combine algebraic cycles on the nose, but combine
functions X → ℤ satisfying the various constraints of a cycle.
-/
def combine (f : ℤ → ℤ → ℤ) (hf : ∀ z w, f z w ≠ 0 → z ≠ 0 ∨ w ≠ 0) (D₁ D₂ : AlgebraicCycle X) :
  AlgebraicCycle X where
    toFun := sorry
    locfin := sorry
    --equidim := sorry
    /-
    This shows that this exact same proof works for +, ⊓ and ⊔. I suppose what we're using here
    is that f(D₁ i, D₂ i) ≠ 0 implies D₁ i ≠ 0 or D₂ i ≠ 0.
    -/
    /-
    simp_all
    have h : {i | ((if D₁ i ⊔ D₂ i = 0 then ∅ else _root_.closure {i}) ∩ (U₁ ∩ U₂)).Nonempty} ⊆
            {i | ((if D₁ i = 0 then ∅ else _root_.closure {i}) ∩ U₁ ∪ (if D₂ i = 0 then ∅ else
            _root_.closure {i}) ∩ U₂).Nonempty} := by
      simp_all
      intro a ha
      split_ifs at ha
      · aesop
      · split_ifs
        · simp_all
        · simp_all[Set.Nonempty]
          obtain ⟨t, ht⟩ := ha
          exact ⟨t, ht.1, ht.2.2⟩
        · simp_all[Set.Nonempty]
          obtain ⟨t, ht⟩ := ha
          exact ⟨t, ht.1, ht.2.1⟩
        · simp_all[Set.Nonempty]
          obtain ⟨t, ht⟩ := ha
          exact Or.inl ⟨t, ht.1, ht.2.1⟩

    suffices {i | ((if D₁ i = 0 then ∅ else _root_.closure {i})
    ∩ U₁ ∪ (if D₂ i = 0 then ∅ else _root_.closure {i}) ∩ U₂).Nonempty}.Finite by
      exact Set.Finite.subset this h

    suffices {i | ((if D₁ i = 0 then ∅ else _root_.closure {i}) ∩ U₁).Nonempty}.Finite ∧
            {i | ((if D₂ i = 0 then ∅ else _root_.closure {i}) ∩ U₂).Nonempty}.Finite by
      simp_all
      exact Set.Finite.union this.1 this.2

    exact ⟨hU₁.2, hU₂.2⟩-/
