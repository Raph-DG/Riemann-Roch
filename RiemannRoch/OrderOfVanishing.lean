import Mathlib
import RiemannRoch.NewModuleLength
import Batteries.Tactic.ShowUnused



open Filter Metric Real Set Topology

open AlgebraicGeometry
open CategoryTheory
open Opposite.op
open Module
open Order
open Ring

universe u v
variable (R : Type v)
         [CommRing R]
         (i : ℕ)
         (X : Scheme)

#check Function.locallyFinsuppWithin
/-
theorem supportDiscreteWithin_iff_locallyFiniteWithin {U : Set X}
   {f : X → ℤ} (h : f.support ⊆ U) :
    f =ᶠ[codiscreteWithin U] 0 ↔ ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support) := by
  have : f.support = (U \ {x | f x = (0 : X → ℤ) x}) := by
    ext x
    simp only [Function.mem_support, ne_eq, Pi.zero_apply, mem_diff, mem_setOf_eq, iff_and_self]
    exact (h ·)
  rw [EventuallyEq, Filter.Eventually]--, codiscreteWithin_iff_locallyFiniteComplementWithin, this]

  sorry-/






/-
We define a preorder instance on a scheme X saying x ≤ y if y generalises x. This ought to
correspond to x ≤ y ↔ closure {x} ⊆ closure {y},
-/
instance {X : Scheme} : Preorder X where
  le x y := y ⤳ x --U ∈ _root_.closure {V}
  le_refl := by
    exact fun a ⦃U⦄ a ↦ a
    /-intro a
    simp_all only
    exact Specializes.mem_closure fun ⦃U⦄ a ↦ a-/
  le_trans := by
    exact fun a b c a_1 a_2 ⦃U⦄ a ↦ a_2 (a_1 a)
    /-intro a b c d e
    simp_all
    aesop-/

/-
Note that an algebraic cycle needs to be equidimensional, which is why I went back to defining
the graded pieces like this.

As of right now, I'm not sure if it's better to have this definition and to define CH^i(X)
separately or just to define CH^i now.
-/
structure AlgebraicCycle (X : Scheme) where
  toFun : X → ℤ
  locfin : LocallyFinite (fun z : X ↦ if toFun z = 0 then ∅ else closure {z}) -- {Z | n Z ≠ 0} is locally finite
  --equidim (Z : X) : toFun Z ≠ 0 → Order.coheight Z = i

namespace AlgebraicCycle

variable {X}

variable {i} in


protected def addSubgroup : AddSubgroup (X → ℤ) where
  carrier := {f | LocallyFinite (fun z : X ↦ if f z = 0 then ∅ else closure {z})} --∧ ∀ Z : X, f Z ≠ 0 → Order.coheight Z = i}
  add_mem' {f g} hf hg := by
    simp_all[LocallyFinite]
    --constructor
    intro x
    obtain ⟨Uf, hUf⟩ := hf x
    obtain ⟨Ug, hUg⟩ := hg x

    use Uf ∩ Ug
    constructor
    · exact Filter.inter_mem hUf.1 hUg.1
    · have h : {i | ((if f i + g i = 0 then ∅ else _root_.closure {i}) ∩ (Uf ∩ Ug)).Nonempty} ⊆
              {i | ((if f i = 0 then ∅ else _root_.closure {i}) ∩ Uf ∪ (if g i = 0 then ∅ else
              _root_.closure {i}) ∩ Ug).Nonempty} := by
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

      suffices {i | ((if f i = 0 then ∅ else _root_.closure {i})
      ∩ Uf ∪ (if g i = 0 then ∅ else _root_.closure {i}) ∩ Ug).Nonempty}.Finite by
        exact Set.Finite.subset this h

      suffices {i | ((if f i = 0 then ∅ else _root_.closure {i}) ∩ Uf).Nonempty}.Finite ∧
              {i | ((if g i = 0 then ∅ else _root_.closure {i}) ∩ Ug).Nonempty}.Finite by
        simp_all
        exact Set.Finite.union this.1 this.2
      exact ⟨hUf.2, hUg.2⟩
    /-
    · intro Z hZ
      replace hg := hg.2 Z
      replace hf := hf.2 Z
      have : f Z ≠ 0 ∨ g Z ≠ 0 := by
        by_cases o : f Z = 0
        all_goals simp_all

      obtain h | h := this
      · exact hf h
      · exact hg h-/
  zero_mem' := by
    simp
    intro x
    use ⊤
    all_goals simp
  neg_mem' {f} hf := by simp_all

variable {i}

instance : FunLike (AlgebraicCycle X) X ℤ where
  coe D := D.toFun
  coe_injective' := fun ⟨_, _⟩ ⟨_, _⟩ ↦ by simp

@[ext]
lemma ext {D₁ D₂ : AlgebraicCycle X} (h : ∀ a, D₁ a = D₂ a) : D₁ = D₂ := DFunLike.ext _ _ h

lemma coe_injective : Function.Injective (· : AlgebraicCycle X → X → ℤ) := DFunLike.coe_injective

protected lemma memAddSubgroup (D : AlgebraicCycle X) :
    (D : X → ℤ) ∈ AlgebraicCycle.addSubgroup := D.locfin --⟨D.locfin, D.equidim⟩

@[simps]
def mk_of_mem  (f : X → ℤ) (hf : f ∈ AlgebraicCycle.addSubgroup) : AlgebraicCycle X :=
  ⟨f, hf⟩ --, hf.2⟩

instance : Zero (AlgebraicCycle X) where
  zero := mk_of_mem 0 <| zero_mem _

instance : Add (AlgebraicCycle X) where
  add D₁ D₂ := mk_of_mem (D₁ + D₂) <| add_mem D₁.memAddSubgroup D₂.memAddSubgroup

instance : Neg (AlgebraicCycle X) where
  neg D := mk_of_mem (-D) <| neg_mem D.memAddSubgroup

instance : Sub (AlgebraicCycle X) where
  sub D₁ D₂ := mk_of_mem (D₁ - D₂) <| sub_mem D₁.memAddSubgroup D₂.memAddSubgroup

instance : SMul ℕ (AlgebraicCycle X) where
  smul n D := mk_of_mem (n • D) <| nsmul_mem D.memAddSubgroup n

instance : SMul ℤ (AlgebraicCycle X) where
  smul n D := mk_of_mem (n • D) <| zsmul_mem D.memAddSubgroup n

@[simp] lemma coe_zero : ((0 : AlgebraicCycle X) : X → ℤ) = 0 := rfl
@[simp] lemma coe_add (D₁ D₂ : AlgebraicCycle X) : (↑(D₁ + D₂) : X → ℤ) = D₁ + D₂ := rfl
@[simp] lemma coe_neg (D : AlgebraicCycle X) : (↑(-D) : X → ℤ) = -(D : X → ℤ) := rfl
@[simp] lemma coe_sub (D₁ D₂ : AlgebraicCycle X) : (↑(D₁ - D₂) : X → ℤ) = D₁ - D₂ := rfl
@[simp] lemma coe_nsmul (D : AlgebraicCycle X) (n : ℕ) : (↑(n • D) : X → ℤ) = n • (D : X → ℤ) := rfl
@[simp] lemma coe_zsmul (D : AlgebraicCycle X) (n : ℤ) : (↑(n • D) : X → ℤ) = n • (D : X → ℤ) := rfl

instance : AddCommGroup (AlgebraicCycle X) :=
  Function.Injective.addCommGroup (M₁ := AlgebraicCycle X) (M₂ := X → ℤ)
    _ coe_injective coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

instance : LE (AlgebraicCycle X) where
  le := fun D₁ D₂ ↦ (D₁ : X → ℤ) ≤ D₂

lemma le_def {D₁ D₂ : AlgebraicCycle X} : D₁ ≤ D₂ ↔ (D₁ : X → ℤ) ≤ (D₂ : X → ℤ) := ⟨(·),(·)⟩

instance : LT (AlgebraicCycle X) where
  lt := fun D₁ D₂ ↦ (D₁ : X → ℤ) < D₂

instance : Max (AlgebraicCycle X) where
  max D₁ D₂ := {
    toFun z := max (D₁ z) (D₂ z)
    locfin := by
      intro x
      obtain ⟨U₁, hU₁⟩ := D₁.locfin x
      obtain ⟨U₂, hU₂⟩ := D₂.locfin x
      use U₁ ∩ U₂
      constructor
      · exact Filter.inter_mem hU₁.1 hU₂.1
      · /-
        This shows that this exact same proof works for +, ⊓ and ⊔. I suppose what we're using here
        is that f(D₁ i, D₂ i) ≠ 0 implies D₁ i ≠ 0 or D₂ i ≠ 0.
        -/
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

        exact ⟨hU₁.2, hU₂.2⟩
    /-equidim := by
      intro Z hZ
      simp at hZ
      by_cases o : D₁ Z ⊔ D₂ Z = D₁ Z
      · rw[o] at hZ
        exact D₁.equidim Z hZ
      · simp at o
        have : D₁ Z ⊔ D₂ Z = D₂ Z := by exact max_eq_right_of_lt o
        rw[this] at hZ
        exact D₂.equidim Z hZ-/
  }

@[simp]
lemma max_apply {D₁ D₂ : AlgebraicCycle X} {x : X} : max D₁ D₂ x = max (D₁ x) (D₂ x) := rfl

instance : Min (AlgebraicCycle X) where
  min D₁ D₂ := {
    toFun z := min (D₁ z) (D₂ z)
    locfin :=
    by
      intro x
      obtain ⟨U₁, hU₁⟩ := D₁.locfin x
      obtain ⟨U₂, hU₂⟩ := D₂.locfin x
      use U₁ ∩ U₂
      constructor
      · exact Filter.inter_mem hU₁.1 hU₂.1
      · simp_all
        have h : {i | ((if D₁ i ⊓ D₂ i = 0 then ∅ else _root_.closure {i}) ∩ (U₁ ∩ U₂)).Nonempty} ⊆
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

        exact ⟨hU₁.2, hU₂.2⟩
    /-equidim := by
      intro Z hZ
      simp at hZ
      by_cases o : D₁ Z ⊓ D₂ Z = D₁ Z
      · rw[o] at hZ
        exact D₁.equidim Z hZ
      · simp at o
        have : D₁ Z ⊓ D₂ Z = D₂ Z := by exact min_eq_right_of_lt o
        rw[this] at hZ
        exact D₂.equidim Z hZ-/
  }

@[simp]
lemma min_def {D₁ D₂ : AlgebraicCycle X} {x : X} : min D₁ D₂ x = min (D₁ x) (D₂ x) := rfl

instance : Lattice (AlgebraicCycle X) where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := by simp [le_def]
  le_trans D₁ D₂ D₃ h₁₂ h₂₃ := fun x ↦ (h₁₂ x).trans (h₂₃ x)
  le_antisymm D₁ D₂ h₁₂ h₂₁ := by
    ext x
    exact Int.le_antisymm (h₁₂ x) (h₂₁ x)
  sup := max
  le_sup_left D₁ D₂ := fun x ↦ by simp
  le_sup_right D₁ D₂ := fun x ↦ by simp
  sup_le D₁ D₂ D₃ h₁₃ h₂₃ := fun x ↦ by simp [h₁₃ x, h₂₃ x]
  inf := min
  inf_le_left D₁ D₂ := fun x ↦ by simp
  inf_le_right D₁ D₂ := fun x ↦ by simp
  le_inf D₁ D₂ D₃ h₁₃ h₂₃ := fun x ↦ by simp [h₁₃ x, h₂₃ x]

instance : OrderedAddCommGroup (AlgebraicCycle X) where
  __ := inferInstanceAs (AddCommGroup (AlgebraicCycle X))
  __ := inferInstanceAs (Lattice (AlgebraicCycle X))
  add_le_add_left := fun _ _ _ _ ↦ by simpa [le_def]


/-
  Points here are just a proxy for irreducible closeds, so this isn't quite what we want. I think
  this definition here is a little bit silly, but taking the closure of the union also seems kind
  of strange.
-/
abbrev support (D : AlgebraicCycle X) :=
    ⋃ (z : X), if D.toFun z = 0 then ∅ else _root_.closure {z}

theorem support_closed {i : ℕ} {X : Scheme} (D : AlgebraicCycle X) :
    IsClosed (D.support) := by
  simp[AlgebraicCycle.support]
  have := D.2
  apply LocallyFinite.isClosed_iUnion
  · exact this
  · intro x
    split_ifs
    · exact isClosed_empty
    · exact isClosed_closure


/-
This is the algebraic cycle of a point (thought of as having the canonical reduced scheme
structure and hence having multiplicity 1)
-/
open Classical in
noncomputable
def of_point (x : X) (hx : coheight x = i) : AlgebraicCycle X where
  toFun := fun z ↦ if z = x then 1 else 0
  locfin := by
    simp[LocallyFinite]
    intro z
    use ⊤
    constructor
    · exact Filter.univ_mem' fun a ↦ trivial
    · simp
      have : {i | (if i = x then _root_.closure {i} else ∅).Nonempty} = {x} := by aesop
      rw[this]
      aesop



noncomputable
def _root_.AlgebraicGeometry.LocallyRingedSpace.Hom.residueMap {X Y : LocallyRingedSpace} (f : X.Hom Y)
  (x : ↑X.toTopCat) :
    IsLocalRing.ResidueField (Y.presheaf.stalk (f.base x)) →+*
    IsLocalRing.ResidueField (X.presheaf.stalk x) :=
  IsLocalRing.ResidueField.lift (RingHom.comp (IsLocalRing.residue (X.presheaf.stalk x))
   (AlgebraicGeometry.LocallyRingedSpace.Hom.stalkMap f x).hom)


open AlgebraicGeometry
open LocallyRingedSpace
open Order
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
  locfin := by
    sorry



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
    locfin := by
      have := h.1

      /-
      Stacks project 31.26.4

      Note that we need X locally Noetherian for local finiteness
      -/
      sorry



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
    locfin := sorry


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
