import Mathlib
import RiemannRoch.AlgebraicCycle.Basic
import RiemannRoch.CodimLemma
import RiemannRoch.Misc.LocalFinitenessLemmas
import RiemannRoch.Misc.AffineOpenLemma
import RiemannRoch.Misc.Instances

/-!
# Algebraic Cycles

In this file we define the notion of a `principal` cycle, which is a slightly nonstandard notion
denoting those cycles which witness rational equivalence between two other cycles.
-/

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

namespace AlgebraicCycle

open Multiplicative WithZero

noncomputable
def _root_.AlgebraicGeometry.Scheme.ord {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  {Z : X} (hZ : Order.coheight Z = 1) : X.functionField →*₀ ℤᵐ⁰ :=
  have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk Z) := by
    rw[Ring.krullDimLE_iff, AlgebraicGeometry.stalk_dim_eq_coheight Z]
    simp [hZ.le]
  Ring.ordFrac (X.presheaf.stalk Z)

lemma _root_.AlgebraicGeometry.Scheme.ord_ne_zero {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {Z : X} (hZ : Order.coheight Z = 1) {f : X.functionField} (hf : f ≠ 0) :
  Scheme.ord hZ f ≠ 0 := (map_ne_zero (Scheme.ord hZ)).mpr hf

lemma _root_.AlgebraicGeometry.Scheme.functionField_exists_unit_nhd
    [IsIntegral X] (f : X.functionField) (hf : f ≠ 0) :
    ∃ U : X.Opens, ∃ f' : Γ(X, U), ∃ _ :
    Nonempty U, X.germToFunctionField U f' = f ∧ IsUnit f' := by
  obtain ⟨U, hU, g, hg⟩ := TopCat.Presheaf.germ_exist _ _ f
  refine ⟨AlgebraicGeometry.Scheme.basicOpen X g,
    TopCat.Presheaf.restrict g (AlgebraicGeometry.Scheme.basicOpen_le X g).hom, ?_⟩
  have : Nonempty (X.basicOpen g) := by
    have := basicOpen_eq_bot_iff g
    simp only [Scheme.Opens.nonempty_iff]
    suffices ¬ X.basicOpen g = ⊥ by exact
      (Opens.ne_bot_iff_nonempty (X.basicOpen g)).mp this
    aesop (add simp hf)
  use this
  have := TopCat.Presheaf.germ_res X.presheaf (Scheme.basicOpen_le X g).hom
    (genericPoint X) (Scheme.germToFunctionField._proof_1 X (X.basicOpen g))
  exact ⟨hg ▸ this ▸ rfl, AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen X.toRingedSpace g⟩




open Classical in
noncomputable
def div [IsIntegral X] [IsLocallyNoetherian X]
  (f : X.functionField) (hf : f ≠ 0) : AlgebraicCycle X where
    toFun Z := if h : Order.coheight Z = 1
               then WithZero.unzero (Scheme.ord_ne_zero h hf)
               else 0
    supportWithinDomain' := by simp
    supportLocallyFiniteWithinDomain' := by
      intro z hz
      have : ∃ U : X.Opens, ∃ f' : Γ(X, U), ∃ hU : Nonempty U,
          X.germToFunctionField U f' = f ∧ IsUnit f' := by
        obtain ⟨U, hU, g, hg⟩ := TopCat.Presheaf.germ_exist _ _ f
        use AlgebraicGeometry.Scheme.basicOpen X g
        use TopCat.Presheaf.restrict g (AlgebraicGeometry.Scheme.basicOpen_le X g).hom
        have : Nonempty U := by simp[Set.nonempty_of_mem hU]
        have : Nonempty (X.basicOpen g) := by
          have := basicOpen_eq_bot_iff g
          simp--[Nonempty, basicOpen_eq_bot_iff]
          suffices ¬ X.basicOpen g = ⊥ by exact
            (Opens.ne_bot_iff_nonempty (X.basicOpen g)).mp this
          rw[this]
          rw[← hg] at hf
          aesop (add simp hf)
        use this
        constructor
        · rw[← hg]
          have := TopCat.Presheaf.germ_res X.presheaf (Scheme.basicOpen_le X g).hom (genericPoint X)
              (Scheme.germToFunctionField._proof_1 X (X.basicOpen g))
          rw[← this]
          rfl
        · exact AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen X.toRingedSpace g
      obtain ⟨U, f', hU, hf'⟩ := this
      /-
      We want to say here that the order of vanishing of f is trivial on all points of U.
      This just follows from the order of vanshing being a homomorphism.
      -/
      --have : ∀ y ∈ U, ∀ h : coheight y = 1, _root_.AlgebraicGeometry.Scheme.ord h f = 0 := sorry
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
        · convert finite_empty
          convert inter_empty U.1
          refine Function.support_eq_empty_iff.mpr ?_
          ext a
          split_ifs
          · rename_i m
            simp
            suffices Scheme.ord m f = 1 by aesop
            --rw [← hf'.1]
            simp [Scheme.ord]
            /-
            We now need to construct f's value at the stalk of a and show that it is a unit.
            -/
            have s := IsLocalization.sec_spec (nonZeroDivisors (X.presheaf.stalk a)) f
            have := Scheme.ord._proof_1 m

            have := congr_arg (ordFrac ↑(X.presheaf.stalk a)) s
            simp[ordFrac_eq_ord] at this

            #check ordFrac_eq_ord (X.presheaf.stalk a) (IsLocalization.sec (nonZeroDivisors ↑(X.presheaf.stalk a)) f).2


            --suffices Scheme.ord m f = (↑(↑(0 : ℤ) : Multiplicative ℤ) : ℤₘ₀) by sorry
            --rw[← hf'.1]
            --simp

            sorry
          · rfl

      · let XU := (⊤ : Set X) \ U
        have properClosed : XU ≠ ⊤ ∧ IsClosed XU := sorry

        have (y : X) (h : Order.coheight y = 1)
          (hy : Scheme.ord h f ≠ 0) : closure {y} ⊆ XU :=

          sorry


        let cly (y : X) (h : Order.coheight y = 1)
          (hy : Scheme.ord h f ≠ 0) : Set XU := fun ⟨a, m⟩ ↦ (closure {y} a)

        have (y : X) (h : Order.coheight y = 1)
          (hy : Scheme.ord h f ≠ 0) :
          cly y h hy ∈ irreducibleComponents XU := by
          constructor
          · simp[cly]
            suffices IsIrreducible <| closure {y} by sorry
            exact IsGenericPoint.isIrreducible rfl
          · --intro z hz hz2
            --suffices coheight (cly y h hy) = 0 by aesop
            --rw [@coheight_eq_zero]
            --simp[IsMax]


            --have ch : coheight z ≤ coheight (cly y h hy) := by exact GCongr.coheight_le_coheight z (cly y h hy) hz2

            --have : coheight (cly y h hy) = coheight y := sorry

            /-
            This should be its own argument. The idea is that in order to be a bigger
            irreducbible set, you must increase the dimension and hence must be the whole
            space. But that contradicts the fact that XU is a proper subset.
            -/
            sorry
        /-
        Take an affine nhd of z

        Since z locally Noetherian, this will be a Noetherian space, and hence the
        intersection with XU will have finitely many irreducible components
        -/


        #check TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
        sorry


theorem div_homomorphism [IsIntegral X] [h : IsLocallyNoetherian X]
  (f : X.functionField) (hf : f ≠ 0) (g : X.functionField) (hg : g ≠ 0) :
  div (f * g) (by simp_all) = div f hf + div g hg := by

  ext a
  suffices (div (f*g) (by simp_all)).toFun a = (div f hf).toFun a + (div g hg).toFun a from this
  simp[AlgebraicCycle.div]
  split_ifs
  · rename_i ha


    rw[← WithZero.coe_inj]
    simp only [WithZero.coe_unzero, WithZero.coe_add]

    apply congr
    · simp[instHMul, instHAdd, Mul.mul]
      ext b c
      constructor
      · intro h
        rw[← h]
        simp_all only [ne_eq, Option.map₂_eq_some_iff, Option.mem_def, exists_and_left, Multiplicative.exists,
          toAdd_ofAdd]
        obtain ⟨w, h⟩ := h
        obtain ⟨left, right⟩ := h
        obtain ⟨w_1, h⟩ := right
        obtain ⟨left_1, right⟩ := h
        subst right left_1
        simp_all only [Option.map₂_coe_right, toAdd_ofAdd, Option.map_some]
        rfl
      · intro h
        rw[← h]
        ext m

        sorry

        --rw[← h]
        --apply Eq.symm
        --obtain ⟨w, h⟩ := h
        --obtain ⟨left, right⟩ := h
        --obtain ⟨w_1, h⟩ := right
        --obtain ⟨left_1, right⟩ := h
        --subst right left_1
        --simp_all only [Option.map₂_coe_right, toAdd_ofAdd, Option.map_some]
        --rfl

    · rfl
    --rw [← @MonoidWithZeroHom.map_mul]

    /-simp[WithZero.unzero_coe, WithZero.toMulBot]
    aesop (add simp ofAdd_add)

    apply congr
    · aesop (add simp Multiplicative.toAdd)
      sorry
    · rfl-/
  · rfl


structure LocallyFiniteClosedFamily (X : Scheme.{u}) where
  {ι : Type}
  n : Nonempty ι
  B : ι → Scheme.{u}
  hB : ∀ i : ι, IsIntegral (B i)
  hB' : ∀ i : ι, IsLocallyNoetherian (B i)
  W : (i : ι) → B i ⟶ X
  qcW : ∀ i, QuasiCompact (W i)
  ciW : ∀ i : ι, IsClosedImmersion (W i)
  f : (i : ι) → (B i).functionField
  hf : ∀ i : ι, f i ≠ 0
  hW : LocallyFinite (fun i : ι ↦ (map (W i) (div (f i) (hf i))).support)

def _root_.LocallyFiniteClosedFamily.ofRat [ix : IsIntegral X]
  (g : X.functionField) (hg : g ≠ 0) [iln : IsLocallyNoetherian X] : LocallyFiniteClosedFamily X where
  ι := Fin 1
  n := instNonemptyOfInhabited
  B := fun _ ↦ X
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


variable {ι : Type*} [Nonempty ι] (B : ι → Scheme) (δx : X → ℤ)
    (δ : (i : ι) → B i → ℤ)
    [hB : ∀ i : ι, IsIntegral (B i)]
    [hB' : ∀ i : ι, IsLocallyNoetherian (B i)]
    (W : (i : ι) → B i ⟶ X) [qcW : ∀ i, QuasiCompact (W i)]
    (f : (i : ι) → (B i).functionField) (hf : ∀ i : ι, f i ≠ 0)
    (hW : LocallyFinite (fun i : ι ↦ (map (W i) (div (f i) (hf i))).support))

variable (F : LocallyFiniteClosedFamily X)
include hW in
omit [Nonempty ι] in
theorem singletonFinite (z : X) :
    {i : ι | ((map (W i) (div (f i) (hf i))).support ∩ {z}).Nonempty}.Finite := by
  choose U hU using hW z
  have : {z} ⊆ U := singleton_subset_iff.mpr (mem_of_mem_nhds hU.1)
  have : {i | (Function.locallyFinsuppWithin.support (map (W i) (div (f i) (hf i))) ∩ {z}).Nonempty} ⊆
      {i | ((fun i ↦ Function.locallyFinsuppWithin.support (map (W i) (div (f i) (hf i)))) i ∩ U).Nonempty} := by
    simp only [top_eq_univ, inter_singleton_nonempty, Function.mem_support, ne_eq,
      setOf_subset_setOf]
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
      ∑ i ∈ (singletonFinite B W f hf hW z).toFinset,
      (∑ x ∈ (preimageSupport_finite (W i) (div (f i) (hf i)) z).toFinset,
      (div (f i) (hf i) x) * mapAux (W i) x)
    supportWithinDomain' := by simp
    supportLocallyFiniteWithinDomain' := by
      intro z hz

      /-
      U is a neighbourhood of z which hits finitely many of the subvarieties on which our principal
      cycle is defined
      -/
      obtain ⟨U, hU⟩ := hW z

      /-
      fino constructs a set which intersects div (f i) in finitely many places.
      -/
      let fino (i : ι) := map_locally_finite (W i) (div (f i) (hf i)) --(f i)

      /-
      For each of the subvarieties hit by U, we can construct a nhd fino i z hz hitting div (f i)
      in finitely many places. If we take the intersection of all of these nhds of z we should be
      left with something that hits all of the div (f i) in finitely many places, where i ranges
      over the subvarieties hitting U. We should also make sure to intersect with U, then we get
      that our nhd of z hits the entire support in finitely many places.
      -/
      use (⋂ i ∈ hU.2.toFinset, (fino i z).choose) ∩ U
      constructor
      · apply Filter.inter_mem
        · rw[Finset.iInter_mem_sets]
          intro i hi
          exact (fino i z).choose_spec.1
        · exact hU.1
      · by_cases o : hU.2.toFinset.Nonempty

        · rw[inter_comm, ← inter_assoc]
          apply Set.Finite.inter_of_left
          rw[inter_comm]
          have (i : ι) := (fino i z).choose_spec.2

          have rwl := biInter_inter o (fun i ↦ (fino i z).choose) (Function.support fun z ↦ ∑ i ∈ (singletonFinite B W f hf hW z).toFinset, ∑ x ∈ (preimageSupport_finite (W i) (div (f i) (hf i)) z).toFinset, (div (f i) (hf i)) x * mapAux (W i) x)
          erw [← rwl]

          suffices (⋂ i ∈ hU.2.toFinset, ((fino i z).choose ∩ ⋃ j ∈ (singletonFinite B W f hf hW z).toFinset, Function.support fun z ↦ ∑ x ∈ (preimageSupport_finite (W j) (div (f j) (hf j)) z).toFinset, (div (f j) (hf j)) x * mapAux (W j) x)).Finite by sorry

          suffices (⋃ j ∈ (singletonFinite B W f hf hW z).toFinset, (⋂ i ∈ hU.2.toFinset, ((fino i z).choose) ∩ Function.support fun z ↦ ∑ x ∈ (preimageSupport_finite (W j) (div (f j) (hf j)) z).toFinset, (div (f j) (hf j)) x * mapAux (W j) x)).Finite by sorry

          apply Set.Finite.biUnion
          · sorry
          intro j hj
          specialize this j
          suffices ∃ i ∈ hU.right.toFinset, ((fino i z).choose ∩ Function.support fun z ↦ ∑ x ∈ (preimageSupport_finite (W j) (div (f j) (hf j)) z).toFinset, (div (f j) (hf j)) x * mapAux (W j) x).Finite by sorry

          use j
          constructor
          · sorry
          exact this

        · rw[Finset.not_nonempty_iff_eq_empty] at o
          simp [o]
          have : {i | ((fun i ↦ Function.locallyFinsuppWithin.support (map (W i)
                      (div (f i) (hf i)))) i ∩ U).Nonempty} = ∅ := by

            sorry
          have : ∀ i, (Function.locallyFinsuppWithin.support (map (W i) (div (f i) (hf i))) ∩ U) = ∅ := sorry

          rw[inter_comm]
          simp[map] at this

          --have : ∀ i, ∑ x ∈ (preimageSupportFinite (W i) (div (f i) (hf i)) z).toFinset, (div (f i) (hf i)) x * mapAux (W i) x = ∅ := sorry


          sorry

variable {ι2 : Type*} [Nonempty ι2] (B2 : ι2 → Scheme)
    [hB2 : ∀ i : ι2, IsIntegral (B2 i)]
    [hB2' : ∀ i : ι2, IsLocallyNoetherian (B2 i)]
    (W2 : (i : ι2) → B2 i ⟶ X) [qcW2 : ∀ i, QuasiCompact (W2 i)]
    (g : (i : ι2) → (B2 i).functionField) (hg : ∀ i : ι2, g i ≠ 0)
    (hW2 : LocallyFinite (fun i : ι2 ↦ (map (W2 i) (div (g i) (hg i))).support))

/-
It's probably more sensible to just show principal cycles form a group
-/

/--
Morally, this should be multiplying f with g. To write this in a sensible way though, we need to
sort out this dimension function business, because right now even if we know the
-/

def principal_mul : AlgebraicCycle X where
  toFun Z := by
    --let c1 := principalCycle B δx δ W f hf hW
    --let c2 := principalCycle B2 δx2 δ2 W2 g hg hW2
    --#check Sum.rec δ δ2
    --#check (Sum.rec (fun i ↦ Sum.inl (δ i)) (fun i ↦ Sum.inr (δ2 i)))

    --#check principalCycle (Sum.rec B B2) δx  --(Sum.rec (fun i ↦ Sum.inl (δ i)) (fun i ↦ Sum.inr (δ2 i)))


    sorry
  supportWithinDomain' := sorry
  supportLocallyFiniteWithinDomain' := sorry

 --(principalCycle B δx δ W f hf hW) + (principalCycle B2 δx2 δ2 W2 g hg hW2) = sorry := sorry

/-
We want a theorem saying if two divisors are linearly equivalent then we can just check this by
checking if their difference is principal.
-/

/-
Note that here we are not actually using the fact that the morphisms in our family are closed immersions.
I think we'll need this in theorems and to make sure that this is indeed an equivalence relation however.
-/
noncomputable
def is_rationally_equivalent (D₁ D₂ : AlgebraicCycle X) : Prop :=
  ∃ F : LocallyFiniteClosedFamily X, D₁ - D₂ =
    have := F.hB
    have := F.hB'
    have := F.qcW
    have := F.n
    principalCycle F.B F.W F.f F.hf F.hW

end AlgebraicCycle
