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

/--
This instance seems to not be picked up very easily by the type inference algorithm without further
coaxing.
-/
lemma krullDimLE_of_coheight {X : Scheme} [IsIntegral X]
    {Z : X} {n : ℕ} (hZ : Order.coheight Z = n) : Ring.KrullDimLE n (X.presheaf.stalk Z) := by
  rw [Ring.krullDimLE_iff, AlgebraicGeometry.stalk_dim_eq_coheight Z, hZ]
  rfl

/--
On a locally noetherian integral scheme, we define the order of vanishing of an element of the
function field `f` at a point `Z` of codimension `1` to be `Ring.ordFrac (X.presheaf.stalk Z) f`.
Because of this definition, `Scheme.ord` is valued in `ℤᵐ⁰`.
-/
noncomputable
def _root_.AlgebraicGeometry.Scheme.ord {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (Z : X) (hZ : Order.coheight Z = 1) : X.functionField →*₀ ℤᵐ⁰ :=
  have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk Z) := krullDimLE_of_coheight hZ
  Ring.ordFrac (X.presheaf.stalk Z)

/--
The order of vanishing of a non-zero element of the function field at any point is not zero. Since
`Scheme.ord` is valued in `ℤᵐ⁰`, `0` does not denote a value of `ℤ` but an added `⊥` element.
-/
lemma _root_.AlgebraicGeometry.Scheme.ord_ne_zero {X : Scheme} [IsIntegral X]
    [IsLocallyNoetherian X] {Z : X} (hZ : Order.coheight Z = 1) {f : X.functionField} (hf : f ≠ 0) :
  Scheme.ord Z hZ f ≠ 0 := (map_ne_zero (Scheme.ord Z hZ)).mpr hf

/--
For `f` an element of the function field of `X`, there exists some open set `U ⊆ X` such that
`f` is a unit in `Γ(X, U)`.
-/
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

lemma _root_.AlgebraicGeometry.Scheme.ord_unit [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    [Nonempty U] (f : Γ(X, U)) (hf : IsUnit f) (x : X) (hx : coheight x = 1) (hx' : x ∈ U) :
    Scheme.ord x hx (X.germToFunctionField U f) = 1 := by
  simp[Scheme.ord]
  have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk x) := krullDimLE_of_coheight hx
  #check X.presheaf.germ U x
  #check ordFrac_eq_ord (X.presheaf.stalk x) --(X.germToFunctionField U f)

  --#check ordFrac_eq_ord (X.presheaf.stalk x) ((ConcreteCategory.hom (X.presheaf.germ U (genericPoint ↥X) (Scheme.germToFunctionField._proof_1 X U))) f)

  sorry

def irreducibleComponents_irreducibleClosed (T : irreducibleComponents X) : IrreducibleCloseds X where
  carrier := T
  is_irreducible' := T.2.1
  is_closed' := isClosed_of_mem_irreducibleComponents T.1 T.2


noncomputable
def irreducibleComponents_height_zero : irreducibleComponents X ≃o {x : X | coheight x = 0} := by
  /-
  This is just a variation on the following OrderIso
  -/
  let f := OrderIso.mapSetOfMaximal
    (OrderIso.trans OrderIso.Set.univ (OrderIso.trans (irreducibleSetEquivPoints (α := X))
     OrderIso.Set.univ.symm))

  sorry
#check IrreducibleCloseds.map
/--
Here, we want to relate the codimension of a point in X to a point in X \ U. For this, I suppose we
can write some lemma about how codimension changes under an open immersion.

Still, I think this is overkill for what we need here.

Here, we want Subtype.val '' to give an irreducible closed set, not just a set. For this, I think
we should define some auxilliary function.
-/
lemma _root_.blablo (Y : Type*) [TopologicalSpace Y] [QuasiSober Y] [T0Space Y] [IrreducibleSpace Y]
    (U : Set Y) (hU : IsOpen U) [Nonempty U] (V : IrreducibleCloseds {x | x ∈ ⊤ ∩ U}) :
    coheight (Subtype.val '' V.1) = coheight V + 1:= by
  apply le_antisymm
  · apply coheight_le
    intro p hlast
    wlog hlenpos : p.length ≠ 0
    · simp_all
    -- essentially p' := (p.drop 1).map unbot
    let p' : LTSeries (IrreducibleCloseds ↑{x | x ∈ ⊤ ∩ U}) := {
      length := p.length - 1
      toFun := fun ⟨i, hi⟩ ↦ by
        refine ⟨p ⟨i, by omega⟩, ?_, ?_⟩
        sorry
        /-(p ⟨i+1, by omega⟩).untop (by
        apply ne_bot_of_gt (a := p.head)
        apply p.strictMono
        exact compare_gt_iff_gt.mp rfl)-/
      step := fun i => by simpa [WithBot.unbot_lt_iff] using p.step ⟨i + 1, by omega⟩ }
    have hlast' : p'.last = x := by
      simp only [p', RelSeries.last, WithBot.unbot_eq_iff, ← hlast, Fin.last]
      congr
      omega
    suffices p'.length ≤ height p'.last by
      simpa [p', hlast'] using this
    apply length_le_height_last
  · rw [height_add_const]
    apply iSup₂_le
    intro p hlast
    let p' := (p.map _ WithBot.coe_strictMono).cons ⊥ (by simp)
    apply le_iSup₂_of_le p' (by simp [p', hlast]) (by simp [p'])

-- lemma blo [IsIntegral X] (x : X)


open Classical in
noncomputable
def div [IsIntegral X] [IsLocallyNoetherian X]
  (f : X.functionField) (hf : f ≠ 0) : AlgebraicCycle X where
    toFun Z := if h : Order.coheight Z = 1
               then Multiplicative.toAdd <| WithZero.unzero (Scheme.ord_ne_zero h hf)
               else 0
    supportWithinDomain' := by simp
    supportLocallyFiniteWithinDomain' := by
      intro z hz

      -- Take U to be a neighboourhood of z in which f ∈ 𝒪(U)ˣ
      obtain ⟨U, f', hU, hf'⟩ := Scheme.functionField_exists_unit_nhd f hf


      by_cases h : z ∈ U
      · /-
        By assumption, the order of vanishing at every point of `U` is trivial.
        Hence, if `z ∈ U`, we can take our neighbourhood to be `U`, where the support will be empty
        and hence clearly finite.
        -/
        use U
        constructor
        · rw [@_root_.mem_nhds_iff]
          use U
          simp[h]
          exact U.2
        · convert finite_empty
          ext a
          simp
          intro ha ha'
          suffices Scheme.ord a ha' f = 1 by aesop
          rw[← hf'.1]
          exact AlgebraicGeometry.Scheme.ord_unit _ _ hf'.2 _ _ ha
      · /-
        Suppose z ∉ U. Since U is assumed to be nonempty, X \ U is a proper closed subset of X.
        Hence, any point of X \ U with codimension 1 in X must have codimension 0 in X \ U, since
        the only point bigger than a codimension 1 point in an integral scheme is the whole space.

        In particular, this means that any codimension 1 point of X where f has nontrivial vanishing
        must be an irreducible component of X \ U.

        Take `W` to be an affine neighbourhood of `z`. Since `X` is locally Noetherian. we must have
        that `W` is a Noetherian space, meaning namely it has finitely many irreducible components.
        This then shows that `W` hits the support of `f` in finitely many places, since any such
        element of the support defines an irreducible component of `XU`, which must be an irreducible
        component of `W ∩ XU`, which is Noetherian since `W` is Noetherian.
        -/
        let XU := (⊤ : Set X) \ U
        have properClosed : XU ≠ ⊤ ∧ IsClosed XU := by have := U.2; aesop

        have (y : X) (h : Order.coheight y = 1)
            (hy : Scheme.ord y h f ≠ 1) : y ∈ XU := by
          simp[XU]
          intro hy'
          have := AlgebraicGeometry.Scheme.ord_unit _ _ hf'.2 _ h hy'
          rw[hf'.1] at this
          exact hy this

        have (y : X) (h : Order.coheight y = 1)
            (hy : Scheme.ord y h f ≠ 1) : closure {y} ⊆ XU :=
          (IsClosed.closure_subset_iff properClosed.2).mpr
            (singleton_subset_iff.mpr (this y h hy))

        obtain ⟨W, hW⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
          (x := z) (U := ⊤) (by aesop)
        use W
        refine ⟨IsOpen.mem_nhds (Opens.isOpen W) hW.2.1, ?_⟩


        /-
        We want to somehow say that elements of this intersection must be irreducible components.
        I think this should just be another application of our lemma in codimlemmas.

        What did I mean by this? Well, I'm not entirely sure, but the argument here should be that
        irreducible components are precisely the points of codimension 0. And it should be the
        case that the points of codimension 0 in `X \ U` are precisely the points of codimension 1
        in `X` outside of `U`.


        -/


        let thing := W.1 ∩ XU

        have : NoetherianSpace thing := sorry
        have : (irreducibleComponents thing).Finite :=
          TopologicalSpace.NoetherianSpace.finite_irreducibleComponents





        --rw[AlgebraicCycle.irreducibleComponents_height_zero] at this
        --suffices (@irreducibleComponents (W.1 ∩ XU) sorry ).Finite by sorry
        #check IrreducibleCloseds.map'OrderIso
        #check TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

        sorry

lemma div_eq_zero_of_coheight_ne_one [IsIntegral X] [IsLocallyNoetherian X] (f : X.functionField)
    (hf : f ≠ 0) (Z : X) (hZ : coheight Z ≠ 1) : div f hf Z = 0 := dif_neg hZ

lemma div_eq_ord_of_coheight_eq_one [IsIntegral X] [IsLocallyNoetherian X] (f : X.functionField)
    (hf : f ≠ 0) (Z : X) (hZ : coheight Z = 1) :
    div f hf Z = Multiplicative.toAdd (WithZero.unzero (Scheme.ord_ne_zero hZ hf)) := dif_pos hZ

theorem div_homomorphism [IsIntegral X] [h : IsLocallyNoetherian X]
    (f : X.functionField) (hf : f ≠ 0) (g : X.functionField) (hg : g ≠ 0) :
    div (f * g) (by simp_all) = div f hf + div g hg := by
  ext a
  suffices (div (f*g) (by simp_all)).toFun a = (div f hf).toFun a + (div g hg).toFun a from this
  simp only [top_eq_univ, div, map_mul]
  aesop (add simp unzero_mul)


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

/-
Helper function for defining principal cycles. It says that given a point z of X, the set of
subschemes on which the principal cycle is defined only hits z at finitely many schemes.
-/
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
      let fino (i : ι) := map_locally_finite (W i) (div (f i) (hf i))

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
        · /-
          If U is empty, that means that the neighbourhood given around z intersects none of the
          subvarieties on which our cycle is supported.
          -/
          rw[inter_comm, ← inter_assoc]
          apply Set.Finite.inter_of_left
          rw[inter_comm]
          have (i : ι) := (fino i z).choose_spec.2

          /-
          Here we're just rearranging the intersections
          -/
          have rwl := biInter_inter o (fun i ↦ (fino i z).choose)
            (Function.support fun z ↦ ∑ i ∈ (singletonFinite B W f hf hW z).toFinset,
            ∑ x ∈ (preimageSupport_finite (W i) (div (f i) (hf i)) z).toFinset,
            (div (f i) (hf i)) x * mapAux (W i) x)
          erw [← rwl] -- don't love this

          /-
          Here we're turning the sum into a union in a manner similar to
          Finsupp.support_sum_eq_biUnion (except here the things are not necessarily disjoint
          so we just get a subset).
          -/
          suffices (⋂ i ∈ hU.2.toFinset,
                   ((fino i z).choose ∩ ⋃ j ∈ (singletonFinite B W f hf hW z).toFinset,
                    Function.support fun z ↦ ∑ x ∈ (preimageSupport_finite (W j)
                    (div (f j) (hf j)) z).toFinset,
                    (div (f j) (hf j)) x * mapAux (W j) x)).Finite by sorry
          /-
          This should hold by distributivity of intersections across unions
          -/
          suffices (⋃ j ∈ (singletonFinite B W f hf hW z).toFinset,
                   (⋂ i ∈ hU.2.toFinset, ((fino i z).choose) ∩ Function.support fun z ↦
                    ∑ x ∈ (preimageSupport_finite (W j) (div (f j) (hf j)) z).toFinset,
                    (div (f j) (hf j)) x * mapAux (W j) x)).Finite by sorry

          apply Set.Finite.biUnion
          · -- This is a little bit cursed
            simp [Set.Finite]
            convert (singletonFinite B W f hf hW z)
            simp [Set.Finite]
          intro j hj

          /-
          (W j) denotes the subvariety we're on.
          -/
          specialize this j

          /-
          This should just be a general lemma somewhere, that if you have a big intersection,
          you only need one of your sets to be finite for the whole thing to be finite
          -/
          suffices ∃ i ∈ hU.right.toFinset,
                   ((fino i z).choose ∩ Function.support fun z ↦
                    ∑ x ∈ (preimageSupport_finite (W j) (div (f j) (hf j)) z).toFinset,
                    (div (f j) (hf j)) x * mapAux (W j) x).Finite by sorry

          use j
          constructor
          · /-
            Here singletonFinite B W f hf hW z denotes the fact that the subvariety (W i) hits z.
            We need t
            -/
            have : j ∈ (singletonFinite B W f hf hW z).toFinset := by exact hj

            simp only [top_eq_univ, Finite.mem_toFinset, mem_setOf_eq] at this ⊢
            refine Nonempty.mono ?_ this
            have := mem_of_mem_nhds hU.1
            apply Set.inter_subset_inter (by simp) (by aesop)

          exact this

        · /-
          We are now in the case where hU.2 is empty, meaning that there are no subvarieties (W i)
          hitting our neighbourhood U.
          -/

          rw[Finset.not_nonempty_iff_eq_empty] at o
          #check Finset.support_sum
          simp [o]

          /-
          We now have something very close to what we want. The goal says that the number of places
          where U hits the support is finite, and o says the number of subvarieties (W i) that hit
          U is empty. The have below expresses this more explicitly
          -/

          have : {i | ((Function.locallyFinsuppWithin.support (map (W i)
                      (div (f i) (hf i)))) ∩ U).Nonempty} = ∅ := by
            rwa [Set.Finite.toFinset_eq_empty] at o

          have : ∀ i,
            (Function.locallyFinsuppWithin.support (map (W i) (div (f i) (hf i))) ∩ U) = ∅ := by
            intro i
            rw[← Set.not_nonempty_iff_eq_empty]
            intro h
            have : {i | ((Function.locallyFinsuppWithin.support (map (W i) (div (f i) (hf i)))) ∩ U).Nonempty} := ⟨i, h⟩
            aesop

          rw[inter_comm]


          /-
          The problem we're having is that `s` in Finset.support_sum cannot depend on the input `x`.
          This is an issue for us since `x` in our case depends on `z`.
          -/


          --#check Finset.support_sum ((singletonFinite B W f hf hW z).toFinset) (fun i z ↦ (∑ x ∈ (preimageSupport_finite (W i) (div (f i) (hf i)) z).toFinset, (div (f i) (hf i)) x * mapAux (W i) x))
          have := Finset.support_sum ((singletonFinite B W f hf hW z).toFinset) (fun i z ↦ ∑ x ∈ (preimageSupport_finite (W i) (div (f i) (hf i)) z).toFinset, (div (f i) (hf i)) x * mapAux (W i) x)
          have t1 := inter_subset_inter this (by simp : U ⊆ U)
          --have t2 : ((Function.support fun x ↦ ∑ i ∈ (singletonFinite B W f hf hW z).toFinset, ∑ x ∈ (preimageSupport_finite (W i) (div (f i) (hf i)) x).toFinset, (div (f i) (hf i)) x * mapAux (W i) x) ∩ U).Finite := sorry

          #check Finite.subset ?_ (Finset.support_sum ?_ ?_)
          have t2 : ((⋃ i ∈ (singletonFinite B W f hf hW z).toFinset, Function.support fun z ↦ ∑ x ∈ (preimageSupport_finite (W i) (div (f i) (hf i)) z).toFinset, (div (f i) (hf i)) x * mapAux (W i) x) ∩ U).Finite := sorry
          have := Finite.subset t2 t1
          simp_all

          /-
          Interesting. I think we're getting the zs mixed up somehow.
          -/
          convert this
          --simp
          --refine Finite.subset ?_ (inter_subset_inter this (by simp : U ⊆ U))
          --#check (by simp : U ⊆ U)
          --refine Finite.subset ?_ (Finset.support_sum ((singletonFinite B W f hf hW z).toFinset) (fun i z ↦ ∑ x ∈ (preimageSupport_finite (W i) (div (f i) (hf i)) z).toFinset, (div (f i) (hf i)) x * mapAux (W i) x))


          simp[map, Function.locallyFinsuppWithin.support] at this
          #check Finite.subset
          #check Finset.support_sum

          /-refine Finite.subset ?_ (Finset.support_sum (congrArg setOf (funext fun i ↦ Eq.trans inter_singleton_nonempty._simp_1 Function.mem_mulSupport._simp_4) ▸
  singletonFinite B W f hf hW z) ?_)  -/


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
