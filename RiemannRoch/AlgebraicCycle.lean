import Mathlib
import RiemannRoch.CodimLemma
import RiemannRoch.IsFreeAbelian
--import Batteries.Tactic.ShowUnused

/-!
# Algebraic Cycles

In this file we define algebraic cycles on a scheme to be functions into the integers with locally
finite support. Throughout this file, and indeed this project, we use height in the specialization
order for dimension and coheight for codimension. For this to work nicely, we really need things to
be catenary. We do not define this notion in this file (at the time of writing this) since we do
not need it here, but this will be needed when one wants to relate dimension and codimension to
eachother via the topological krull dimension of the scheme.

Much of the algebraic structure on cycles is already defined happily, so here we just define the
notion of the pushforward of algebraic cycles, and define the notion of a "principal cycle",
which is just a witness for rational equivalence. We show that these principal
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




lemma heightClosedPoint {X : Scheme} {x : X} (hx : IsClosed {x}) : height x = 0 := by
  simp only [height_eq_zero]
  intro b _
  by_cases h : b ≠ x
  have := IsClosed.not_specializes hx rfl h
  · contradiction
  · aesop

noncomputable
instance {X : Scheme} [IsIntegral X] : OrderTop X where
  top := genericPoint X
  le_top := fun a ↦ genericPoint_specializes a

/--
An algebraic cycle on a scheme X is defined to be a function from X to
ℤ with locally finite support.
-/
abbrev AlgebraicCycle (X : Scheme) := Function.locallyFinsuppWithin (⊤ : Set X) ℤ



namespace AlgebraicCycle

/--
Proposition saying whether a cycle is of pure dimension `d`.
-/
def IsHomogeneous (d : ℕ∞) (c : AlgebraicCycle X) : Prop := ∀ x ∈ c.support, height x = d

/--
Subgroup of cycles of pure dimension `d`.
-/
def HomogeneousAddSubgroup (X : Scheme) (d : ℕ∞) : AddSubgroup (AlgebraicCycle X) where
  carrier := {c : AlgebraicCycle X | IsHomogeneous d c}
  add_mem' c₁ c₂ := by
    rename_i a b
    simp_all only [IsHomogeneous, top_eq_univ, Function.mem_support, ne_eq, mem_setOf_eq,
      Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
    intro x hx
    specialize c₁ x
    specialize c₂ x
    have : ¬ a x = 0 ∨ ¬ b x = 0 := by omega
    obtain h | h := this
    · exact c₁ h
    · exact c₂ h
  zero_mem' := by simp [IsHomogeneous]
  neg_mem' c := by simp_all [IsHomogeneous]


/--
Homogeneous part of dimension `d` of an algebraic cycle `c`.
-/
noncomputable
def homogeneousProjection (c : AlgebraicCycle X) (d : ℕ∞) : HomogeneousAddSubgroup X d where
  val := {
    toFun x := if height x = d then c x else 0
    supportWithinDomain' := by simp
    supportLocallyFiniteWithinDomain' z hz := by
      choose t ht using c.supportLocallyFiniteWithinDomain' z
      use t hz
      specialize ht hz
      refine ⟨ht.1, ?_⟩
      have := ht.2
      apply Finite.subset this
      refine inter_subset_inter (fun ⦃a⦄ a ↦ a) (Function.support_subset_iff'.mpr ?_)
      intro x hx
      simp only [top_eq_univ, Function.mem_support, ne_eq, Decidable.not_not,
        ite_eq_right_iff] at hx ⊢
      exact fun _ ↦ hx
  }
  property := by
    simp only [top_eq_univ, HomogeneousAddSubgroup, IsHomogeneous, Function.mem_support, ne_eq,
      AddSubgroup.mem_mk, mem_setOf_eq]
    intro x hx
    have : ¬ (if height x = d then c x else 0) = 0 := hx
    aesop

variable (f : X ⟶ Y)
         (c : AlgebraicCycle X)
         (x : X)
         (z : Y)
lemma sma {α : Type*} (s t : Set α) : (s ∩ t) = {i : s | ↑i ∈ t} := by
  aesop

lemma ds {α : Type*} (s t : Set α) : {i : s | ({↑i} ∩ t).Nonempty} = (t ∩ s) := by aesop

lemma _root_.LocallyFinite.of_set_set : LocallyFinite (fun s : c.support ↦ ({s.val} : Set X)) := by
  intro z
  obtain ⟨t, ht⟩ := c.supportLocallyFiniteWithinDomain' z (by aesop)
  use t
  refine ⟨ht.1, ?_⟩
  have ans := ht.2
  simp only [top_eq_univ, sma t (Function.support c.toFun), Function.mem_support, ne_eq,
    Subtype.coe_image, mem_setOf_eq, exists_prop] at ans
  simp only [top_eq_univ, Function.support, ne_eq, coe_setOf, mem_setOf_eq,
    singleton_inter_nonempty]
  have  : {x | x ∈ t ∧ ¬c.toFun x = 0} =
            Subtype.val '' {i : { x // ¬c x = 0 } | ↑i ∈ t} := by aesop
  rw[this] at ans
  convert ans
  apply Equiv.set_finite_iff
  exact BijOn.equiv (Subtype.val) (InjOn.bijOn_image injOn_subtype_val)


/--
The cycle containing a single point with a chosen coefficient
-/
noncomputable
def single (coeff : ℤ) : AlgebraicCycle X where
  toFun := Set.indicator {x} (Function.const X coeff)
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' z hz :=
    ⟨⊤, ⟨Filter.univ_mem' fun a ↦ trivial, by simp [← Function.const_def, toFinite]⟩⟩

instance [CompactSpace X.carrier] : IsFreeAbelian (fun x ↦ single x 1 : X → AlgebraicCycle X) := sorry
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
  simp[preimageSupport]
  have cpct : IsCompact (f.base ⁻¹' {z}) := QuasiCompact.isCompact_preimage_singleton f z
  have := LocallyFinite.finite_nonempty_inter_compact (_root_.LocallyFinite.of_set_set c) cpct
  rw[← ds c.support (f.base ⁻¹' {z})]
  exact Finite.image Subtype.val this

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
def mapAux {Y : Scheme} (f : X ⟶ Y) (x : X) : ℤ :=
  if height x = height (f.base x) then Hom.degree f x else 0

lemma map_locally_finite {Y : Scheme}
  (f : X ⟶ Y) [qc : QuasiCompact f] (c : AlgebraicCycle X) :
  ∀ z ∈ (⊤ : Set Y), ∃ t ∈ 𝓝 z, (t ∩ Function.support fun z ↦
  ∑ x ∈ (preimageSupportFinite f c z).toFinset, (c x) * mapAux f x).Finite := by
  intro y hy
  have : ∃ W : Y.Opens, IsAffineOpen W ∧ y ∈ W := by
    obtain ⟨R, f, hf⟩ := AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset
      (U := ⊤) (x := y) (by aesop)
    exact ⟨Scheme.Hom.opensRange f (H := hf.1),
          ⟨AlgebraicGeometry.isAffineOpen_opensRange f (H := hf.1) , hf.2.1⟩⟩




  obtain ⟨W, hW⟩ := this
  have affineCompact : IsCompact W.carrier := AlgebraicGeometry.IsAffineOpen.isCompact hW.1
  use W
  constructor
  · refine IsOpen.mem_nhds ?_ ?_
    · exact Opens.isOpen W
    · exact hW.2
  · have cpct : IsCompact (f.base ⁻¹' W) := qc.1 W.carrier W.is_open' affineCompact

    have pbfinite : (f.base ⁻¹' W ∩ Function.support c).Finite := by
      simp[preimageSupport]
      have := LocallyFinite.finite_nonempty_inter_compact (_root_.LocallyFinite.of_set_set c) cpct
      rw[← ds c.support (f.base ⁻¹' W)]
      exact Finite.image Subtype.val this

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
def map {Y : Scheme}
  (f : X ⟶ Y) [qc : QuasiCompact f] (c : AlgebraicCycle X) : AlgebraicCycle Y where
  toFun z := (∑ x ∈ (preimageSupportFinite f c z).toFinset, (c x) * mapAux f x)
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' := fun z a ↦ map_locally_finite f c z a

@[simp]
lemma map_id (c : AlgebraicCycle X) :
    map (𝟙 X) c = c := by
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
   suffices (map (𝟙 X) c).toFun z = c.toFun z by exact this
   obtain h | h := this
   · simp[map, mapAux]
     rw[h.2]
     simp [Hom.degree]
     rfl
   · simp[map, mapAux]
     rw[h.2]
     simp[Hom.degree]
     exact h.1.symm

/--
Pushforward preserves cycles of pure dimension `d`.
-/
noncomputable
def map_homogeneneous {Y : Scheme.{u}} {d : ℕ∞} (f : X ⟶ Y) [qc : QuasiCompact f]
  (c : HomogeneousAddSubgroup X d) : HomogeneousAddSubgroup Y d where
    val := map f c
    property := by
      simp[HomogeneousAddSubgroup, IsHomogeneous]
      intro y hy
      have : ¬ (map f c).toFun y = 0 := hy
      simp only [top_eq_univ, map, preimageSupport, mapAux, mul_ite, mul_zero] at this
      obtain ⟨x, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero this
      simp only [Finite.mem_toFinset, mem_inter_iff, mem_preimage, mem_singleton_iff,
        Function.mem_support, ne_eq, ite_eq_right_iff, mul_eq_zero, Int.natCast_eq_zero,
        Classical.not_imp, not_or] at hx
      have : height x = d := c.2 x hx.1.2
      aesop

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
  exact @IsLocalization.isNoetherianRing _ _ (U.2.primeIdealOf ⟨Z, hU⟩).asIdeal.primeCompl (X.presheaf.stalk Z) _ (X.presheaf.algebra_section_stalk ⟨Z, hU⟩) this (IsLocallyNoetherian.component_noetherian U)


instance {X : Scheme} [IsIntegral X] {Z : X} : IsDomain (X.presheaf.stalk Z) :=
  Function.Injective.isDomain _ (IsFractionRing.injective (X.presheaf.stalk Z) (X.functionField))


open Multiplicative
noncomputable
def _root_.AlgebraicGeometry.Scheme.ord {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  {Z : X} (hZ : Order.coheight Z = 1) : X.functionField →*₀ ℤₘ₀ :=
  have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk Z) := by
    rw[Ring.krullDimLE_iff, stalk_dim_of_codim Z hZ]
  Ring.ordFrac (X.presheaf.stalk Z)
/-
Proof of concept, but this is a mildly insane way to write this I think.

The idea is we want to compute the order of vanishing of a mermorphic section of a line bundle.
On an integral scheme, a meromorphic section is just a section of the constant sheaf
of value F.stalk (genericPoint X).

The idea is we should have that for any x : X,
F.stalk (genericPoint X) ≅ (F.stalk x) ⊗ X.functionField. This should be induced by the fact that
the constant sheaf F.stalk (genericPoint X) is 𝒪.stalk (genericPoint X)
-/

def _root_.AlgebraicGeometry.Scheme.sheafOrd {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  {Z : X} (hZ : Order.coheight Z = 1) (F : TopCat.Presheaf CommRingCat X)
  [Module ↑(X.presheaf.stalk Z) ↑(F.stalk Z) ]
  [Module.Free ↑(X.presheaf.stalk Z) ↑(F.stalk Z) ]
  (hF : Module.rank (X.presheaf.stalk Z) (F.stalk Z) = 1) :
  F.stalk (genericPoint X) →*₀ ℤₘ₀ := by
    have : StrongRankCondition ↑(F.stalk Z) := sorry
    choose s hs using rank_eq_one_iff.mp hF
    let f : F.stalk (genericPoint X) → X.functionField := by
      intro v
      --obtain ⟨r, hr⟩ := hs.2 v

      sorry

    sorry


lemma _root_.AlgebraicGeometry.Scheme.ord_ne_zero {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  {Z : X} (hZ : Order.coheight Z = 1) {f : X.functionField} (hf : f ≠ 0) : Scheme.ord hZ f ≠ 0 := (map_ne_zero
        (Scheme.ord hZ)).mpr
    hf
/-
I'm not enitrely sure if this works or not. I think since we're working on an intetgral scheme,
we really should have that there is no mixing of dimension and this should work fine
-/
noncomputable
def div [IsIntegral X] [IsLocallyNoetherian X]
  (f : X.functionField) (hf : f ≠ 0) : AlgebraicCycle X where
    -- TODO: Fix this definition with the new definition of order
    toFun Z := if h : Order.coheight Z = 1
               then WithZero.unzero (Scheme.ord_ne_zero h hf)
               else 0
    supportWithinDomain' := by simp
    supportLocallyFiniteWithinDomain' := by sorry
      /-
      intro z hz

      have : ∃ U : X.Opens, ∃ f' : Γ(X, U), ∃ hU : Nonempty U,
        X.germToFunctionField U f' = f ∧ IsUnit f' := by
        /-
        This is really just the universal property of colimits + the fact that the map is
        injective, so there should be nothing to say here.
        -/

        sorry
      obtain ⟨U, f', hU, hf'⟩ := this
      /-
      We want to say here that the order of vanishing of f is trivial on all points of U.
      This just follows from the order of vanshing being a homomorphism.
      -/
      have : ∀ y ∈ U, ∀ h : height y = 1, _root_.AlgebraicGeometry.Scheme.ord h f = 0 := sorry
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
          (hy : _root_.AlgebraicGeometry.Scheme.ord h f ≠ 0) : closure {y} ⊆ XU :=

          sorry
        have (y : X) (h : Order.height y = 1)
          (hy : _root_.AlgebraicGeometry.Scheme.ord h f ≠ 0) : Prop := by
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
        sorry-/



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
  suffices (div (f*g) (by simp_all)).toFun a = (div f hf).toFun a + (div g hg).toFun a from this
  simp[div]
  split_ifs
  · rename_i ha
    rw[← WithZero.coe_inj]
    simp[WithZero.unzero_coe, WithZero.toMulBot]



    sorry
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

def _root_.LocallyFiniteClosedFamily.ofRat (δ : X → ℤ) [ix : IsIntegral X]
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
      ∑ i ∈ (singletonFinite B W f hf hW z).toFinset,
      (∑ x ∈ (preimageSupportFinite (W i) (div (f i) (hf i)) z).toFinset,
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
      use (⋂ i ∈ hU.2.toFinset, (fino i z hz).choose) ∩ U
      constructor
      · apply Filter.inter_mem
        · rw[Finset.iInter_mem_sets]
          intro i hi
          exact (fino i z hz).choose_spec.1
        · exact hU.1
      · /-
        U is a set around z which intersects finitely many of the subvarieties on which we're
        computing the rational equivalence.

        Let c_i be the pushforward of div (f i) along W_i. On U, z meets finitely many c_i. And
        we know that for all i, we can construct a neighbourhood V_i of z such that V_i instersects
        c_i in finitely many places.

        The idea is to take the finitely many i meeting U, and so take the intersection of all the
        V_is and U. Call this new set T. T intersects finitely many c_i since it is a subset of U.
        Further, every c_i intersects T in finitely many points since we took an intersection, so
        we should be done.

        One thing to note is that if there are no such c_i meeting U, then T will be an intersection
        over the empty set, i.e. univ.
        -/


        have (i : ι) := (fino i z hz).choose_spec
        rw[iInter_inter, iInter_inter]
        apply @Finite.Set.finite_iInter _ _ _ _ ?_
        intro i

        have ne : Nonempty (i ∈ hU.2.toFinset) := sorry
        rw[iInter_inter, iInter_inter]
        apply @Finite.Set.finite_iInter _ _ _ _ ?_
        intro hi
        rw[inter_right_comm]
        have := (this i).2
        suffices Finite ↑(((fino i z hz).choose ∩ ⋃ i ∈ (singletonFinite B W f hf hW z).toFinset, Function.support fun z ↦  ∑ x ∈ (preimageSupportFinite (W i) (div (f i) (hf i)) z).toFinset, (div (f i) (hf i)) x * mapAux (W i) x) ∩ U) by sorry
        refine @Finite.Set.finite_inter_of_left _ _ _ ?_
        rw [@inter_iUnion₂]

        --
        #check @Finite.Set.finite_biUnion _ _ _ (singletonFinite B W f hf hW z) (fun i_1 ↦ (fino i z hz).choose ∩ Function.support fun z ↦ ∑ x ∈ (preimageSupportFinite (W i_1) (div (f i_1) (hf i_1)) z).toFinset, (div (f i_1) (hf i_1)) x * mapAux (W i_1) x) ?_
        convert this


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
    #check Sum.inl
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

end AlgebraicCycle
