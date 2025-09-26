import Mathlib
import RiemannRoch.CodimLemma
import RiemannRoch.Misc.LocalFinitenessLemmas
--import RiemannRoch.Misc.AffineOpenLemma
--import RiemannRoch.Misc.Instances

/-!
# Algebraic Cycles

In this file we define algebraic cycles on a scheme to be functions into the integers with locally
finite support. Throughout this file, and indeed this project, we use height in the specialization
order for dimension and coheight for codimension. For this to work nicely, we really need things to
be catenary. We do not define this notion in this file (at the time of writing this) since we do
not need it here, but this will be needed when one wants to relate dimension and codimension to
eachother via the topological krull dimension of the scheme.

Much of the algebraic structure on cycles is already defined nicely enough, so here we just define the
notion of the pushforward of algebraic cycles.
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

def supportLocallyFinite (c : AlgebraicCycle X) :
    ∀ z : X, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ c.support) :=
  fun z ↦ c.supportLocallyFiniteWithinDomain' z trivial
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

/--
The cycle containing a single point with a chosen coefficient
-/
noncomputable
def single (coeff : ℤ) : AlgebraicCycle X where
  toFun := Set.indicator {x} (Function.const X coeff)
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' z hz :=
    ⟨⊤, ⟨Filter.univ_mem' fun a ↦ trivial, by simp [← Function.const_def, toFinite]⟩⟩

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
def preimageSupport_finite [qf : QuasiCompact f] :
    (preimageSupport f c z).Finite := supportLocallyFiniteWithin_top_inter_compact_finite
  c.supportLocallyFinite <| QuasiCompact.isCompact_preimage_singleton f z

noncomputable
def degree [@CompactSpace X.carrier.carrier (TopCat.str X.carrier)] : ℤ :=
  LocallyFinsupp.degree c.supportLocallyFinite

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
  ∀ z : Y, ∃ t ∈ 𝓝 z, (t ∩ Function.support fun z ↦
  ∑ x ∈ (preimageSupport_finite f c z).toFinset, (c x) * mapAux f x).Finite := by
  intro y
  obtain ⟨W, hW⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) (by aesop)
  have cpct : IsCompact (f.base ⁻¹' W) := qc.1 W.carrier W.is_open' <|
     AlgebraicGeometry.IsAffineOpen.isCompact hW.1
  use W
  refine ⟨IsOpen.mem_nhds (Opens.isOpen W) hW.2.1, ?_⟩

  have pbfinite : (f.base ⁻¹' W ∩ Function.support c).Finite :=
   supportLocallyFiniteWithin_top_inter_compact_finite c.supportLocallyFinite cpct

  suffices (W.carrier ∩ {z : Y | (preimageSupport f c z).Nonempty}).Finite by
      apply Finite.subset this
      apply inter_subset_inter Set.Subset.rfl
      intro x
      simp only [top_eq_univ, Function.mem_support, ne_eq, mem_setOf_eq]
      contrapose!
      intro aux
      rw [Finset.sum_eq_zero]
      intro x hx
      simp_all

  have : W.carrier ∩ {z | (preimageSupport f c z).Nonempty} ⊆
    f.base '' (f.base ⁻¹' ((W.carrier ∩ {z | (preimageSupport f c z).Nonempty})) ∩ c.support) := by
    intro a ha
    rw [image_preimage_inter]
    suffices a ∈ f.base '' c.support from mem_inter ha this
    have := ha.2.some_mem
    simp only [preimageSupport, top_eq_univ, mem_inter_iff, mem_preimage, mem_singleton_iff,
      Function.mem_support, ne_eq, mem_image] at this ⊢
    exact ⟨ha.2.some, this.symm⟩

  refine Finite.subset (Finite.image _ ?_) this
  rw[preimage_inter]
  have : f.base ⁻¹' W.carrier ∩ f.base ⁻¹' {z | (preimageSupport f c z).Nonempty} ∩ c.support ⊆
      f.base ⁻¹' W.carrier ∩ (⋃ z : Y, preimageSupport f c z) := by
    intro p hp
    simp only [Opens.carrier_eq_coe, preimageSupport, top_eq_univ, preimage_setOf_eq, mem_inter_iff,
      mem_preimage, SetLike.mem_coe, mem_setOf_eq, Function.mem_support, ne_eq, mem_iUnion,
      mem_singleton_iff, exists_and_right, exists_eq', true_and] at hp ⊢
    exact ⟨hp.1.1, hp.2⟩

  apply Finite.subset _ this
  rw[inter_iUnion]
  simp[preimageSupport]
  suffices (⋃ i : Y, f.base ⁻¹' W.carrier ∩ c.support).Finite by
    apply Finite.subset this
    simp only [Opens.carrier_eq_coe, top_eq_univ, iUnion_subset_iff]
    intro y x hx
    simp only [mem_inter_iff, mem_preimage, SetLike.mem_coe, mem_singleton_iff,
      Function.mem_support, ne_eq, mem_iUnion, exists_and_left, exists_const_iff] at hx ⊢
    exact ⟨hx.1, ⟨Nonempty.intro y, hx.2.2⟩⟩

  suffices (f.base ⁻¹' W.carrier ∩ c.support).Finite by
    apply Finite.subset this
    intro a ha
    simp only [Opens.carrier_eq_coe, top_eq_univ, mem_iUnion, mem_inter_iff, mem_preimage,
      SetLike.mem_coe, Function.mem_support, ne_eq, exists_and_left, exists_const_iff] at ha ⊢
    exact ⟨ha.1, ha.2.2⟩

  exact pbfinite

open Classical in
noncomputable
def map {Y : Scheme}
  (f : X ⟶ Y) [qc : QuasiCompact f] (c : AlgebraicCycle X) : AlgebraicCycle Y where
  toFun z := (∑ x ∈ (preimageSupport_finite f c z).toFinset, (c x) * mapAux f x)
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' := fun z a ↦ map_locally_finite f c z

@[simp]
lemma map_id (c : AlgebraicCycle X) :
    map (𝟙 X) c = c := by
   ext z
   have : (c z ≠ 0 ∧ (preimageSupport_finite (𝟙 X) c z).toFinset = {z}) ∨
          (c z = 0 ∧ (preimageSupport_finite (𝟙 X) c z).toFinset = ∅) := by
    simp only [top_eq_univ, ne_eq, Finite.toFinset, preimageSupport, Scheme.id.base, TopCat.hom_id,
      ContinuousMap.coe_id, preimage_id_eq, id_eq, toFinset_eq_empty, singleton_inter_eq_empty,
      Function.mem_support, Decidable.not_not, and_self]
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
      simp only [HomogeneousAddSubgroup, IsHomogeneous]
      intro y hy
      simp only [top_eq_univ, map, preimageSupport, mapAux, mul_ite, mul_zero] at hy
      obtain ⟨x, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
      simp only [Finite.mem_toFinset, mem_inter_iff, mem_preimage, mem_singleton_iff,
        Function.mem_support, ne_eq, ite_eq_right_iff, mul_eq_zero, Int.natCast_eq_zero,
        Classical.not_imp, not_or] at hx
      have : height x = d := c.2 x hx.1.2
      rw [← this]
      rw [hx.2.1]
      rw [hx.1.1]
      --simp_all only [Function.mem_support, ne_eq]
