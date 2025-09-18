import Mathlib

open Order TopologicalSpace Topology

variable {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X]



lemma Maximal.top_iff_isMax {α : Type*} (x : α) [LE α] : Maximal ⊤ x ↔ IsMax x := by
  simp [Maximal, IsMax]

/--
If a proposition holds for all elements, then the subtype is order isomorphic to the original type.
-/
def subtypeUnivOrderIso {α : Type*} [LE α] {p : α → Prop} (h : ∀ (x : α), p x) :
  Subtype p ≃o α where
    __ := Equiv.subtypeUnivEquiv h
    map_rel_iff' := by simp

local instance {X : Type*} [TopologicalSpace X] : Preorder X := specializationPreorder X in
/--
The irreducible components are precisely the codimension `0` points.
-/
noncomputable
def coheightZeroSetOrderIsoIrreducibleComponents :
    {x : X | coheight x = 0} ≃o irreducibleComponents X := by
  let something := irreducibleSetEquivPoints (α := X)
  rw [irreducibleComponents_eq_maximals_closed]
  let thing := OrderIso.image_setOf_maximal something ⊤

  have : {x : X | coheight x = 0} = {x : X | IsMax x} := by simp
  rw [this]

  have : {x : X | IsMax x} = {x : X | Maximal ⊤ x} := by
    simp[Maximal.top_iff_isMax]

  rw [this]
  apply OrderIso.mapSetOfMaximal
  simp
  have : (fun x ↦ True : Set X) = ⊤ := rfl
  rw [this]
  have : ((fun x ↦ IsClosed x ∧ IsIrreducible x) : Set (Set X)) =
      {x : Set X | IsClosed x ∧ IsIrreducible x} := rfl
  rw[this]
  simp
  let cruc := TopologicalSpace.IrreducibleCloseds.orderIsoSubtype' X
  have : ∀ x : X, ⊤ := by aesop
  let mmm := subtypeUnivOrderIso this
  let l := OrderIso.trans mmm something.symm
  let l' := OrderIso.trans l cruc
  exact l'


/-
With a bit of luck we can now use this to show that if we have some proper closed subset of an
integral scheme, then codimension 1 points lying on our set have codimension 0 when measured on
just the proper closed subset.

TODO: Clean this stupid definition up a bit. Should be ~3 lines.
-/
lemma coheight_zero_of_coheight_one_of_strictMono
    {α β: Type*} [Preorder α] [Preorder β] (f : WithTop α → β) (hf : StrictMono f) (x : α)
    (h : coheight (f x) = 1) : coheight x = 0 := by
  suffices coheight (x : WithTop α) = 1 by
    simp at this
    by_cases m : coheight x = ⊤
    · rw[m] at this
      contradiction
    · push_neg at m
      rw [ENat.ne_top_iff_exists] at m
      obtain ⟨a, ha⟩ := m
      rw [← ha] at this ⊢
      rw [← Nat.cast_one, ← ENat.coe_add, ENat.coe_inj] at this
      simpa using this

  have : coheight (f x) ≥ coheight (x : WithTop α) :=
    coheight_le_coheight_apply_of_strictMono f hf ↑x

  rw [h] at this
  apply le_antisymm
  · exact this
  · simp

open Classical in
/-
This would be more general if we, instead of taking as input points of X, took in sets. Then we
could just send our ⊤ element to the whole space X instead of needing a generic point to send ⊤ to.
-/
noncomputable
def withtop_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [QuasiSober Y]
    [IrreducibleSpace Y]
    (f : X → Y) : WithTop X → Y :=
  fun a ↦ if h : a = ⊤ then genericPoint Y else f (WithTop.untop a h)

/--
This tells us the map from a proper closed subset to the whole space is strictly monotone
-/
local instance {X : Type*} [TopologicalSpace X] : Preorder X := specializationPreorder X in
lemma dsa {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [QuasiSober Y] [IrreducibleSpace Y]
    (f : X → Y) (hf : @StrictMono _ _ (specializationPreorder X) (specializationPreorder Y) f)
    (hf2 : ∀ x : X, f x < genericPoint Y) :
    @StrictMono _ _ (@WithTop.preorder _ (specializationPreorder X)) (specializationPreorder Y)
    (withtop_map f) := by
  unfold withtop_map
  intro a b h
  by_cases ha : a = ⊤
  · simp [ha]
    rw[ha] at h
    have : b = ⊤ := by aesop
    simp [this]
    aesop
  · simp [ha]
    by_cases hb : b = ⊤
    · specialize hf2 (a.untop ha)
      simpa [hb]
    · simp [hb]
      have : a.untop ha < b.untop hb := by
        simpa only [WithTop.untop_lt_iff, WithTop.coe_untop]
      exact hf this

/-
We now need to show that the conditions for this silly dsa lemma actually apply to the inclusion
from a proper closed subset into some ambient space.
-/
/-
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))

lemma strictMono_f (hf : Function.Injective f) :
    @StrictMono _ _ (specializationPreorder X) (specializationPreorder Y) f := by
  intro a b h
  suffices f b ⤳ f a ∧ ¬f a ⤳ f b by
    simpa [specializationPreorder]
  constructor
  · apply ContinuousMap.map_specializes f
    simp_all [specializationPreorder]
  ·
    simp_all [specializationPreorder]
    #check h.1.map
    sorry-/


variable {X : Type*} {p : Set X} [TopologicalSpace X]

lemma strictMono_val :
    @StrictMono _ _ (specializationPreorder p) (specializationPreorder X) Subtype.val := by
  intro a b h
  simp_all [specializationPreorder]
  rw [subtype_specializes_iff, subtype_specializes_iff] at h
  exact h

variable [QuasiSober X] [IrreducibleSpace X]

local instance {X : Type*} [TopologicalSpace X] : Preorder X := specializationPreorder X in
lemma val_lt_genericPoint_of_closure_ne_top (hp : closure p ≠ ⊤) :
    ∀ x : p, @LT.lt X (specializationPreorder X).toLT (Subtype.val x) (genericPoint X) := by
  intro x
  simp_all [specializationPreorder]
  constructor
  · exact genericPoint_specializes (Subtype.val x)
  · intro h
    rw [specializes_iff_closure_subset] at h
    simp at h
    have : closure {Subtype.val x} ⊆ closure p := by
      refine closure_mono ?_
      simp
    simp_all

variable [T0Space X]

lemma thingo (x : X) (hx : x ⤳ genericPoint X) : x = genericPoint X := by
  have a : IsGenericPoint (genericPoint X) ⊤ := by
    simp [IsGenericPoint]
  have b : IsGenericPoint x ⊤ := by
    simp [IsGenericPoint]
    rw [specializes_iff_closure_subset] at hx
    apply le_antisymm
    · simp
    · simpa using hx
  exact IsGenericPoint.eq b a


local instance {X : Type*} [TopologicalSpace X] : Preorder X := specializationPreorder X in
omit [T0Space X] in
lemma coheight_lemma (hp : closure p ≠ ⊤) :
    {x : X | x ∈ p ∧ coheight x = 1} ⊆ Subtype.val '' {x : p | coheight x = 0} := by
  simp only [Set.subset_def, Set.mem_setOf_eq, Set.mem_image,
    Subtype.exists, exists_and_right, exists_eq_right, and_imp]
  intro x hx hx'
  use hx
  have : ∀ (x : Subtype p), ↑x < genericPoint X := by
    intro x
    exact val_lt_genericPoint_of_closure_ne_top hp x
  have := dsa (Subtype.val : Subtype p → X) strictMono_val this
  let m := @coheight_zero_of_coheight_one_of_strictMono (Subtype p) X
      (specializationPreorder (Subtype p)) (specializationPreorder X)
      (withtop_map (Subtype.val : Subtype p → X)) this ⟨x, hx⟩ hx'
  convert m
  simp [instPreorderOfTopologicalSpace_riemannRoch_3]
  simp [Subtype.preorder, specializationPreorder, Preorder.lift]
  ext a b
  simp
  exact Iff.symm (subtype_specializes_iff b a)


/-
Sanity check. What are we actually trying to show here?

We're trying to show that in a proper closed subset of a space, the points with codimension 1 in the
image of the embedding have codimension 0 in the original space. Is this funny WithTop business
the best was to accomplish this? I think so??
-/
