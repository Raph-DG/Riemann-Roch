import Mathlib

open Order TopologicalSpace Topology

variable {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X]


#check Specialization X
/-
Above is the notion of `X` considered with the specialization order.
We should use this in this file instead of the silly type annotations.
-/

lemma Maximal.top_iff_isMax {α : Type*} (x : α) [LE α] : Maximal ⊤ x ↔ IsMax x := by
  simp [Maximal, IsMax]

/--
If a predicate `p` on `α` holds for all elements of `α`,
then `Subtype p` is order isomorphic to the original type.
-/
def subtypeUnivOrderIso {α : Type*} [LE α] {p : α → Prop} (h : ∀ (x : α), p x) :
  Subtype p ≃o α where
    __ := Equiv.subtypeUnivEquiv h
    map_rel_iff' := by simp


local instance {X : Type*} [TopologicalSpace X] : Preorder X := specializationPreorder X in
/--
In a sober topological space, the irreducible components are precisely the points with coheight
`0` in the specialization order.
-/
noncomputable
def coheightZeroSetOrderIsoIrreducibleComponents :
    {x : X | coheight x = 0} ≃o irreducibleComponents X := by
  have : {x : X | coheight x = 0} = {x : X | Maximal ⊤ x} := by simp [Maximal.top_iff_isMax]
  rw [irreducibleComponents_eq_maximals_closed, this]
  exact OrderIso.mapSetOfMaximal <| OrderIso.trans
    (OrderIso.trans (subtypeUnivOrderIso (by aesop : ∀ x : X, ⊤))
    (irreducibleSetEquivPoints (α := X)).symm) <|
    TopologicalSpace.IrreducibleCloseds.orderIsoSubtype' X
#find_home! subtypeUnivOrderIso
/--
For preorders `α` and `β`, if there is a strictly monotone function `f : WithTop α → β`, then if
`f x` has coheight `1`, then `x` has coheight `0`.
-/
lemma coheight_zero_of_coheight_one_of_strictMono
    {α β: Type*} [Preorder α] [Preorder β] (f : WithTop α → β) (hf : StrictMono f) (x : α)
    (h : coheight (f x) = 1) : coheight x = 0 := by
  suffices coheight (x : WithTop α) = 1 by
    simp only [coheight_coe_withTop] at this
    by_cases m : coheight x = ⊤
    · rw [m] at this
      contradiction
    · push_neg at m
      rw [ENat.ne_top_iff_exists] at m
      obtain ⟨a, ha⟩ := m
      rw [← ha] at this ⊢
      rw [← Nat.cast_one, ← ENat.coe_add, ENat.coe_inj] at this
      simpa using this
  exact le_antisymm (h ▸ coheight_le_coheight_apply_of_strictMono f hf ↑x) (by simp)

open Classical in
/--
For types `X, Y` where `Y` is a quasisober, irreducible space, we can lift a function `f : X → Y`
to a function `f' : WithTop X → Y` sending `⊤` to a generic point of `Y`.
-/
noncomputable
def QuasiSober.withTop_lift {X Y : Type*} [TopologicalSpace Y] [QuasiSober Y]
    [IrreducibleSpace Y]
    (f : X → Y) : WithTop X → Y :=
  fun a ↦ if h : a = ⊤ then genericPoint Y else f (WithTop.untop a h)

open Classical in
noncomputable
def withtop_map' {X Y : Type*} [Top Y]
    (f : X → Y) : WithTop X → Y :=
  fun a ↦ if h : a = ⊤ then ⊤ else f (WithTop.untop a h)

/--
Given topological space `X, Y` and a function `f : X → Y` which is stricly monotone with respect
to the specialziation order, `QuasiSober.withTop_lift f` is strictly monotone with respect to the
specialization order.
-/
local instance {X : Type*} [TopologicalSpace X] : Preorder X := specializationPreorder X in
lemma QuasiSober.withTop_lift_strictMono {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [QuasiSober Y] [IrreducibleSpace Y]
    (f : X → Y) (hf : @StrictMono _ _ (specializationPreorder X) (specializationPreorder Y) f)
    (hf2 : ∀ x : X, f x < genericPoint Y) :
    @StrictMono _ _ (@WithTop.preorder _ (specializationPreorder X)) (specializationPreorder Y)
    (QuasiSober.withTop_lift f) := fun a ↦ by aesop (add simp QuasiSober.withTop_lift)

variable {X : Type*} {p : Set X} [TopologicalSpace X]

/--
For a subset `p` of a topoological space `X`, `Subtype.val` is strictly monotone with respect to the
specialization order.
-/
lemma Specialization.strictMono_val :
    @StrictMono _ _ (specializationPreorder p) (specializationPreorder X) Subtype.val := by
  simp_all [specializationPreorder, subtype_specializes_iff, subtype_specializes_iff]
  exact fun _ _ h ↦ h

variable [QuasiSober X] [IrreducibleSpace X]

local instance {X : Type*} [TopologicalSpace X] : Preorder X := specializationPreorder X in
/--
In a quasisober, irreducible space `X`, if `p` is some non dense subset, then the generic point of
`X` specializes to any point of `p`.
-/
lemma QuasiSober.val_lt_genericPoint_of_closure_ne_top (hp : closure p ≠ ⊤) :
    ∀ x : p, @LT.lt X (specializationPreorder X).toLT (Subtype.val x) (genericPoint X) := by
  simp_all only [Set.top_eq_univ, ne_eq, specializationPreorder, Subtype.forall]
  refine fun x hx ↦ ⟨genericPoint_specializes x, fun h ↦ ?_⟩
  have : closure {Subtype.val ⟨x, hx⟩} ⊆ closure p := closure_mono (by simp [hx])
  simp_all [specializes_iff_closure_subset]

variable [T0Space X]
/--
Note this is NOT USED ANYWHERE. I think it could be useful to have in the library, but it doesn't
belong in PRs relating to cycles.
-/
lemma thingo (x : X) (hx : x ⤳ genericPoint X) : x = genericPoint X := IsGenericPoint.eq
    (le_antisymm (by simp) (by simpa [specializes_iff_closure_subset] using hx))
    (by simp [IsGenericPoint] : IsGenericPoint (genericPoint X) ⊤)

local instance {X : Type*} [TopologicalSpace X] : Preorder X := specializationPreorder X in
omit [T0Space X] in
/--
In a quasisober, irreducible space `X`, any set `p` which is not dense satisfies that the
set of points in `X` which lie in `p` and have coheight `1` in the specialization order on `X` have
coheight `0` in the specialization order on `p`.
-/
lemma QuasiSober.coheight_eq_zero_subset_of_coheight_eq_one (hp : closure p ≠ ⊤) :
    {x : X | x ∈ p ∧ coheight x = 1} ⊆ Subtype.val '' {x : p | coheight x = 0} := by
  simp only [Set.subset_def, Set.mem_setOf_eq, Set.mem_image,
    Subtype.exists, exists_and_right, exists_eq_right, and_imp]
  intro x hx kx
  use hx
  convert @coheight_zero_of_coheight_one_of_strictMono (Subtype p) X
    (specializationPreorder (Subtype p)) (specializationPreorder X)
    (QuasiSober.withTop_lift (Subtype.val : Subtype p → X))
    (QuasiSober.withTop_lift_strictMono (Subtype.val : Subtype p → X)
    Specialization.strictMono_val <| QuasiSober.val_lt_genericPoint_of_closure_ne_top hp) ⟨x, hx⟩ kx
  simp only [Subtype.preorder, Preorder.lift, specializationPreorder]
  ext a b
  exact (subtype_specializes_iff b a).symm
