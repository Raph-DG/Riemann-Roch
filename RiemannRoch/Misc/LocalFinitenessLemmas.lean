import Mathlib

open Topology Set Function

variable
  {X : Type*} [TopologicalSpace X] {U : Set X}
  {Y : Type*}

lemma supportLocallyFiniteWithin_top_iff [Zero Y] (f : X → Y) :
    (∀ z : X, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support)) ↔
    LocallyFinite (fun s : f.support ↦ ({s.val} : Set X)) := by
  have lem {α : Type u_1} (s t : Set α) : (s ∩ t) = {i : s | ↑i ∈ t} := by aesop
  constructor
  all_goals intro h z
            obtain ⟨t, ht⟩ := h z
            use t
            refine ⟨ht.1, ?_⟩
            have ans := ht.2
  · simp only [lem t f.support, mem_support, ne_eq, Subtype.coe_image,
              mem_setOf_eq, exists_prop, singleton_inter_nonempty] at ans ⊢
    have : {x | x ∈ t ∧ ¬f x = 0} =
            Subtype.val '' {i : { x // ¬f x = 0 } | ↑i ∈ t} := by aesop
    rw [this] at ans
    convert ans
    apply Equiv.set_finite_iff
    exact BijOn.equiv (Subtype.val) (InjOn.bijOn_image injOn_subtype_val)
  · simp only [singleton_inter_nonempty] at ans ⊢
    have : {i : f.support | ↑i ∈ t} = t ∩ f.support := by aesop
    rw [← this]
    exact Finite.image Subtype.val ans

lemma supportLocallyFiniteWithin_top_inter_compact_finite {W : Set X}
   [Zero Y] {f : X → Y} (hf : ∀ z : X, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support))
   (hW : IsCompact W) : (W ∩ f.support).Finite := by
  have := LocallyFinite.finite_nonempty_inter_compact
    ((supportLocallyFiniteWithin_top_iff f).mp hf) hW
  have lem {α : Type u_1} (s t : Set α) : {i : s | ({↑i} ∩ t).Nonempty} = (t ∩ s) := by aesop
  rw [← lem f.support W]
  exact Finite.image Subtype.val this

noncomputable
def LocallyFinsupp.degree [h : CompactSpace X] [Zero Y] [AddCommMonoid Y] {f : X → Y}
    (hf : ∀ z : X, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support)) : Y :=
  ∑ (i ∈ (supportLocallyFiniteWithin_top_inter_compact_finite hf h.1).toFinset), f i
