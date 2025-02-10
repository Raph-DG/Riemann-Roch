import Batteries.Tactic.ShowUnused
import Mathlib

lemma _root_.Set.ssubset_iff_exists.{u} {α : Type u} {s t : Set α} :
  s ⊂ t ↔ s ⊆ t ∧ ∃ x ∈ t, x ∉ s := by
    constructor
    · intro h
      refine ⟨h.subset, ?_⟩
      rwa[←Set.ssubset_iff_of_subset h.subset]
    · rintro ⟨h1, h2⟩
      rwa[Set.ssubset_iff_of_subset h1]

theorem Set.preimage_mono_of_range_intersection {A B : Type*} {f : A → B} {S S' : Set B} :
  Set.range f ∩ S ⊂ Set.range f ∩ S' ↔ f ⁻¹' S ⊂ f ⁻¹' S' := by
    rw[Set.ssubset_iff_exists, Set.ssubset_iff_exists]
    apply and_congr
    · constructor
      · rintro r x hx
        simp_all only [subset_inter_iff, inter_subset_left, true_and, mem_preimage]
        aesop
      · rintro r x hx
        simp_all only [mem_inter_iff, mem_range, exists_apply_eq_apply, and_self]
        aesop
    · aesop
