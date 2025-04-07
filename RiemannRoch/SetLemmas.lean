import Batteries
import Mathlib
--import Mathlib.Data.Set.Basic

#check Set.ssubset_def

/-

refine ⟨h.subset, ?_⟩
      rwa[←Set.ssubset_iff_of_subset h.subset]
      -/

/-
lemma _root_.Set.ssubset_iff_exists.{u} {α : Type u} {s t : Set α} :
  s ⊂ t ↔ s ⊆ t ∧ ∃ x ∈ t, x ∉ s :=
  ⟨fun h ↦ ⟨h.le, Set.exists_of_ssubset h⟩, fun ⟨h1, h2⟩ ↦ (Set.ssubset_iff_of_subset h1).mpr h2⟩-/

  /-by

    constructor
    · intro h; exact ⟨h.le, Set.exists_of_ssubset h⟩
    · rintro ⟨h1, h2⟩
      rwa[Set.ssubset_iff_of_subset h1]-/

theorem Set.range_intersection_ssubset_iff_preimage_ssubset {A B : Type*} {f : A → B} {S S' : Set B} :
  Set.range f ∩ S ⊂ Set.range f ∩ S' ↔ f ⁻¹' S ⊂ f ⁻¹' S' := by
    simp only [Set.ssubset_iff_exists]
    apply and_congr
    · constructor
      all_goals
        intro r x hx
        simp_all only [subset_inter_iff, inter_subset_left, true_and, mem_preimage,
         mem_inter_iff, mem_range, true_and]
        aesop
    · aesop
