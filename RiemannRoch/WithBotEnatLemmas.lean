import Mathlib.Order.KrullDimension
import Mathlib.Order.JordanHolder
import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.FiniteLength
import Mathlib.Data.ENat.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Group
import RiemannRoch.trimmedLength



open AlgebraicGeometry
open CategoryTheory
open Opposite.op
open Module
open Order
open Ring


/-
This doesn't feel like the right level of generality.
At the same time it doesn't feel that bad either, so I'm not sure

I really don't know if this or the other proof we had is better. I think one thing to note
here is that this really ought to be a statement about just Withbot anything rather than
ℕ∞ necessarily.



This will probably work if instead of using
-/
/--/
lemma test' {α : Type*} {ι : Sort*} [ConditionallyCompleteLattice α] [Nonempty ι] {f : ι → WithBot (WithTop α)} (ex : ∃ i, f i ≠ ⊥) :
    ⨆ i, f i = ⨆ i, (WithBot.unbot' ⊥ (f i) : WithTop α) := by
  rw[WithBot.coe_iSup]
  #check @iSup_eq_of_forall_le_of_forall_lt_exists_gt (WithBot (WithTop α)) ι (@WithBot.WithTop.completeLattice α (by infer_instance)) --f := f) --(α := WithBot α) (f := f) (b := ⨆ i, (WithBot.unbot' ⊥ (f i) : α))--(b := (⨆ i : ι, (@WithBot.some α (WithBot.unbot' ⊥ (f i))))
  rw[iSup_eq_of_forall_le_of_forall_lt_exists_gt (ι := ι) (f := f) (b := ((⨆ i, (WithBot.unbot' ⊥ (f i) : WithTop α)) : WithBot (WithTop α)))]
  exact OrderTop.bddAbove (Set.range fun i ↦ WithBot.unbot' ⊥ (f i))-/
  /-
    · intro i
      by_cases o : (f i = ⊥)
      · rw[o]; simp
      · have : ↑(WithBot.unbot' 0 (f i)) = f i := by
          cases k : (f i)
          · contradiction
          · rfl
        rw[← this]
        exact le_iSup_iff.mpr fun b a ↦ a i
    · intro w hw
      obtain ⟨i, hi⟩ := lt_iSup_iff.mp hw
      by_cases o : (f i = ⊥)
      · obtain ⟨j, hj⟩ := ex
        use j
        have : f j ≥ 0 := by
          cases k : (f j)
          · contradiction
          · simp
        apply lt_of_lt_of_le (b := 0)
        · simp[o] at hi
          assumption
        · exact this
      · use i
        simp_all
        have : ↑(WithBot.unbot' 0 (f i)) = f i := by
          cases k : (f i)
          · contradiction
          · rename_i a
            exact rfl
        rw[←this]
        exact hi
  · exact OrderTop.bddAbove (Set.range fun i ↦ WithBot.unbot' ⊥ (f i))--exact OrderTop.bddAbove (Set.range fun i ↦ WithBot.unbot' 0 (f i))-/

lemma WithBot.coe_unbot'_iSup {ι : Sort*} [Nonempty ι] {f : ι → WithBot ℕ∞} (ex : ∃ i, f i ≠ ⊥) :
    ⨆ i, f i = ⨆ i, (WithBot.unbotD 0 (f i) : ℕ∞) := by
  rw[WithBot.coe_iSup]
  · rw[iSup_eq_of_forall_le_of_forall_lt_exists_gt]
    · intro i
      by_cases o : (f i = ⊥)
      · rw[o]; simp
      · have : ↑(WithBot.unbotD 0 (f i)) = f i := by
          cases k : (f i)
          · contradiction
          · exact rfl
        rw[← this]
        exact le_iSup_iff.mpr fun b a ↦ a i
    · intro w hw
      obtain ⟨i, hi⟩ := lt_iSup_iff.mp hw
      by_cases o : (f i = ⊥)
      · obtain ⟨j, hj⟩ := ex
        use j
        have : f j ≥ 0 := by
          cases k : (f j)
          · contradiction
          · simp
        apply lt_of_lt_of_le (b := 0)
        · simp[o] at hi
          assumption
        · exact this
      · use i
        simp_all
        have : ↑(WithBot.unbotD 0 (f i)) = f i := by
          cases k : (f i)
          · contradiction
          · rename_i a
            exact rfl
        rw[←this]
        exact hi
  · exact OrderTop.bddAbove (Set.range fun i ↦ WithBot.unbotD 0 (f i))

lemma WithBot.add_iSup {ι : Sort*} [Nonempty ι] {a : WithBot ℕ∞} (f : ι → WithBot ℕ∞) :
    a + ⨆ i, f i = ⨆ i, a + f i := by
  refine le_antisymm ?_ <| iSup_le fun i ↦ add_le_add_left (le_iSup ..) _
  obtain m | hf := eq_or_ne (⨆ i, f i) ⊥
  · simp[m]
  cases a
  · simp
  · rename_i a
    let g : ι → ℕ∞ := fun i ↦ WithBot.unbotD 0 (f i)
    have h1 : ∀ i, unbotD 0 (f i) = f i ∨ f i = ⊥ := by
      intro i
      cases (f i)
      · exact add_eq_bot.mp rfl
      · exact unbotD_eq_self_iff.mp rfl
    have enatStat := ENat.add_iSup (fun i ↦ WithBot.unbotD 0 (f i)) (a := a)
    simp at hf
    rw[WithBot.coe_unbot'_iSup hf]
    obtain ⟨x, hx⟩ := hf
    simp[WithBot.ne_bot_iff_exists] at hx
    obtain ⟨fx, hfx⟩ := hx

    rw[← WithBot.coe_add, enatStat, WithBot.coe_iSup]
    · simp only [coe_add, iSup_le_iff]
      intro i
      obtain h | h := h1 i
      · rw[h]
        exact le_iSup_iff.mpr fun b a ↦ a i
      · simp[h]
        refine le_iSup_iff.mpr ?_
        intro b j
        specialize j x
        have : unbotD 0 (f x) = f x := by
          nth_rw 2 [←(WithBot.unbotD_coe 0 (f x))]
          rw[←hfx]
          rfl
        have : f x ≥ 0 := by
          rw[←hfx]
          simp[zero_le fx]
        exact le_trans (b := (↑a + f x)) (le_add_of_nonneg_right this) j
    · exact OrderTop.bddAbove (Set.range fun i ↦ a + unbotD 0 (f i))


lemma WithBot.iSup_add {ι : Sort*} [Nonempty ι] {a : WithBot ℕ∞} (f : ι → WithBot ℕ∞) :
    (⨆ i, f i) + a = ⨆ i, f i + a := by simp [add_comm, WithBot.add_iSup]

theorem WithBot.iSup_le_add {ι ι': Sort*} [Nonempty ι] [Nonempty ι']
  {f : ι → WithBot ℕ∞} {g : ι' → WithBot ℕ∞} {a : WithBot ℕ∞} :
iSup f + iSup g ≤ a ↔ ∀ (i: ι) (j : ι'), f i + g j ≤ a := by
  simp_rw [WithBot.iSup_add, WithBot.add_iSup]
  exact iSup₂_le_iff
