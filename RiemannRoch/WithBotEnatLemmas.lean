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



lemma WithBot.add_iSup {ι : Sort*} [Nonempty ι] {a : WithBot ℕ∞} (f : ι → WithBot ℕ∞) :
a + ⨆ i, f i = ⨆ i, a + f i := by
  refine le_antisymm ?_ <| iSup_le fun i ↦ add_le_add_left (le_iSup ..) _

  obtain m | hf := eq_or_ne (⨆ i, f i) ⊥
  · simp[m]
  cases a
  · simp
  · rename_i a
    simp only [ne_eq, iSup_eq_bot, not_forall, WithBot.ne_bot_iff_exists] at hf
    obtain ⟨i, n, hn⟩ := hf
    cases a
    · apply le_top.trans
      rw[le_iSup_iff]
      intro l hl
      specialize hl i
      simp[hn.symm, ←WithBot.coe_top, ←WithBot.coe_add] at hl
      simpa using hl
    · rename_i a

      let g : ι → ℕ∞ := fun i ↦ WithBot.unbot' 0 (f i)

      trans ((a : ℕ∞) : WithBot ℕ∞) + ⨆ i, g i
      · suffices ⨆ i, f i ≤ ⨆ i, g i by
          exact add_le_add_left this ↑↑a
        simp[g, WithBot.le_coe_iff, le_iSup_iff]
        intro j m hm b hb
        specialize hb j
        simp[hm] at hb
        exact hb
      trans (((⨆ i, a + g i) : ℕ∞) : WithBot ℕ∞)
      · simp[WithBot.le_coe_iff, le_iSup_iff]
        intro b hb c hc
        simp[←WithBot.coe_add] at hb
        have : a + ⨆ i, g i ≤ c := by
          intro k hk
          cases b
          · simp only [ENat.some_eq_coe]
            subst hk
            simp_all only [ENat.some_eq_coe]
            suffices False by exact False.elim this
            have : ↑a + ⨆ i, g i ≤ k := by simpa[ENat.add_iSup]
            simp_all
          · rename_i b
            use b
            subst hk
            simp[hc]
            constructor
            · assumption
            · simp_all
              suffices (b : ℕ∞) ≤ k by
                exact ENat.coe_le_coe.mp this
              have : ↑a + ⨆ i, g i ≤ k := by simpa[ENat.add_iSup]
              rw[hb] at this
              exact this
        exact le_of_eq_of_le (id (Eq.symm hb)) this

      trans ⨆ i, ((a : ℕ∞) : WithBot ℕ∞) + g i
      · simp[WithBot.coe_le_iff, le_iSup_iff]
        intro b hb
        obtain m | hb' := eq_or_ne b ⊥
        · subst m
          simp_all
        · have : ∃ b' : ℕ∞, b = b' := by
            exact Option.ne_none_iff_exists'.mp hb'
          obtain ⟨b', hb'⟩ := this
          use b'
          constructor
          · assumption
          · exact fun i ↦ (fun a_1 ↦ (WithBot.coe_le a_1).mp) hb' (hb i)
      · simp
        intro j
        rw[le_iSup_iff]
        intro b hb
        obtain m | hfj := eq_or_ne (f j) ⊥

        · specialize hb i
          simp[m, ←hn, g] at hb ⊢
          apply le_trans _ hb
          norm_cast
          exact le_self_add
        specialize hb j
        suffices g j = f j by rwa[this]
        dsimp only [g]
        revert hfj
        generalize f j = x
        cases x
        all_goals simp

lemma WithBot.iSup_add {ι : Sort*} [Nonempty ι] {a : WithBot ℕ∞} (f : ι → WithBot ℕ∞) :
    (⨆ i, f i) + a = ⨆ i, f i + a := by simp [add_comm, WithBot.add_iSup]

theorem WithBot.iSup_le_add {ι ι': Sort*} [Nonempty ι] [Nonempty ι']
  {f : ι → WithBot ℕ∞} {g : ι' → WithBot ℕ∞} {a : WithBot ℕ∞} :
iSup f + iSup g ≤ a ↔ ∀ (i: ι) (j : ι'), f i + g j ≤ a := by
  simp_rw [WithBot.iSup_add, WithBot.add_iSup]
  exact iSup₂_le_iff
