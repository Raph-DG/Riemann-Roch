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
--import RiemannRoch.SetLemmas
import RiemannRoch.WithBotEnatLemmas
import RiemannRoch.RelSeriesLemmas

import Batteries.Tactic.ShowUnused



open AlgebraicGeometry
open CategoryTheory
open Opposite.op
open Module
open Order
open Ring

  variable {R : Type*}
           [Ring R]
           {M M' : Type*}
           [AddCommGroup M]
           [AddCommGroup M']
           [Module R M]
           [Module R M']



  open Classical in
  /--
  Given a short exact sequence S and rs : RelSeries (α := Submodule R S.X₂) (· < ·),
  we have that the length of rs is bounded above by the trimmed length of rs.submoduleMap S.g.hom
  plus the trimmed length of rs.submoduleComap S.f.hom.

  This is the main ingredient in our proof that the module length is additive.
  -/
  theorem RelSeries.trimmedLength_additive
    {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS : S.ShortExact)
      (rs : RelSeries (α := Submodule R S.X₂) (· < ·)) :
      rs.length ≤ RelSeries.trimmedLength (rs.submoduleMap S.g.hom) +
                  RelSeries.trimmedLength (rs.submoduleComap S.f.hom) := by
        induction' o : rs.length with n ih generalizing rs
        · aesop
        · let n' : Fin (rs.length) := {val := n, isLt := by rw[o] ; exact lt_add_one n}
          have rserasedLen : rs.eraseLast.length = n := by aesop
          by_cases q : rs.submoduleMap S.g.hom (n'.castSucc) = rs.submoduleMap S.g.hom n'.succ
          · rw[RelSeries.trimmedLength_eraseLast_of_eq ⟨n', ⟨id q, id (Eq.symm o)⟩⟩]
            specialize ih rs.eraseLast rserasedLen
            have leftlt : ∃ i : Fin (rs.submoduleComap S.f.hom).length,
                (rs.submoduleComap S.f.hom).toFun i.castSucc <
                (rs.submoduleComap S.f.hom).toFun i.succ ∧
                ↑i + 1 = (rs.submoduleComap S.f.hom).length :=
                ⟨n', ⟨RelSeries.submodule_comap_lt_of_map_eq_exact hS rs n' q, o.symm⟩⟩
            rw[RelSeries.trimmedLength_eraseLast_of_lt leftlt]; exact Nat.add_le_add_right ih 1
          · rw[RelSeries.trimmedLength_eraseLast_of_lt
              ⟨n', ⟨lt_of_le_of_ne ((rs.submoduleMap S.g.hom).step n') q, id (Eq.symm o)⟩⟩]
            specialize ih rs.eraseLast rserasedLen
            suffices n + 1 ≤ (rs.submoduleMap S.g.hom).eraseLast.trimmedLength +
                             1 + (rs.submoduleComap S.f.hom).eraseLast.trimmedLength by
              exact le_add_of_le_add_left this
                (RelSeries.trimmedLength_eraseLast_le (rs.submoduleComap S.f.hom))
            ring_nf
            have proof := Nat.add_le_add_left ih 1
            ring_nf at proof; exact proof
  --#min_imports
  open Classical in
  /--
  The module length is additive in short exact sequences.
  -/
    theorem Module.length_additive
    {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
      Module.length R S.X₂ = Module.length R S.X₁ + Module.length R S.X₃ := by
    simp only [length, krullDim, le_antisymm_iff, iSup_le_iff]
    constructor
    · intro rs
      trans ↑((RelSeries.submoduleComap rs S.f.hom).trimmedLength +
             (RelSeries.submoduleMap rs S.g.hom).trimmedLength)
      · apply Nat.mono_cast
        have trimmedProof := RelSeries.trimmedLength_additive hS rs
        rwa[Nat.add_comm] at trimmedProof
      · have trimleft :=
          RelSeries.moduleLength_ge_trimmedLength (RelSeries.submoduleComap rs S.f.hom)
        have trimright :=
          RelSeries.moduleLength_ge_trimmedLength (RelSeries.submoduleMap rs S.g.hom)
        exact add_le_add trimleft trimright
    · rw[WithBot.iSup_le_add]
      intro rstemp rstemp'
      obtain ⟨rs, hrs⟩ := RelSeries.exists_ltSeries_ge_head_bot_last_top rstemp
      obtain ⟨rs', hrs'⟩ := RelSeries.exists_ltSeries_ge_head_bot_last_top rstemp'

      let gInv : RelSeries (fun (a : Submodule R S.X₂) (b : Submodule R S.X₂) => a < b) :=
        LTSeries.map rs' (Submodule.comap S.g.hom)
        (Submodule.comap_strictMono_of_surjective hS.moduleCat_surjective_g)

      let fIm : RelSeries (fun (a : Submodule R S.X₂) (b : Submodule R S.X₂) => a < b) :=
        LTSeries.map rs (Submodule.map S.f.hom)
        (Submodule.map_strictMono_of_injective hS.moduleCat_injective_f)

      have connect : fIm.last = gInv.head := by
        convert CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hS.exact
        · simp only [RelSeries.last, LTSeries.map_length, LTSeries.map_toFun, fIm]
          have obv : (rs.toFun (Fin.last rs.length)) = ⊤ := hrs.2.2
          rw[obv]; exact Submodule.map_top S.f.hom
        · simp only [RelSeries.head, LTSeries.map_toFun, gInv]
          have obv : rs'.toFun 0 = ⊥ := hrs'.2.1
          rw[obv]; exact rfl

      let smashfg := RelSeries.smash fIm gInv connect
      trans ↑smashfg.length
      · have this' : smashfg.length = rs.length + rs'.length := rfl
        rw[this']
        simp only [Nat.cast_add, ge_iff_le]
        refine add_le_add ?h₁ ?h₂
        all_goals simp only [Nat.cast_le, hrs.1, hrs'.1]
      · exact le_iSup_iff.mpr fun b a ↦ a smashfg

variable (R) (M) in
theorem Module.length_additive_of_quotient (N : Submodule R M) :
   Module.length R M = Module.length R N + Module.length R (M ⧸ N) := by
   let quotientSeq : CategoryTheory.ShortComplex (ModuleCat R) := {
     X₁ := ModuleCat.of R N
     X₂ := ModuleCat.of R M
     X₃ := ModuleCat.of R (M ⧸ N)
     f := ModuleCat.ofHom <| Submodule.subtype N
     g := ModuleCat.ofHom <| Submodule.mkQ N
     zero := by
       ext a
       simp
     }
   let ex : quotientSeq.ShortExact := {
     exact := by
       simp[CategoryTheory.ShortComplex.moduleCat_exact_iff]
       intro a b
       have X2 : ↑quotientSeq.X₂ = M := rfl
       have X1 : ↑quotientSeq.X₁ = @Subtype M fun x ↦ x ∈ N := rfl
       let a'' : N := {
         val := a
         property := (Submodule.Quotient.mk_eq_zero N).mp b
       }
       use a''
       aesop
     mono_f := by
       simp[quotientSeq]
       have : Function.Injective (N.subtype) := by exact Submodule.injective_subtype N
       exact (ModuleCat.mono_iff_injective (ModuleCat.ofHom N.subtype)).mpr this
     epi_g := by
       simp[quotientSeq]
       have : Function.Surjective (N.mkQ) := by exact Submodule.mkQ_surjective N
       exact (ModuleCat.epi_iff_surjective (ModuleCat.ofHom N.mkQ)).mpr this
   }
   have := Module.length_additive ex
   aesop
