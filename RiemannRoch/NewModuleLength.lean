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
import RiemannRoch.SetLemmas
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
        · let n' : Fin (rs.length) := {val := n, isLt := by aesop}
          by_cases q : rs.submoduleMap S.g.hom (n'.castSucc) = rs.submoduleMap S.g.hom n'.succ
          · let n' : Fin (rs.length) := {val := n, isLt := by rw[o] ; exact lt_add_one n}

            let leleft := RelSeries.submodule_comap_lt_of_map_eq_exact hS rs n' q
            simp at leleft


            let obv : (rs.submoduleMap S.g.hom).length > 0 := by exact Fin.pos n'

            have qcoe' : ∃ i : Fin (rs.submoduleMap S.g.hom).length,
                (rs.submoduleMap S.g.hom).toFun i.castSucc = (rs.submoduleMap S.g.hom).toFun i.succ ∧
                ↑i + 1 = (rs.submoduleMap S.g.hom).length := by
                use n'
                exact ⟨id q, id (Eq.symm o)⟩

            rw[RelSeries.trimmedLength_eraseLast_of_eq qcoe']


            have rserasedLen : rs.eraseLast.length = n := by aesop

            have iherased := ih rs.eraseLast rserasedLen

            have leftlt : ∃ i : Fin (rs.submoduleComap S.f.hom).length,
                (rs.submoduleComap S.f.hom).toFun i.castSucc < (rs.submoduleComap S.f.hom).toFun i.succ ∧
                ↑i + 1 = (rs.submoduleComap S.f.hom).length := by
                use n'
                exact ⟨leleft, id (Eq.symm o)⟩



            rw[RelSeries.trimmedLength_eraseLast_of_lt leftlt]
            exact Nat.add_le_add_right iherased 1


          · have q' : rs.submoduleMap S.g.hom n'.castSucc < (rs.submoduleMap S.g.hom).toFun n'.succ := by
              let leq := (rs.submoduleMap S.g.hom).step n'
              exact lt_of_le_of_ne leq q

            have q'' :
              ∃ i : Fin (rs.length),
              (rs.submoduleMap S.g.hom) (i.castSucc) <
              (rs.submoduleMap S.g.hom) i.succ ∧ (i + 1:ℕ) = rs.length := by
                use n'
                exact ⟨q', id (Eq.symm o)⟩


            have nonempt : (rs.submoduleMap S.g.hom).length > 0 := by exact Fin.pos n'
            rw[RelSeries.trimmedLength_eraseLast_of_lt q'']

            let rserasedLen : rs.eraseLast.length = n := by aesop

            let iherased := ih rs.eraseLast rserasedLen

            suffices n + 1 ≤ (rs.submoduleMap S.g.hom).eraseLast.trimmedLength +
                             1 + (rs.submoduleComap S.f.hom).eraseLast.trimmedLength by
              exact le_add_of_le_add_left this
                (RelSeries.trimmedLength_eraseLast_le (rs.submoduleComap S.f.hom))

            ring_nf

            let shouldProve := Nat.add_le_add_left iherased 1
            ring_nf at shouldProve
            exact shouldProve

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

      let trimmedProof := RelSeries.trimmedLength_additive hS rs


      let trimleft := RelSeries.moduleLength_ge_trimmedLength (RelSeries.submoduleComap rs S.f.hom)
      let trimright := RelSeries.moduleLength_ge_trimmedLength (RelSeries.submoduleMap rs S.g.hom)

      have inbet : (RelSeries.submoduleComap rs S.f.hom).trimmedLength +
        (RelSeries.submoduleMap rs S.g.hom).trimmedLength
        ≤ Module.length R S.X₁ + Module.length R S.X₃ := by exact add_le_add trimleft trimright


      apply le_trans (b := ↑((RelSeries.submoduleComap rs S.f.hom).trimmedLength + (RelSeries.submoduleMap rs S.g.hom).trimmedLength))

      apply Nat.mono_cast
      rw[Nat.add_comm] at trimmedProof
      exact trimmedProof
      exact inbet



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
        have gInvheadker : gInv.head = LinearMap.ker S.g.hom := by
          simp only [RelSeries.head, LTSeries.map_toFun, gInv]
          let obv : rs'.toFun 0 = ⊥ := by aesop
          rw[obv]
          exact rfl
        have fImLastRange : fIm.last = LinearMap.range S.f.hom := by
          simp only [RelSeries.last, LTSeries.map_length, LTSeries.map_toFun, fIm]
          let obv : (rs.toFun (Fin.last rs.length)) = ⊤ := by aesop
          rw[obv]
          exact Submodule.map_top S.f.hom


        simp_all only [fIm, fImLastRange, gInv, gInvheadker]
        exact CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hS.exact

      let smashfg := RelSeries.smash fIm gInv connect
      have : smashfg.length ≤ (@iSup (WithBot ℕ∞) (LTSeries (Submodule R ↑S.X₂)) WithBot.instSupSet fun p ↦ ↑p.length) := by
        exact le_iSup_iff.mpr fun b a ↦ a smashfg

      let this' : smashfg.length = rs.length + rs'.length := by aesop
      let step1 : rstemp.length + rstemp'.length ≤ @Nat.cast (WithBot ℕ∞) Semiring.toNatCast smashfg.length := by
          rw[this']
          simp
          refine add_le_add ?h₁ ?h₂
          simp[hrs.1]
          simp[hrs'.1]
      exact le_trans step1 this
