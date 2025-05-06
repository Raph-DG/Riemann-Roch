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
import Batteries.Tactic.ShowUnused

import RiemannRoch.SetLemmas
import RiemannRoch.LinearMapLemmas



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


  theorem RelSeries.exists_ltSeries_ge_head_bot
  (rs : RelSeries (α := Submodule R M) (· < ·)) :
  ∃ xs : RelSeries (α := Submodule R M) (· < ·),
  xs.length ≥ rs.length ∧ xs.head = ⊥ ∧ xs.last = rs.last :=
    Or.elim (em (rs.head = ⊥)) (by aesop)
    (by intro h; use cons rs ⊥ (by exact Ne.bot_lt' fun a ↦ h (id (Eq.symm a))); simp)
      #min_imports

  theorem RelSeries.exists_ltSeries_le_last_top
  (rs : RelSeries (α := Submodule R M) (· < ·)) :
  ∃ xs : RelSeries (α := Submodule R M) (· < ·),
  xs.length ≥ rs.length ∧ xs.last = ⊤ ∧ xs.head = rs.head :=
    Or.elim (em (rs.last = ⊤)) (by aesop)
    (by intro h; use snoc rs ⊤ (by exact Ne.lt_top' fun a ↦ h (id (Eq.symm a))); simp)

  /--
  Given an LTSeries rs, there always exists an LTSeries xs with xs.length ≥ rs.length and
  the head of xs equal to ⊥ and the last of xs equal to ⊤.
  -/
  theorem RelSeries.exists_ltSeries_ge_head_bot_last_top
  (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b))
  : ∃ xs : RelSeries (α := Submodule R M) (· < ·),
    xs.length ≥ rs.length ∧ xs.head = ⊥ ∧ xs.last = ⊤ := by
    obtain ⟨rs', hrs'⟩ := rs.exists_ltSeries_ge_head_bot
    obtain ⟨rs'', hrs''⟩ := rs'.exists_ltSeries_le_last_top
    use rs''; exact ⟨le_trans hrs'.1 hrs''.1, by aesop⟩


  def RelSeries.submoduleMap (rs : RelSeries (α := Submodule R M) (· < ·))
    (f : M →ₗ[R] M') : RelSeries (α := Submodule R M') (· ≤ ·) :=
      RelSeries.map rs {toFun := Submodule.map f, map_rel' := fun a ↦ Submodule.map_mono (a.le)}

  def RelSeries.submoduleComap (rs : RelSeries (α := Submodule R M') (· < ·))
    (f : M →ₗ[R] M') : RelSeries (α := Submodule R M) (· ≤ ·) :=
      RelSeries.map rs {toFun := Submodule.comap f, map_rel' := fun a ↦ Submodule.comap_mono (a.le)}


  theorem RelSeries.submodule_comap_lt_of_map_eq_exact
    {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS : S.ShortExact)
    (rs : RelSeries (α := Submodule R S.X₂) (· < ·)) (i : Fin rs.length)
    (p : (rs.submoduleMap S.g.hom).toFun i.castSucc = (rs.submoduleMap S.g.hom).toFun i.succ)
    : (rs.submoduleComap S.f.hom).toFun i.castSucc < (rs.submoduleComap S.f.hom).toFun i.succ := by
      have kernelInt : LinearMap.ker S.g.hom ⊓ (rs.toFun i.castSucc) <
        LinearMap.ker S.g.hom ⊓ (rs.toFun i.succ) :=
          LinearMap.ker_intersection_mono_of_map_eq (rs.step i) (by aesop)
      rw[← CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hS.exact] at kernelInt
      apply Set.range_intersection_ssubset_iff_preimage_ssubset.mp kernelInt



    theorem RelSeries.submodule_map_lt_of_comap_eq_exact
        {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS : S.ShortExact)
        (rs : RelSeries (α := Submodule R S.X₂) (· < ·)) (i : Fin rs.length)
        (p : (rs.submoduleComap S.f.hom).toFun i.castSucc =
        (rs.submoduleComap S.f.hom).toFun i.succ) :
        (rs.submoduleMap S.g.hom).toFun i.castSucc < (rs.submoduleMap S.g.hom).toFun i.succ := by
      have imInt : LinearMap.range S.f.hom ⊓ (rs.toFun i.castSucc) =
                   LinearMap.range S.f.hom ⊓ (rs.toFun i.succ) := by
        rw[← Submodule.map_comap_eq, ←Submodule.map_comap_eq]
        exact congrArg (Submodule.map S.f.hom) p
      rw[CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hS.exact] at imInt
      apply LinearMap.map_mono_of_ker_intersection_eq (rs.step i) imInt


  /-
  Note: this is just a rewriting of the definition of smash which yields a more general notion
  of concatenation. In principal I think smash should be defined in terms of concat but it might
  be annoying to do this replacement in practice.
  -/
  def RelSeries.concat {α : Type*} {r : Rel α α} (p q : RelSeries r) (connect : r p.last q.head) : RelSeries r where
  length := p.length + q.length + 1
  toFun i :=
    if H : i.1 < p.length + 1
    then p ⟨i.1, H⟩
    else q ⟨i.1 - (p.length + 1),
            Nat.sub_lt_left_of_lt_add (by rwa [not_lt] at H)
            (by rw [← add_assoc]; ring_nf at i; omega)⟩
  step i := by
    dsimp only
    by_cases h₂ : i.1 + 1 < p.length + 1
    · have h₁ : i.1 < p.length + 1 := by omega
      have h₁' : i.1 < p.length := by omega
      simp only [Fin.coe_castSucc, h₁, ↓reduceDIte, Fin.val_succ, add_lt_add_iff_right, h₁']
      exact p.step ⟨i, h₁'⟩
    · simp only [Fin.coe_castSucc, Fin.val_succ, h₂, ↓reduceDIte, Nat.reduceSubDiff]
      split_ifs with h₁
      · have h₃ : p.length = i.1 := by omega
        convert connect
        · simp_all only [lt_self_iff_false, not_false_eq_true]
          have check : p.last = p.toFun (p.length) := by simp[RelSeries.last]
          rw[check]
          apply congr_arg
          apply Fin.eq_of_val_eq
          simpa using h₃.symm
        · simp_all only [lt_add_iff_pos_right, zero_lt_one, tsub_self, Fin.zero_eta]
          rfl

      · convert q.step ⟨i.1 - (p.length + 1), _⟩ using 1
        · congr
          omega
        · have imas : ↑i < p.length + 1 + q.length := by omega
          refine Nat.sub_lt_left_of_lt_add ?_ imas
          rwa [not_lt] at h₁
