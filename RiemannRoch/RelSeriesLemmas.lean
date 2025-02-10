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



  /--
  Given an LTSeries rs, there always exists an LTSeries xs with xs.length ≥ rs.length and
  the head of xs equal to ⊥ and the last of xs equal to ⊤.
  -/
  theorem RelSeries.exists_ltSeries_ge_head_bot_last_top
  (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b))
  : ∃ xs : RelSeries (α := Submodule R M) (· < ·),
    xs.length ≥ rs.length ∧ xs.head = ⊥ ∧ xs.last = ⊤ := by
    by_cases h : rs.head = ⊥
    · by_cases q : rs.last = ⊤
      · use rs
      · have : rs.last < ⊤ := by exact Ne.lt_top' fun a ↦ q (id (Eq.symm a))
        use rs.snoc ⊤ this
        aesop
    · have : ⊥ < rs.head := by exact Ne.bot_lt' fun a ↦ h (id (Eq.symm a))
      by_cases q : rs.last = ⊤
      · use rs.cons ⊥ this
        aesop
      · let this' : (rs.cons ⊥ this).last < ⊤ := by
          simp only [last_cons]
          exact Ne.lt_top' fun a ↦ q (id (Eq.symm a))
        use (rs.cons ⊥ this).snoc ⊤ this'
        simp only [snoc_length, cons_length, ge_iff_le, head_snoc, head_cons, last_snoc, and_self,
          and_true]
        omega


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

      have kernelInt : LinearMap.ker S.g.hom ⊓ (rs.toFun i.castSucc) < LinearMap.ker S.g.hom ⊓ (rs.toFun i.succ) := by

       have p' : Submodule.map S.g.hom (rs.toFun i.castSucc) = Submodule.map S.g.hom (rs.toFun i.succ) :=
        by aesop
       have ans := LinearMap.ker_intersection_mono_of_map_eq (rs.step i) p'
       aesop

      have exactness : LinearMap.ker S.g.hom = LinearMap.range S.f.hom := by
        have proof := CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hS.exact
        exact id (Eq.symm proof)

      rw[exactness] at kernelInt

      simp_all

      have intLem (k : Fin (rs.length + 1)) :
       (rs.submoduleComap S.f.hom).toFun k = Submodule.comap S.f.hom (LinearMap.range S.f.hom ⊓ rs.toFun k) :=
         by aesop
      rw[intLem i.castSucc, intLem i.succ]

      have lem := Set.preimage_mono_of_range_intersection.mp kernelInt
      simp
      have comap_range : Submodule.comap S.f.hom (LinearMap.range S.f.hom) = ⊤ := by aesop
      rw[comap_range]
      simp
      exact lem


    theorem RelSeries.submodule_map_lt_of_comap_eq_exact {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS : S.ShortExact)
    (rs : RelSeries (α := Submodule R S.X₂) (· < ·)) (i : Fin rs.length)
    (p : (rs.submoduleComap S.f.hom).toFun i.castSucc = (rs.submoduleComap S.f.hom).toFun i.succ)
    : (rs.submoduleMap S.g.hom).toFun i.castSucc < (rs.submoduleMap S.g.hom).toFun i.succ := by

      let exactness : LinearMap.range S.f.hom = LinearMap.ker S.g.hom :=
        CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hS.exact

      let imInt : LinearMap.range S.f.hom ⊓ (rs.toFun i.castSucc) = LinearMap.range S.f.hom ⊓ (rs.toFun i.succ) := by
        rw[← Submodule.map_comap_eq, ←Submodule.map_comap_eq]
        exact congrArg (Submodule.map S.f.hom) p


      rw[exactness] at imInt

      simp_all

      let intLem (k : Fin (rs.length + 1)) :
        (rs.submoduleMap S.g.hom).toFun k = Submodule.map S.g.hom (rs.toFun k) := by aesop
      rw[intLem i.castSucc, intLem i.succ]

      exact LinearMap.map_mono_of_ker_intersection_eq (rs.step i) imInt

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
