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
import Batteries.Tactic.ShowUnused



open AlgebraicGeometry
open CategoryTheory
open Opposite.op
open Module
open Order
open Ring




section FL

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


  -- This should probably be for any relseries with a relation r satisfying r implies ≤
  def RelSeries.submoduleMap (rs : RelSeries (α := Submodule R M) (· < ·))
    (f : M →ₗ[R] M') : RelSeries (α := Submodule R M') (· ≤ ·) :=
      RelSeries.map rs {toFun := Submodule.map f, map_rel' := fun a ↦ Submodule.map_mono (a.le)}

  def RelSeries.submoduleComap (rs : RelSeries (α := Submodule R M') (· < ·))
    (f : M →ₗ[R] M') : RelSeries (α := Submodule R M) (· ≤ ·) :=
      RelSeries.map rs {toFun := Submodule.comap f, map_rel' := fun a ↦ Submodule.comap_mono (a.le)}

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


  theorem LinearMap.ker_intersection_mono_of_map_eq {A B : Submodule R M} {f :  M →ₗ[R] M'} (hab : A < B)
    (q : Submodule.map f A = Submodule.map f B) : LinearMap.ker f ⊓ A < LinearMap.ker f ⊓ B := by
      rw[lt_iff_le_and_ne]
      constructor
      · exact inf_le_inf le_rfl hab.le
      · intro H
        apply hab.ne
        apply le_antisymm hab.le
        intro x hx
        let y := f x
        have hy : y ∈ Submodule.map f B := by use x, hx
        rw[←q] at hy
        obtain ⟨z, hz, hzy⟩ := hy
        suffices x - z ∈ LinearMap.ker f ⊓ A by
          simpa using add_mem this.2 hz
        rw[H]
        constructor
        · simp[hzy]
        · apply sub_mem hx (hab.le hz)

  -- Since this is almost exactly the same proof this could probably be given a bit of a refactor,
  -- but that's alright
  theorem LinearMap.map_mono_of_ker_intersection_eq {A B : Submodule R M} {f :  M →ₗ[R] M'} (hab : A < B)
    (q : LinearMap.ker f ⊓ A = LinearMap.ker f ⊓ B) : Submodule.map f A < Submodule.map f B := by
      rw[lt_iff_le_and_ne]
      constructor
      · exact Set.image_mono hab.le
      · intro H
        apply hab.ne
        apply le_antisymm hab.le
        intro x hx
        let y := f x
        have hy : y ∈ Submodule.map f B := by use x, hx
        rw[←H] at hy
        obtain ⟨z, hz, hzy⟩ := hy
        suffices x - z ∈ LinearMap.ker f ⊓ A by
          simpa using add_mem this.2 hz
        rw[q]
        constructor
        · simp[hzy]
        · apply sub_mem hx (hab.le hz)


  theorem RelSeries.submodule_comap_lt_of_map_eq_exact
    {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS : S.ShortExact)
    (rs : RelSeries (α := Submodule R S.X₂) (· < ·)) (i : Fin rs.length)
    (p : (rs.submoduleMap S.g.hom).toFun i.castSucc = (rs.submoduleMap S.g.hom).toFun i.succ)
    : (rs.submoduleComap S.f.hom).toFun i.castSucc < (rs.submoduleComap S.f.hom).toFun i.succ := by

      have kernelInt : LinearMap.ker S.g.hom ⊓ (rs.toFun i) < LinearMap.ker S.g.hom ⊓ (rs.toFun (i+1)) := by
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
        rw[←Submodule.map_comap_eq, ←Submodule.map_comap_eq]
        exact congrArg (Submodule.map S.f.hom) p


      rw[exactness] at imInt

      simp_all

      let intLem (k : Fin (rs.length + 1)) :
        (rs.submoduleMap S.g.hom).toFun k = Submodule.map S.g.hom (rs.toFun k) := by aesop
      rw[intLem i.castSucc, intLem i.succ]

      exact LinearMap.map_mono_of_ker_intersection_eq (rs.step i) imInt





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

  variable (a b : ℕ∞)

  lemma WithBot.add_iSup {ι : Sort*} [Nonempty ι] {a : WithBot ℕ∞} (f : ι → WithBot ℕ∞) : a + ⨆ i, f i = ⨆ i,
     a + f i := by
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

  lemma WithBot.iSup_add {ι : Sort*} [Nonempty ι] {a : WithBot ℕ∞} (f : ι → WithBot ℕ∞) : (⨆ i, f i) + a = ⨆ i,
     f i + a := by simp [add_comm, WithBot.add_iSup]

  theorem WithBot.iSup_le_add {ι ι': Sort*} [Nonempty ι] [Nonempty ι']
   {f : ι → WithBot ℕ∞} {g : ι' → WithBot ℕ∞} {a : WithBot ℕ∞} :
  iSup f + iSup g ≤ a ↔ ∀ (i: ι) (j : ι'), f i + g j ≤ a := by
    simp_rw [WithBot.iSup_add, WithBot.add_iSup]
    exact iSup₂_le_iff
  #find_home! WithBot.iSup_le_add


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

#show_unused Module.length_additive
end FL
