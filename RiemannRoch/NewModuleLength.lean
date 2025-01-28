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
import Mathlib.Order.ConditionallyCompleteLattice.Group
import RiemannRoch.trimmed_length


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




  def RelSeries.submoduleMap_injective {f : M →ₗ[R] M'} (hf : Function.Injective f)
      (s : RelSeries (α := Submodule R M) (· < ·)) :
      RelSeries (α := Submodule R M') (· < ·) := {
        length := s.length
        toFun := fun n => Submodule.map f (s.toFun n)
        step := by {
          let proof := Submodule.map_strictMono_of_injective hf
          intro i
          apply proof
          exact s.step i
        }
      }

  def RelSeries.submoduleComap_surjective {f : M →ₗ[R] M'} (hf : Function.Surjective f)
      (s : RelSeries (α := Submodule R M') (· < ·)) :
      RelSeries (α := Submodule R M) (· < ·) := {
        length := s.length
        toFun := fun n => Submodule.comap f (s.toFun n)
        step := by {
          let proof := Submodule.comap_strictMono_of_surjective hf
          intro i
          apply proof
          exact s.step i
        }
      }


  theorem RelSeries.chain_le_bot_top
  (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b))
  : ∃ xs : RelSeries (α := Submodule R M) (· < ·),
    xs.length ≥ rs.length ∧ xs.head = ⊥ ∧ xs.last = ⊤ := by
    obtain h | h := em (rs.head = ⊥)
    · obtain q | q := em (rs.last = ⊤)
      · use rs
      · have : rs.last < ⊤ := by exact Ne.lt_top' fun a ↦ q (id (Eq.symm a))
        use rs.snoc ⊤ this
        aesop
    · have : ⊥ < rs.head := by exact Ne.bot_lt' fun a ↦ h (id (Eq.symm a))
      obtain q | q := em (rs.last = ⊤)
      · use rs.cons ⊥ this
        aesop
      · let this' : (rs.cons ⊥ this).last < ⊤ := by
          simp
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





  theorem Set.preimage_mono_of_range_intersection {A B : Type*} {f : A → B} {S S' : Set B}
    (ltint : Set.range f ⊓ S < Set.range f ⊓ S') (lt : S ≤ S') : f ⁻¹' S < f ⁻¹' S' := by
      simp_all
      rw[Set.ssubset_def]
      rw[Set.ssubset_def] at ltint

      constructor
      apply Set.monotone_preimage
      exact lt
      intro opp
      let k : f ⁻¹' S ⊆ f ⁻¹' S' := by
        apply Set.monotone_preimage
        exact lt
      let jint : Set.range f ⊓ S = Set.range f ⊓ S' := by aesop
      let obv : ¬ (Set.range f ∩ S = Set.range f ∩ S') := by aesop
      exact obv jint


  theorem kernel_intersection {A B : Submodule R M} {f :  M →ₗ[R] M'} (hab : A < B)
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
  theorem kernel_intersection' {A B : Submodule R M} {f :  M →ₗ[R] M'} (hab : A < B)
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

 theorem image_intersection {A : Submodule R M'} {f :  M →ₗ[R] M'} :
   Submodule.map f (Submodule.comap f A) = (LinearMap.range f) ⊓ A := by
    aesop


  theorem RelSeries.submodule_comap_lt_of_map_eq_exact
    {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS : S.ShortExact)
    (rs : RelSeries (α := Submodule R S.X₂) (· < ·)) (i : Fin rs.length)
    --(p : (rs.submoduleMap S.g).toFun i = (rs.submoduleMap S.g).toFun (i+1))
    (p : (rs.submoduleMap S.g).toFun i.castSucc = (rs.submoduleMap S.g).toFun i.succ)
    : (rs.submoduleComap S.f).toFun i.castSucc < (rs.submoduleComap S.f).toFun i.succ := by

      have kernelInt : LinearMap.ker S.g ⊓ (rs.toFun i) < LinearMap.ker S.g ⊓ (rs.toFun (i+1)) := by
       have p' : Submodule.map S.g (rs.toFun i.castSucc) = Submodule.map S.g (rs.toFun i.succ) :=
        by aesop
       have ans := kernel_intersection (rs.step i) p'
       aesop

      have exactness : LinearMap.ker S.g = LinearMap.range S.f := by
        have proof := CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hS.exact
        exact id (Eq.symm proof)

      rw[exactness] at kernelInt

      simp_all

      have intLem (k : Fin (rs.length + 1)) :
       (rs.submoduleComap S.f).toFun k = Submodule.comap S.f (LinearMap.range S.f ⊓ rs.toFun k) :=
         by aesop
      rw[intLem i.castSucc, intLem i.succ]

      have lem := Set.preimage_mono_of_range_intersection kernelInt (le_of_lt (rs.step i))
      simp
      have comap_range : Submodule.comap S.f (LinearMap.range S.f) = ⊤ := by aesop
      rw[comap_range]
      simp
      exact lem


    theorem RelSeries.submodule_map_lt_of_comap_eq_exact {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS : S.ShortExact)
    (rs : RelSeries (α := Submodule R S.X₂) (· < ·)) (i : Fin rs.length)
    (p : (rs.submoduleComap S.f).toFun i.castSucc = (rs.submoduleComap S.f).toFun i.succ)
    : (rs.submoduleMap S.g).toFun i.castSucc < (rs.submoduleMap S.g).toFun i.succ := by

      let exactness : LinearMap.range S.f = LinearMap.ker S.g :=
        CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hS.exact

      let imInt : LinearMap.range S.f ⊓ (rs.toFun i.castSucc) = LinearMap.range S.f ⊓ (rs.toFun i.succ) := by
        rw[←image_intersection, ←image_intersection]
        exact congrArg (Submodule.map S.f) p


      rw[exactness] at imInt

      simp_all

      let intLem (k : Fin (rs.length + 1)) :
        (rs.submoduleMap S.g).toFun k = Submodule.map S.g (rs.toFun k) := by aesop
      rw[intLem i.castSucc, intLem i.succ]

      exact kernel_intersection' (rs.step i) imInt





  open Classical in
  theorem trimmed_length_additive
    {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS : S.ShortExact)
      (rs : RelSeries (α := Submodule R S.X₂) (· < ·)) :
      rs.length ≤ RelSeries.trimmed_length (rs.submoduleMap S.g) + RelSeries.trimmed_length (rs.submoduleComap S.f) := by

        induction' o : rs.length with n ih generalizing rs
        · aesop
        · -- Case match on the last ineqality in the seires on the right. If it's equality, then
          -- the guy on the left is < and we use our lemmas about trimmed length on eraseLast to
          -- get the job done. If instead we have < on the right, it's even easier because we get
          -- our lemma just by looking at the right series.
          let n' : Fin (rs.length) := {val := n, isLt := by aesop}
          by_cases q : rs.submoduleMap S.g (n'.castSucc) = rs.submoduleMap S.g n'.succ --(rs.submoduleMap S.g).toFun n = (rs.submoduleMap S.g).toFun (n + 1)
          · let n' : Fin (rs.length) := {val := n, isLt := by rw[o] ; exact lt_add_one n}

            let leleft := RelSeries.submodule_comap_lt_of_map_eq_exact hS rs n' q
            simp at leleft


            let obv : (rs.submoduleMap S.g).length > 0 := by exact Fin.pos n'

            have qcoe' : ∃ i : Fin (rs.length),
                (rs.submoduleMap S.g).toFun i.succ = (rs.submoduleMap S.g).toFun i.castSucc ∧
                ↑i + 1 = (rs.submoduleMap S.g).length := by
                use n'
                exact ⟨id (Eq.symm q), id (Eq.symm o)⟩

            rw[RelSeries.trimmed_length_eraseLast_of_eq obv qcoe']


            let rserasedLen : rs.eraseLast.length = n := by aesop

            let iherased := ih rs.eraseLast rserasedLen

            have leftlt : ∃ i : Fin (rs.length),
                (rs.submoduleComap S.f).toFun i.castSucc < (rs.submoduleComap S.f).toFun i.succ ∧
                ↑i + 1 = (rs.submoduleMap S.g).length := by
                use n'
                exact ⟨leleft, id (Eq.symm o)⟩




            have leftlength : (rs.submoduleComap S.f).length = n+1 := by aesop

            have nonempt : (rs.submoduleComap S.f).length > 0 := by aesop

            --#check RelSeries.trimmed_length_eraseLast_le
            rw[RelSeries.trimmed_length_eraseLast_of_lt nonempt leftlt]
            exact Nat.add_le_add_right iherased 1


          · have q' : rs.submoduleMap S.g n'.castSucc < (rs.submoduleMap S.g).toFun n'.succ := by
              let leq := (rs.submoduleMap S.g).step n'
              exact lt_of_le_of_ne leq q


            /-
            have q'' : (rs.submoduleMap S.g).toFun ((rs.submoduleMap S.g).length - 1) <
                      (rs.submoduleMap S.g).toFun ((rs.submoduleMap S.g).length) := by
              have leneq : (rs.submoduleMap S.g).length = rs.length := rfl
              simp_all
            -/

            have q'' :
              ∃ i : Fin (rs.length),
              (rs.submoduleMap S.g) (i.castSucc) <
              (rs.submoduleMap S.g) i.succ ∧ (i + 1:ℕ) = rs.length := by
                use n'
                exact ⟨q', id (Eq.symm o)⟩


            have nonempt : (rs.submoduleMap S.g).length > 0 := by exact Fin.pos n'
            rw[RelSeries.trimmed_length_eraseLast_of_lt nonempt q'']

            let rserasedLen : rs.eraseLast.length = n := by aesop

            let iherased := ih rs.eraseLast rserasedLen

            have makeIntoLemma : (rs.submoduleComap S.f).eraseLast.trimmed_length ≤
                                (rs.submoduleComap S.f).trimmed_length :=
            RelSeries.trimmed_length_eraseLast_le (rs.submoduleComap S.f) (by aesop)


            suffices n + 1 ≤ (rs.submoduleMap S.g).eraseLast.trimmed_length +
                             1 + (rs.submoduleComap S.f).eraseLast.trimmed_length by
              exact le_add_of_le_add_left this makeIntoLemma

            ring_nf

            let shouldProve := Nat.add_le_add_left iherased 1
            ring_nf at shouldProve
            exact shouldProve





  /-
  There is a very similar result about ENNReal which would be potentially useful to generalize,
  I think I could port their proof over without too much difficutly, but finding an appropriate
  geberalization for them both is proving to be kind of annoying.

  There is of course also the conditional lattice business which has similar lemmas assuming the
  addition is in a group and that the order has a kind of reverse cancellative property wrt to the
  addition, but it's unclear how to generalise this to the case we want, especially considering
  that in our application, we're not actually working with a monoid which embeds into it's
  "groupification", since a monoid needs to be cancellative for this to be the case which gets
  messed around by adding infinities
  -/

  -- Sps ⨆ i, f i = ⊥, then ⊥ ≥ f i for every i ∈ ι.
  -- Since ι nonempty, we must then have that f i = ⊥ for every i ∈ ι, so a + f i = a + ⊥ = ⊥, and so
  -- the supremum is ⊥ there too. So it should certainly be true.

  lemma withbot_isup_eq_bot_iff {ι : Sort*} [Nonempty ι] (f : ι → WithBot ℕ∞) :
     ⨆ i, f i = ⊥ ↔ ∀ i, f i = ⊥ := by
     constructor
     · intro h i
       rw[eq_bot_iff]
       rw[← h]
       exact le_iSup f i
     · intro h
       simp[h]

  variable (a b : ℕ∞)
  #check a - b
  #eval (⊤ : ℕ∞) - ⊤
  lemma add_iSup {ι : Sort*} [Nonempty ι] {a : WithBot ℕ∞} (f : ι → WithBot ℕ∞) : a + ⨆ i, f i = ⨆ i,
     a + f i := by
    /-
    The ENNReal proof had essentially this structure; case matching on whether or not a was equal
    to ∞, proving it easily when a is ∞ since a + ⊤ = ⊤ for any a and going from there.

    The problem here is that this is no longer true of ⊤ in WithBot ℕ∞ since ⊥ + ⊤ = ⊥. So, we can
    case match away a being ⊥, but if it's ⊤ then the sum could either be ⊤ or ⊥, which makes reasoning
    the ⊤ case out slightly more difficult.
    -/
    /-
    obtain rfl | ha := eq_or_ne a ⊥
    · --have : ∀ b : WithBot ℕ∞, ⊤ + b = ⊤ := by sorry
      simp-/
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
        ·

          sorry
        trans (((⨆ i, a + g i) : ℕ∞) : WithBot ℕ∞)
        sorry
        trans ⨆ i, ((a : ℕ∞) : WithBot ℕ∞) + g i
        · --simp

          sorry
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
          --simp[hfj] at hb ⊢
          --rw[WithBot.unbot'_coe]
          suffices g j = f j by rwa[this]
          dsimp only [g]
          revert hfj
          generalize f j = x
          cases x
          · simp
          · simp


    /-
    obtain m | ha := eq_or_ne a ⊥
    · simp[m]
    obtain m | ha' := eq_or_ne a ⊤
    · simp[m]

      --rw[←WithBot.coe_le_coe]

      simp only [←WithBot.coe_top, ←WithBot.coe_add]

      --rw[WithBot.coe_le_coe]




      sorry
    · --refine add_le_of_le_tsub_left_of_le (le_iSup_of_le (Classical.arbitrary _) le_self_add) ?_

      sorry-/
    --refine add_le_of_le_tsub_left_of_le (le_iSup_of_le (Classical.arbitrary _) le_self_add) ?_
    --exact iSup_le fun i ↦ ENNReal.le_sub_of_add_le_left ha <| le_iSup (a + f ·) i

  lemma iSup_add {ι : Sort*} [Nonempty ι] {a : WithBot ℕ∞} (f : ι → WithBot ℕ∞) : (⨆ i, f i) + a = ⨆ i,
     f i + a := by simp [add_comm, add_iSup]

  theorem iSup_le_add {ι ι': Sort*} [Nonempty ι] [Nonempty ι']
   {f : ι → WithBot ℕ∞} {g : ι' → WithBot ℕ∞} {a : WithBot ℕ∞} :
  iSup f + iSup g ≤ a ↔ ∀ (i: ι) (j : ι'), f i + g j ≤ a := by
    simp_rw [iSup_add, add_iSup]
    exact iSup₂_le_iff
    --simp[WithBot.instSupSet, ConditionallyCompleteLattice.toSupSet]


  /-
  Note: this is just a rewriting of the definition of smash which yields a more general notion
  of concatenation. In principal I think smash should be defined in terms of concat but it might
  be annoying to do this replacement in practice.
  -/
  def concat {α : Type*} {r : Rel α α} (p q : RelSeries r) (connect : r p.last q.head) : RelSeries r where
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
        · simp_all
          have check : p.last = p.toFun (p.length) := by simp[RelSeries.last]
          rw[check]
          apply congr_arg
          apply Fin.eq_of_val_eq
          simpa using h₃.symm
        · simp_all
          exact rfl

      · convert q.step ⟨i.1 - (p.length + 1), _⟩ using 1
        · congr
          omega
        · have imas : ↑i < p.length + 1 + q.length := by omega
          refine Nat.sub_lt_left_of_lt_add ?_ imas
          rwa [not_lt] at h₁


  open Classical in
    theorem Module.length_additive
    {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
      Module.length R S.X₂ = Module.length R S.X₁ + Module.length R S.X₃ := by


    simp only [length, krullDim, le_antisymm_iff, iSup_le_iff]

    constructor
    · intro rs

      let trimmedProof := trimmed_length_additive hS rs


      let trimleft := Module.length_ge_trimmed_length (RelSeries.submoduleComap rs S.f)
      let trimright := Module.length_ge_trimmed_length (RelSeries.submoduleMap rs S.g)

      have inbet : (RelSeries.submoduleComap rs S.f).trimmed_length +
        (RelSeries.submoduleMap rs S.g).trimmed_length
        ≤ Module.length R S.X₁ + Module.length R S.X₃ := by exact add_le_add trimleft trimright


      apply le_trans (b := ↑((RelSeries.submoduleComap rs S.f).trimmed_length + (RelSeries.submoduleMap rs S.g).trimmed_length))

      apply Nat.mono_cast
      rw[Nat.add_comm] at trimmedProof
      exact trimmedProof
      exact inbet



    · rw[iSup_le_add]
      --#check ciSup_add_ciSup_le
      --apply (ciSup_add_ciSup_le )
      intro rstemp rstemp'
      obtain ⟨rs, hrs⟩ := RelSeries.chain_le_bot_top rstemp
      obtain ⟨rs', hrs'⟩ := RelSeries.chain_le_bot_top rstemp'


      let gInv : RelSeries (fun (a : Submodule R S.X₂) (b : Submodule R S.X₂) => a < b) :=
        RelSeries.submoduleComap_surjective hS.moduleCat_surjective_g rs'


      let fIm : RelSeries (fun (a : Submodule R S.X₂) (b : Submodule R S.X₂) => a < b) :=
        RelSeries.submoduleMap_injective hS.moduleCat_injective_f rs


      have connect : fIm.last = gInv.head := by
        have gInvheadker : gInv.head = LinearMap.ker S.g := by
          simp[gInv, RelSeries.submoduleComap_surjective, RelSeries.head]
          let obv : rs'.toFun 0 = ⊥ := by aesop
          rw[obv]
          exact rfl
        have fImLastRange : fIm.last = LinearMap.range S.f := by
          simp[fIm, RelSeries.submoduleMap_injective, RelSeries.last]
          let obv : (rs.toFun (Fin.last rs.length)) = ⊤ := by aesop
          rw[obv]
          exact Submodule.map_top S.f


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

end FL
