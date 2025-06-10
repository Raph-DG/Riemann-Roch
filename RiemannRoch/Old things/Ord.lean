import Mathlib
open Order
open Ring
open LinearMap
open Multiplicative
open Pointwise
open Function


variable {R : Type*} [CommRing R] {M : Type*} [AddCommMonoid M] [Module R M]

lemma LinearMap.span_singleton_le_ker_mul (a b : R) :
  Ideal.span {a} ≤
    LinearMap.ker ((Ideal.span {a*b}).mkQ ∘ₗ LinearMap.mul R R b) := by
  simp [mul_comm, Ideal.mem_span_singleton, Ideal.span_le]

lemma LinearMap.range_mul (A : Type u_2) [CommSemiring R] [CommSemiring A] [Module R A] 
  [SMulCommClass R A A] [IsScalarTower R A A] (a : A) : range (mul R A a) = (Ideal.span {a}).restrictScalars R := by
  aesop (add simp Ideal.mem_span_singleton) (add simp dvd_def)

@[simp]
lemma LinearMap.range_mul' (a : R) : range (mul R R a) = Ideal.span {a} := range_mul ..
  --simp[Ideal.ext_iff,Submodule.mem_smul_pointwise_iff_exists, mem_range]
  

lemma Submodule.span_quot (a : R) (I : Ideal R) : (a • ⊤ : Submodule R (R ⧸ a • I)) =
   Submodule.span R {Submodule.Quotient.mk a} := by
    ext k
    simp[Submodule.mem_smul_pointwise_iff_exists, mem_span_singleton]
    constructor
    · intro h
      obtain ⟨b, hb⟩ := h
      rw[← hb]
      have : ∃ b' : R, Submodule.Quotient.mk b' = b := Quotient.exists_rep b
      obtain ⟨b', hb'⟩ := this
      use b'
      rw[← hb']
      suffices b' • (Submodule.Quotient.mk (p := a • I) a) = a • Submodule.Quotient.mk b' by exact
        this
      rw[← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
      congr 1
      simp only [smul_eq_mul, mul_comm]
    · intro h
      obtain ⟨b, hb⟩ := h
      use (Ideal.Quotient.mk (a • I) b)
      rw[← hb]
      suffices a • (Submodule.Quotient.mk (p := (a • I))) b =
        b • (Submodule.Quotient.mk (p := (a • I))) a by exact this
      rw[← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
      congr 1
      simp only [smul_eq_mul, mul_comm]


lemma Ideal.le_comap_mul_singleton (b : R) (I : Ideal R) : I ≤ Submodule.comap ((mul R R) b) (b • I) := by
  have : b • I = Submodule.map ((LinearMap.mul R R) b) I := rfl
  simp[this, Submodule.comap_map_eq]


def LinearMap.mulQuot (a : R) (I : Ideal R) :
    R ⧸ I →ₗ[R] R ⧸ (a • I) := Submodule.mapQ _ _ (LinearMap.mul R R a) <| Ideal.le_comap_mul_singleton a I

def LinearMap.mulQuotInjective {a : R} (I : Ideal R) (ha : a ∈ nonZeroDivisors R) :
  Function.Injective (LinearMap.mulQuot a I) := by
  simp[← LinearMap.ker_eq_bot, LinearMap.mulQuot, Submodule.mapQ.eq_1]
  apply Submodule.ker_liftQ_eq_bot'
  apply le_antisymm
  · rw [@le_ker_iff_map]
    have : Submodule.map (mul R R a) I = a • I := rfl
    rw[Submodule.map_comp]
    rw[this]
    exact Submodule.mkQ_map_self (a • I)
  · have m : I = Submodule.comap (mul R R a) (a • I) := by
      ext b
      exact Iff.symm (Submodule.mul_mem_smul_iff ha)
    simp[←m, ker_comp]
lemma LinearMap.smul_le_span (s : Set R) (I : Ideal R) : s • I ≤ Ideal.span s :=
  by simp[← Submodule.set_smul_top_eq_span, Submodule.singleton_set_smul, smul_le_smul_left]

def LinearMap.quotOfMul (a : R) (I : Ideal R) :
  (R ⧸ a • I) →ₗ[R] (R ⧸ Ideal.span {a}) :=
  Submodule.factor <| Submodule.singleton_set_smul I a ▸ LinearMap.smul_le_span {a} I

def LinearMap.quotOfMulSurjective {a : R} (I : Ideal R) :
    Function.Surjective (LinearMap.quotOfMul a I) := by
    simp[LinearMap.quotOfMul]
    exact Submodule.factor_surjective <|
      Submodule.singleton_set_smul I a ▸ LinearMap.smul_le_span {a} I

def LinearMap.quotMulExact {a : R} (I : Ideal R) :
  Function.Exact (LinearMap.mulQuot a I) (LinearMap.quotOfMul a I) := by
  simp [LinearMap.exact_iff]
  have : ker (quotOfMul a I) = a • ⊤ := by
    simp [quotOfMul, Submodule.factor, Submodule.mapQ.eq_1, Submodule.ker_liftQ]
    suffices Submodule.map (Submodule.mkQ (a • I)) (Submodule.span R {a}) = a • ⊤ by exact
      this
    rw [Submodule.map_span]
    simp [Submodule.span_quot]
  simp [this, mulQuot, Submodule.mapQ.eq_1, Submodule.range_liftQ, range_comp, range_mul]

variable (R)
/--
ENat valued order of vanishing function. Note
-/
noncomputable
abbrev CommRing.ord (x : R) := Module.length R (R ⧸ Submodule.span (R := R) (M := R) {x})

lemma CommRing.ord_one : CommRing.ord R 1 = 0 := by
  simp[CommRing.ord]
  rw[Module.length_eq_zero_iff]
  simp_all only [Ideal.span_singleton_one]
  exact (Submodule.Quotient.subsingleton_iff ⊤).mpr fun x ↦ trivial

theorem CommRing.ord_mul {a b : R}
  (hb : b ∈ nonZeroDivisors R) :
  CommRing.ord R (a*b) = CommRing.ord R a + CommRing.ord R b :=
  Module.length_eq_add_of_exact (LinearMap.mulQuot b (Ideal.span {a})) (LinearMap.quotOfMul a b)
    (LinearMap.mulQuotInjective (Ideal.span {a}) hb) LinearMap.quotOfMulSurjective LinearMap.quotMulExact

instance : CommMonoidWithZero (Multiplicative ℕ∞) where
  zero := ⊤
  zero_mul _ := rfl
  mul_zero a := add_top (toAdd a)

/-
If R is finite length, then ord R 0 will be some non top value. However, having this around
would break our morphism since 0 needs to be sent to 0 for things to be nontrivial, hence the
case distinction here
-/
open Classical in
@[stacks 02MD]
noncomputable
def CommRing.ordMap [Nontrivial R] : R →*₀ Multiplicative ℕ∞ where
  toFun x := if x ∈ nonZeroDivisors R then CommRing.ord R x else 0
  map_zero' := by
    simp[nonZeroDivisors, exists_ne]
  map_one' := by
    simp[nonZeroDivisors, CommRing.ord_one]
    rfl
  map_mul' := by
    intro x y
    split_ifs
    all_goals simp_all [mul_mem_nonZeroDivisors]
    rename_i a b
    apply CommRing.ord_mul R b



def ENat.multiplicativeToMulWithZero : Multiplicative ℕ∞ →*₀ ℕₘ₀ where
  toFun n := n
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl


noncomputable
def WithZero.castNatMulZeroMonoidWithZeroHom : ℕₘ₀ →*₀ ℤₘ₀ := WithZero.map' <|
  (AddMonoidHom.toMultiplicative).toFun (Nat.castAddMonoidHom ℤ)


noncomputable
def bibo : Multiplicative ℕ∞ →*₀ ℤₘ₀ := MonoidWithZeroHom.comp
  WithZero.castNatMulZeroMonoidWithZeroHom ENat.multiplicativeToMulWithZero


/--
Order of vanishing function
-/
@[stacks 02MD]
noncomputable
def ordFrac [Nontrivial R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : ∀ y : nonZeroDivisors R, ENat.multiplicativeToMulWithZero (CommRing.ord R y.1) ≠ 0) :
    K →*₀ ℤₘ₀ :=
  letI f := Submonoid.LocalizationWithZeroMap.lift (toLocalizationWithZeroMap (nonZeroDivisors R) K)
    (MonoidWithZeroHom.comp bibo (CommRing.ordMap R))
  haveI : (∀ (y : ↥(nonZeroDivisors R)), IsUnit ((bibo.comp (CommRing.ordMap R)) ↑y)) := by
    intro y
    simp[bibo, ENat.multiplicativeToMulWithZero, WithZero.castNatMulZeroMonoidWithZeroHom]
    intro a
    have : ∃ a : Multiplicative ℕ, WithZero.coe a = ((CommRing.ordMap R) y.1) := by
      specialize hR y
      refine WithZero.ne_zero_iff_exists.mp ?_
      simp[CommRing.ordMap]
      exact hR
    obtain ⟨m, hm⟩ := this
    rw[← hm] at a
    simp at a

  f this



lemma dkkm {a : WithBot ℕ∞} {b c : ℕ} (h : a + b ≤ c) : a ≤ c - b := by
  have : a ≠ ⊤ := by
    intro a
    subst a
    exact not_le_of_lt (compareOfLessAndEq_eq_lt.mp rfl) h

  by_cases o : a = ⊥
  · aesop
  · obtain ⟨a', ha'⟩ := WithBot.ne_bot_iff_exists.mp o
    rw[← ha'] at this
    have : a' ≠ ⊤ := by exact fun a ↦ this (congrArg WithBot.some a)
    have : WithTop.untop a' this ≤ c - b := by
      rw[WithTop.untop_le_iff]

      sorry
    rw[WithTop.untop_le_iff] at this
    rw [← ha']
    exact (WithBot.coe_le rfl).mpr this


/--
The order of vanishing is finite for all elements x of
Noetherian local domains of Krull dimension less than or equal to 1.

Note this doesn't really need to be in the same namespace strictly speaking.
-/
theorem CommRing.ord_finite [IsNoetherianRing R]
         [IsLocalRing R] [IsDomain R] [IsLocalRing R]
         (hR : ringKrullDim R ≤ 1) {x : R} (hx : x ∈ nonZeroDivisors R) :
         IsFiniteLength R (R ⧸ Ideal.span {x}) := by
  rw[isFiniteLength_iff_isNoetherian_isArtinian]
  constructor
  · exact isNoetherian_quotient (Ideal.span {x})
  · by_cases o : IsArtinianRing R
    · exact isArtinian_of_quotient_of_artinian (Ideal.span {x})
    · have := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hx
      have : ringKrullDim (R ⧸ Ideal.span {x}) ≤ 0 := by
        have : ringKrullDim (R ⧸ Ideal.span {x}) + 1 ≤ 1 :=
          Preorder.le_trans (ringKrullDim (R ⧸ Ideal.span {x}) + 1) (ringKrullDim R) 1 this hR
        exact dkkm this
        /-by_cases o : ringKrullDim (R ⧸ Ideal.span {x}) = ⊤
        · simp_all
          have rwlem : (⊤ : WithBot (ℕ∞)) + 1 = ⊤ := rfl
          simp[rwlem] at this
          have thing : 1 ≠ (⊤ : WithBot ℕ∞) := by exact ne_of_beq_false rfl
          exact False.elim (thing this)
        · by_cases o' : ringKrullDim (R ⧸ Ideal.span {x}) = ⊥
          · rw[o']
            exact OrderBot.bot_le 0
          · obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp o'
            have c : d ≠ ⊤ := by
              rw[← hd] at o
              exact fun a ↦ o (congrArg WithBot.some a)
            obtain ⟨d', hd'⟩ := WithTop.ne_top_iff_exists.mp c
            suffices d ≤ 0 by
              rw[← hd]
              exact WithBot.coe_le_zero.mpr this
            suffices d' ≤ 0 by
              rw[← hd']
              aesop
            have : d + 1 ≤ 1 := by
              rw[←hd] at this
              exact WithBot.coe_le_one.mp this
            have : d' + 1 ≤ 1 := by
              rw[← hd'] at this
              exact ENat.coe_le_coe.mp this
            omega-/
      have : Ring.KrullDimLE 0 (R ⧸ Ideal.span {x}) :=
        (krullDimLE_iff 0 (PrimeSpectrum (R ⧸ Ideal.span {x}))).mpr this

      have : IsArtinian (R ⧸ Ideal.span {x}) ((R ⧸ Ideal.span {x})) :=
        IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

      apply (OrderEmbedding.wellFoundedLT (β := Submodule (R ⧸ Ideal.span {x})
        (R ⧸ Ideal.span {x})) _)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro N
        refine {toAddSubmonoid := N.toAddSubmonoid, smul_mem' := ?_}
        intro c x hx
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        show r • x ∈ N
        apply N.smul_mem _ hx
      · intro N1 N2 h
        rwa[Submodule.ext_iff] at h ⊢
      · intro N1 N2
        rfl
