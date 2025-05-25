import Mathlib
open Order
open Ring
open LinearMap
open Multiplicative
open Pointwise
open Function


variable {R : Type*} [CommRing R] {M : Type*} [AddCommMonoid M] [Module R M]

lemma LinearMap.span_singleton_le_range_mul (a b : R) :
  Ideal.span {a} ≤
    LinearMap.ker ((Submodule.span (R := R) (M := R) {a*b}).mkQ ∘ₗ LinearMap.mul R R b) := by
  simp[mul_comm, Ideal.mem_span_singleton, Ideal.span_le, LinearMap.ker_comp, Submodule.ker_mkQ]

lemma LinearMap.range_mul (a : R) : range (mul R R a) = a • ⊤ := by
  simp[Ideal.ext_iff,Submodule.mem_smul_pointwise_iff_exists, mem_range]

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
    suffices ker (Submodule.mkQ (a • I) ∘ₗ (mul R R) a) ≤ Submodule.comap (mul R R a) (a • I) by
      rw[←m] at this
      exact this
    rw[ker_comp]
    simp

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
  simp[LinearMap.exact_iff]
  have : ker (quotOfMul a I) = a • ⊤ := by
    simp[quotOfMul, Submodule.factor, Submodule.mapQ.eq_1, Submodule.ker_liftQ]
    suffices Submodule.map (Submodule.mkQ (a • I)) (Submodule.span R {a}) = a • ⊤ by exact
      this
    rw[Submodule.map_span]
    simp[Submodule.span_quot]
  simp[this, mulQuot, Submodule.mapQ.eq_1, Submodule.range_liftQ, range_comp, range_mul]



  /-
  simp[LinearMap.mulQuot, LinearMap.quotOfMul]
  rw[Function.Exact]
  intro r
  constructor
  · intro hr
    simp at hr
    sorry-/
    /-obtain ⟨y, hy⟩ := hr
      have : ∃ y', y = b*y' := by
        have := hy.1
        rw [@Ideal.mem_span_singleton'] at this
        obtain ⟨y', hy'⟩ := this
        use y'
        rw[← hy']
        exact CommMonoid.mul_comm y' b
      obtain ⟨y', hy'⟩ := this
      use (Ideal.Quotient.mk (Ideal.span {a})) y'
      aesop-/
  /-· intro hr
    simp_all
    obtain ⟨y, hy⟩ := hr
    have : ∃ y' : R, y = Submodule.Quotient.mk y' := by
      have : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
      obtain ⟨y', hy'⟩ := this y
      use y'
      exact hy'.symm
    obtain ⟨y', hy'⟩ := this
    rw[hy'] at hy
    rw[Submodule.mapQ.eq_1] at hy
    rw[Submodule.liftQ_apply] at hy
    simp at hy
    simp[← hy]
    rw?-/


    /-
    use b*y'
    constructor
    · rw [@Ideal.mem_span_singleton]
      exact dvd_mul_right b y'
    · simp
      exact hy-/


  /-have : Submodule.mapQ (a • I) I LinearMap.id (by simp) =
         Submodule.factor (by simp) := rfl
  rw[← this]
  refine exact_iff.mpr ?_
  simp[Submodule.mapQ.eq_1, Submodule.ker_liftQ, Submodule.range_liftQ]
  ext b
  rw [@range_comp]
  have : range (mul R R a) = a • ⊤ := sorry
  rw[this]
  simp only [Submodule.mem_map, Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk,
    Submodule.map_pointwise_smul, Submodule.map_top, Submodule.range_mkQ]
  constructor
  · intro h
    obtain ⟨y, hy⟩ := h
    rw[← hy.2]

    --suffices a ∣ b by sorry
    sorry
  · intro h

    sorry-/

  --rw[← Submodule.mapQ_eq_factor]
  --#check Function.Exact.exact_mapQ_iff
  --refine exact_iff.mpr ?_

#check Submodule.ker_liftQ_eq_bot'
/-
def LinearMap.quotOfMul (a b : R) :
  (R ⧸ Submodule.span (R := R) (M := R) {a*b}) →ₗ[R] (R ⧸ Submodule.span (R := R) (M := R) {b}) :=
    have : Ideal.span {a * b} ≤ Ideal.span {b} := by
      rw [Ideal.span_singleton_le_span_singleton]
      exact dvd_mul_left b a
    let o := (Submodule.map (Submodule.span (R := R) (M := R) {a*b}).mkQ
      (Submodule.span (R := R) (M := R) {b})).mkQ
    let l := Submodule.quotientQuotientEquivQuotient
      (Submodule.span (R := R) (M := R) {a*b}) (Submodule.span (R := R) (M := R) {b}) (by aesop)
    l.toLinearMap ∘ₗ o

def LinearMap.mulQuotInjective' {b : R} (I : Ideal R) (hb : b ∈ nonZeroDivisors R) :
  Function.Injective (LinearMap.mulQuot b I) := by
  simp[LinearMap.mulQuot]
  rw [injective_iff_map_eq_zero]
  intro a ha
  #check Submodule.mapQ
  have : ∃ a', a = Submodule.Quotient.mk a' := sorry
  obtain ⟨r, hr⟩ := this
  rw[hr] at ha
  rw[Submodule.mapQ_apply] at ha
  simp at ha
  rw[hr]
  simp only [Ideal.Quotient.mk_eq_mk]




  --rw[← hr] at ha
  --have : Submodule.mapQ I (b • I) ((b : R ⧸ I) * a) = 0 := sorry
  sorry
  /-suffices LinearMap.ker (LinearMap.mulQuot a b) = ⊥ by exact LinearMap.ker_eq_bot.mp this
  simp[LinearMap.mulQuot]
  apply Submodule.ker_liftQ_eq_bot'
  apply le_antisymm
  · simp only [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_ker, coe_comp,
    Function.comp_apply, mul_apply_apply, Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk]
    suffices (Submodule.mkQ (Ideal.span {a * b})) (a * b) = 0 by
      exact (CommMonoid.mul_comm a b).symm ▸ this
    aesop
  · intro x hx
    simpa only [Ideal.mem_span_singleton, mem_ker, coe_comp, Function.comp_apply, mul_apply_apply,
      mul_comm b x, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      dvd_cancel_right_mem_nonZeroDivisors hb] using hx  -/

    --(by simp[mul_comm, Ideal.mem_span_singleton, Ideal.span_le])

def LinearMap.mulQuotInjective {b : R} (I : Ideal R) (hb : b ∈ nonZeroDivisors R) :
  Function.Injective (LinearMap.mulQuot b I) := by
  suffices LinearMap.ker (LinearMap.mulQuot a b) = ⊥ by exact LinearMap.ker_eq_bot.mp this
  simp[LinearMap.mulQuot]
  apply Submodule.ker_liftQ_eq_bot'
  apply le_antisymm
  · simp only [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_ker, coe_comp,
    Function.comp_apply, mul_apply_apply, Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk]
    suffices (Submodule.mkQ (Ideal.span {a * b})) (a * b) = 0 by
      exact (CommMonoid.mul_comm a b).symm ▸ this
    aesop
  · intro x hx
    simpa only [Ideal.mem_span_singleton, mem_ker, coe_comp, Function.comp_apply, mul_apply_apply,
      mul_comm b x, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      dvd_cancel_right_mem_nonZeroDivisors hb] using hx

lemma span_le_ker_mqQ_of_mul (a b : R) :
  Submodule.span R {a * b} ≤ LinearMap.ker (Submodule.span (R := R) (M := R) {b}).mkQ := by
    simp only [Ideal.submodule_span_eq, Submodule.ker_mkQ,
               Ideal.span_singleton_le_span_singleton, dvd_mul_left b a]



lemma LinearMap.range_mul_eq (a : R) : LinearMap.range (LinearMap.mul R R a) = Ideal.span {a} := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hx
    simp [← hy, Ideal.mem_span_singleton]
  · intro hx
    rw [Ideal.mem_span_singleton, dvd_def] at hx
    obtain ⟨y, hy⟩ := hx
    use y
    exact hy.symm


def LinearMap.quotOfMulSurjective {a b : R} :
    Function.Surjective (LinearMap.quotOfMul a b) := by
    simp[LinearMap.quotOfMul]
    exact
      Submodule.mkQ_surjective (Submodule.map (Submodule.mkQ (Ideal.span {a * b})) (Ideal.span {b}))

lemma LinearMap.quotMul_range_of_quotOfMul_ker {a b : R} {r : R ⧸ Submodule.span R {a * b}}
  (hr : (quotOfMul a b) r = 0) : r ∈ Set.range ⇑(mulQuot a b) := by
    simp_all[LinearMap.quotOfMul, LinearMap.mulQuot]
    obtain ⟨y, hy⟩ := hr
    have : ∃ y', y = b*y' := by
      have := hy.1
      rw [@Ideal.mem_span_singleton'] at this
      obtain ⟨y', hy'⟩ := this
      use y'
      rw[← hy']
      exact CommMonoid.mul_comm y' b
    obtain ⟨y', hy'⟩ := this
    use (Ideal.Quotient.mk (Ideal.span {a})) y'
    aesop

lemma LinearMap.quotOfMul_ker_of_quotMul_range {a b : R} {r : R ⧸ Submodule.span R {a * b}}
  (hr : r ∈ Set.range ⇑(mulQuot a b)) : (quotOfMul a b) r = 0 := by
  simp_all[LinearMap.quotOfMul, LinearMap.mulQuot]
  obtain ⟨y, hy⟩ := hr
  have : ∃ y' : R, y = Submodule.Quotient.mk y' := by
    have : Function.Surjective (Ideal.Quotient.mk (Ideal.span {a})) := Ideal.Quotient.mk_surjective
    obtain ⟨y', hy'⟩ := this y
    use y'
    exact hy'.symm
  obtain ⟨y', hy'⟩ := this
  rw[hy'] at hy
  rw[Submodule.liftQ_apply] at hy
  simp at hy
  use b*y'
  constructor
  · rw [@Ideal.mem_span_singleton]
    exact dvd_mul_right b y'
  · simp
    exact hy

def LinearMap.quotMulExact {a b : R} :
  Function.Exact (LinearMap.mulQuot a b) (LinearMap.quotOfMul a b) :=
  fun _ ↦ ⟨quotMul_range_of_quotOfMul_ker, quotOfMul_ker_of_quotMul_range⟩-/
#min_imports
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
  mul a b := a * b
  mul_assoc := mul_assoc
  one := 1
  one_mul := one_mul
  mul_one := MulOneClass.mul_one
  npow_zero _ := rfl
  npow_succ _ _ := rfl
  mul_comm := CommMonoid.mul_comm
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
