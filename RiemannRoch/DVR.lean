import Mathlib

variable {R : Type*} [CommRing R] [IsDomain R] --[IsDiscreteValuationRing R]

open Ring

theorem ord_irreducible [IsDiscreteValuationRing R] (ϖ : R) (hϖ : Irreducible ϖ) : ord R ϖ = 1 := by
  rw[Ring.ord, Module.length_eq_one_iff]
  have : (Ideal.span {ϖ}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hϖ
  constructor

  intro I
  rw[or_iff_not_imp_right]
  intro hI

  let J : Submodule R R := I.comap (Algebra.ofId R (R ⧸ Ideal.span {ϖ})).toLinearMap
  have hJ1 : J ≠ ⊤ := by
    contrapose! hI with hJ
    rw[eq_top_iff] at hJ ⊢
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    specialize hJ (trivial : x ∈ ⊤)
    simpa [J] using hJ

  have hJ2 : Ideal.span {ϖ} ≤ J := by
    intro x hx
    have : (Ideal.Quotient.mk (Ideal.span {ϖ})) x = 0 := by
      rwa [@Ideal.Quotient.eq_zero_iff_mem]
    simp only [J, Submodule.mem_comap, AlgHom.toLinearMap_apply]
    convert I.zero_mem

  have aux := this.eq_of_le (J := J) hJ1 hJ2
  rw[eq_bot_iff]
  intro x hx
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  suffices x ∈ J by
    rw [← aux] at this
    simpa only [Submodule.mem_bot, @Ideal.Quotient.eq_zero_iff_mem]
  simpa [J] using hx


/--
TODO: Generalize to arbitrary rings
-/
theorem ord_pow (x : R) (hx : x ≠ 0) (n : ℕ) : ord R (x ^ n) = n • ord R x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw[pow_succ, ord_mul, ih, succ_nsmul]
    exact mem_nonZeroDivisors_of_ne_zero hx

@[simp]
lemma ord_of_isUnit (x : R) (hx : IsUnit x) : ord R x = 0 := by
  obtain ⟨x, rfl⟩ := hx
  have : ord R ↑(x⁻¹) + ord R x = 0 := by
    rw[← ord_mul, Units.inv_mul, ord_one]
    simp
  exact eq_zero_of_add_left this


theorem ord_add [IsDiscreteValuationRing R] (x y : R) : min (Ring.ord R x) (Ring.ord R y) ≤
    Ring.ord R (x + y) := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  by_cases hx0 : x = 0
  · simp[hx0]
  by_cases hy0 : y = 0
  · simp[hy0]
  obtain ⟨m, α, hx⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  obtain ⟨n, β, hy⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  wlog hmn : m ≤ n
  · rw[min_comm, add_comm]
    apply this y x ϖ hϖ hy0 hx0 n β hy m α hx
    omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have : x + y = (α + β*ϖ^k) * ϖ^m := by
    rw[hx, hy]
    ring
  rw[this, hx, hy, ord_mul, ord_mul, ord_mul, ord_pow, ord_pow,
     ord_of_isUnit (α : R), ord_of_isUnit (β : R), ord_irreducible _ hϖ]
  · simp
  all_goals simp[hϖ.ne_zero]


theorem ordMonoidWithZeroHom_eq_ord (x : R) (h : x ∈ nonZeroDivisors R) :
  ordMonoidWithZeroHom R x =
  WithZero.map' (Nat.castAddMonoidHom ℤ).toMultiplicative (Ring.ord R x) := dif_pos h

omit [IsDomain R] in
lemma ord_neg (x : R) : Ring.ord R x = Ring.ord R (-x) := by
  simp[Ring.ord]
  congr 2
  all_goals exact Eq.symm (Ideal.span_singleton_neg x)

omit [IsDomain R] in
lemma ord_smul (a : R) (h : IsUnit a) (x : R) : Ring.ord R x = Ring.ord R (a * x) := by
  simp[Ring.ord]
  congr 2
  all_goals exact Eq.symm (Ideal.span_singleton_mul_left_unit h x)

omit [IsDomain R] in
lemma ord_le_smul {S : Type*} [CommRing S] [Algebra S R] (a : S) (x : R) :
    Ring.ord R x ≤ Ring.ord R (a • x) := by
  simp[Ring.ord]
  suffices Ideal.span {a • x} ≤ Ideal.span {x} by
    let g : (R ⧸ Ideal.span {a • x}) →ₗ[R] (R ⧸ Ideal.span {x}) := Submodule.factor this
    refine Module.length_le_of_surjective (Submodule.factor this) (Submodule.factor_surjective this)
  rw [@Ideal.span_singleton_le_span_singleton]
  rw [@Algebra.smul_def']
  exact Dvd.intro_left (Algebra.algebraMap a) rfl


lemma ord_ne_top (x : R) (hx : x ≠ 0) : Ring.ord R x ≠ ⊤ := by
  simp[Ring.ord]
  /-
  0 -> <x> -> R -> R ⧸ <x> -> 0
  -/

  sorry


/-
I'm not sure if this is true to be honest. I think the other version is strong enough
but it's not quite what we need.

The proof should be that ordFrac (a • (f1/f2)) = ord (a1 • f1) - ord (a2 • f2)
-/
lemma ordFrac_le_smul [IsNoetherianRing R] [KrullDimLE 1 R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K]
    {S : Type*} [CommRing S] [Algebra S K]
    (a : S) (ha : a ≠ 0) (f : K) : Ring.ordFrac R f ≤ Ring.ordFrac R (a • f) := by sorry


/-#check IsScalarTower
set_option maxHeartbeats 0
lemma ordFrac_le_smul [IsNoetherianRing R] [KrullDimLE 1 R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K]
    {S : Type*} [CommRing S] [Algebra S R] [Algebra S K] [IsScalarTower S R K]
    (a : S) (ha : a ≠ 0) (f : K) :
    Ring.ordFrac R f ≤ Ring.ordFrac R (a • f) := by
  by_cases j : f = 0
  · simp[j]
  suffices (ordFrac R) f ≤ (ordFrac R) ((algebraMap S R) a • f) by simp_all only [ne_eq,
    algebraMap_smul]
  rw [← IsLocalization.mk'_sec (M := nonZeroDivisors R) K f]

  rw [IsLocalization.smul_mk']
  have auxf : (IsLocalization.sec (nonZeroDivisors R) f).1 ≠ 0 := sorry
  have auxf2 : (IsLocalization.sec (nonZeroDivisors R) f).2.1 ≠ 0 := sorry
  have auxf3 : (algebraMap S R) a * (IsLocalization.sec (nonZeroDivisors R) f).1 ≠ 0 := sorry
  simp only [IsFractionRing.mk'_eq_div, map_div₀, ordFrac_eq_ord R _ auxf, ordFrac_eq_ord R _ auxf2,
    ordFrac_eq_ord R _ auxf3]
  have : (ordMonoidWithZeroHom R) ↑(IsLocalization.sec (nonZeroDivisors R) f).2 > 0 := by sorry
  apply (div_le_div_iff_of_pos_right this).mpr
  rw[ordMonoidWithZeroHom_eq_ord ((algebraMap S R) a * (IsLocalization.sec (nonZeroDivisors R) f).1) (by simp[auxf3])]
  rw[ordMonoidWithZeroHom_eq_ord ((IsLocalization.sec (nonZeroDivisors R) f).1) (by simp[auxf])]
  apply WithZero.map'_mono
  · intro x y h
    simp_all
  · by_cases o : ord R (IsLocalization.sec (nonZeroDivisors R) f).1 = (0 : WithZero (Multiplicative ℕ))
    · aesop
    have := ord_le_smul a (IsLocalization.sec (nonZeroDivisors R) f).1
    have : ord R (IsLocalization.sec (nonZeroDivisors R) f).1 ≤
           ord R ((algebraMap S R) a * (IsLocalization.sec (nonZeroDivisors R) f).1) := by
      convert this
      rw [@funext_iff]
      intro x
      exact Eq.symm (Algebra.smul_def a x)
    have : ord R ((algebraMap S R) a * (IsLocalization.sec (nonZeroDivisors R) f).1) ≠
           (0 : WithZero (Multiplicative ℕ)) := by

      rw[ord_mul R (mem_nonZeroDivisors_of_ne_zero auxf)]


      suffices ord R ((algebraMap S R) a) ≠ (0 : WithZero (Multiplicative ℕ)) ∧
               ord R (IsLocalization.sec (nonZeroDivisors R) f).1 ≠
               (0 : WithZero (Multiplicative ℕ)) by sorry
      refine ⟨?_, o⟩



      sorry
    rw[WithZero.ne_zero_iff_exists] at this
    obtain ⟨l, hl⟩ := this
    rw[← hl]
    have : ord R (IsLocalization.sec (nonZeroDivisors R) f).1 ≠ (0 : WithZero (Multiplicative ℕ)) := o
    rw[WithZero.ne_zero_iff_exists] at this
    obtain ⟨p, hp⟩ := this
    rw[← hp]

    rw[← hp, ← hl] at this
    rw[WithZero.coe_le_coe]
    have : p ≤ (l : ℕ∞) := this
    rw[ENat.coe_le_coe] at this
    exact this-/



/-
This should be the correct thing to prove
-/
lemma ordFrac_smul [IsNoetherianRing R] [KrullDimLE 1 R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] (a : R) (ha : IsUnit a) (f : K) : Ring.ordFrac R (a • f) = Ring.ordFrac R f := by
  by_cases j : f = 0
  · simp[j]
  rw[← IsLocalization.mk'_sec (M := nonZeroDivisors R) K f]
  rw[IsLocalization.smul_mk']
  have auxf : (IsLocalization.sec (nonZeroDivisors R) f).1 ≠ 0 := sorry
  have auxf2 : (IsLocalization.sec (nonZeroDivisors R) f).2.1 ≠ 0 := sorry
  have auxf3 : a * (IsLocalization.sec (nonZeroDivisors R) f).1 ≠ 0 := sorry
  simp only [IsFractionRing.mk'_eq_div, map_div₀, ordFrac_eq_ord R _ auxf, ordFrac_eq_ord R _ auxf2,
    ordFrac_eq_ord R _ auxf3]
  refine (div_left_inj' ?_).mpr ?_
  · -- This should be easy, we just need to write some more API to make it automatic
    sorry
  · rw[ordMonoidWithZeroHom_eq_ord (a * (IsLocalization.sec (nonZeroDivisors R) f).1) (by simp[auxf3])]
    rw[ordMonoidWithZeroHom_eq_ord ((IsLocalization.sec (nonZeroDivisors R) f).1) (by simp[auxf])]
    congr 1
    rw[ord_mul]
    · simp[ha]
    · exact mem_nonZeroDivisors_of_ne_zero auxf







/-
We need a better way to lift things from Ring.ord to Ring.ordFrac, something like saying if
we have some property P(f) such that P(Ring.ord, x) holds for all x and
P(Ring.ord, ??) holds then P(Ring.ordFrac, x) holds for all x.

Unclear how this should work.

In any case, this should be extended to smul_neg
-/
lemma ordFrac_neg [IsNoetherianRing R] [KrullDimLE 1 R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] (x : K) : Ring.ordFrac R x = Ring.ordFrac R (-x) := by
  by_cases j : x = 0
  · simp[j]
  rw[← IsLocalization.mk'_sec (M := nonZeroDivisors R) K x]
  have auxx : (IsLocalization.sec (nonZeroDivisors R) x).1 ≠ 0 := by
    exact IsLocalization.sec_fst_ne_zero j
  have auxx' : (IsLocalization.sec (nonZeroDivisors R) x).1 ∈ nonZeroDivisors R := by aesop
  have auxnx : (IsLocalization.sec (nonZeroDivisors R) x).1 ≠ 0 := by
    sorry
  have auxnx' : -(IsLocalization.sec (nonZeroDivisors R) x).1 ∈ nonZeroDivisors R := by aesop

  simp[ordFrac_eq_ord R _ auxx, ordMonoidWithZeroHom_eq_ord _ auxx',
       ordFrac_eq_ord R _ auxnx, ordMonoidWithZeroHom_eq_ord _ auxnx']


  /-
  It can't even work out how to deal with -x...
  -/
  sorry

theorem ordFrac_add [IsNoetherianRing R] [KrullDimLE 1 R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] (x y : K) :
    min (Ring.ordFrac R x) (Ring.ordFrac R y) ≤ Ring.ordFrac R (x + y) := by

  rw[← IsLocalization.mk'_sec (M := nonZeroDivisors R) K x,
     ← IsLocalization.mk'_sec (M := nonZeroDivisors R) K y]

  #check div_add_div
  have auxx : (IsLocalization.sec (nonZeroDivisors R) x).1 ≠ 0 := sorry
  have auxx' : (IsLocalization.sec (nonZeroDivisors R) x).1 ∈ nonZeroDivisors R := sorry
  have auxy : (IsLocalization.sec (nonZeroDivisors R) y).1 ≠ 0 := sorry
  have auxy' : (IsLocalization.sec (nonZeroDivisors R) y).1 ∈ nonZeroDivisors R := sorry
  simp[ordFrac_eq_ord, ordFrac_eq_ord R _ auxx, ordFrac_eq_ord R _ auxy, ordMonoidWithZeroHom_eq_ord,
  ordMonoidWithZeroHom_eq_ord (IsLocalization.sec (nonZeroDivisors R) x).1 auxx',
  ordMonoidWithZeroHom_eq_ord (IsLocalization.sec (nonZeroDivisors R) y).1 auxy', div_add_div]
  /-
  We now need some analogous auxx' and auxy' for these sums appearing everywhere.
  -/

  sorry




--lemma test (x y : ) (k : ℕ) : ∑ x ∈ Ico 0 k, k.cho
