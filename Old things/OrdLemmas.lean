import Mathlib

variable {R : Type*} [CommRing R] [Nontrivial R]

open Ring

/--
If `x` is a non zero divisor, `ordMonoidWithZeroHom` is equal to the canonical embedding
of `Ring.ord R x` into `WithZero (Multiplicative ℤ)`.
-/
@[simp]
theorem ordMonoidWithZeroHom_eq_ord (x : R) (h : x ∈ nonZeroDivisors R) :
    ordMonoidWithZeroHom R x =
  WithZero.map' (Nat.castAddMonoidHom ℤ).toMultiplicative (Ring.ord R x) := dif_pos h

/--
If `x` is not a non zero divisor, `ordMonoidWithZeroHom` is equal to `0`.
-/
@[simp]
theorem ordMonoidWithZeroHom_eq_zero (x : R) (h : x ∉ nonZeroDivisors R) :
    ordMonoidWithZeroHom R x = 0 := dif_neg h

/--
The canonical monoid with zero hom from `WithZero (Multiplicative ℕ)` to
`WithZero (Multiplicative ℤ)` is strictly monotone
-/
lemma Nat.cast_withZero_mul_int_strictMono : StrictMono <|
    (WithZero.map' (AddMonoidHom.toMultiplicative (Nat.castAddMonoidHom ℤ))) := by
  intro a b h
  apply WithZero.map'_strictMono ?_ h
  intro x y hy
  simp_all

/--
The canonical monoid with zero hom from `WithZero (Multiplicative ℕ)` to
`WithZero (Multiplicative ℤ)` is monotone
-/
lemma Nat.cast_withZero_mul_int_mono : Monotone <|
    (WithZero.map' (AddMonoidHom.toMultiplicative (Nat.castAddMonoidHom ℤ))) :=
  Nat.cast_withZero_mul_int_strictMono.monotone

/--
The canonical monoid with zero hom from `WithZero (Multiplicative ℕ)` to
`WithZero (Multiplicative ℤ)` is injective
-/
lemma Nat.cast_withZero_mul_int_injective : Function.Injective <|
    (WithZero.map' (AddMonoidHom.toMultiplicative (Nat.castAddMonoidHom ℤ))) := by
  apply WithZero.map'_injective
  exact Isometry.injective fun x1 ↦ congrFun rfl


variable {R : Type*} [CommRing R]
variable [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/--
In a Noetherian ring of krull dimension less than or equal to `1`, the order of vanishing
of a non zero divisor `a` is not `⊤`.
-/
lemma ord_ne_top (a : R) (ha : a ∈ nonZeroDivisors R) : ord R a ≠ ⊤ := by
  simp [isFiniteLength_quotient_span_singleton R ha, Ring.ord, Module.length_ne_top_iff]

/--
Analogue of `ord_ne_top` for `ordMonoidWithZeroHom`.
-/
lemma ordMonoidWithZeroHom_ne_zero [Nontrivial R] (a : R) (ha : a ∈ nonZeroDivisors R) :
    ordMonoidWithZeroHom R a ≠ 0 := by
  have := ord_ne_top a ha
  rw [WithTop.ne_top_iff_exists] at this
  obtain ⟨a', ha'⟩ := this
  simp [ha]
  rw [← ha']
  exact not_eq_of_beq_eq_false rfl

variable [Nontrivial R]
/--
Helper lemma to pass between the orders on `ℕ∞` and `ℤᵐ⁰` (which notably have different behaviour at
∞). Note that here we're using the fact that the order of any non zero divisor is finite, hence
the assumptions on the ring.
-/
lemma ord_le_iff (a b : R) (ha : a ∈ nonZeroDivisors R) (hb : b ∈ nonZeroDivisors R) :
    ord R a ≤ ord R b ↔ ordMonoidWithZeroHom R a ≤ ordMonoidWithZeroHom R b := by
  rw [ordMonoidWithZeroHom_eq_ord a ha, ordMonoidWithZeroHom_eq_ord b hb]
  obtain ⟨a', ha'⟩ := WithTop.ne_top_iff_exists.mp <| ord_ne_top a ha
  obtain ⟨b', hb'⟩ := WithTop.ne_top_iff_exists.mp <| ord_ne_top b hb
  rw [← ha', ← hb']
  constructor
  · exact fun h ↦ Nat.cast_withZero_mul_int_mono (WithZero.coe_le_coe.mpr (ENat.coe_le_coe.mp h))
  · intro h
    have := (StrictMono.le_iff_le Nat.cast_withZero_mul_int_strictMono
            (a := WithZero.coe (a' : Multiplicative ℕ))
            (b := WithZero.coe (b' : Multiplicative ℕ))).mp h
    rw [WithTop.coe_le_coe]
    rwa [WithZero.coe_le_coe] at this

#min_imports
