import Mathlib
import Plausible

/-!
# Wilson's Theorem

In this file we're going to prove Wilson's theorem, a fun lemma from number theory about
factorials and modular arithmetic.
-/

open Nat ZMod FiniteField Finset

/-
A common theme in elementary number theory is to ask how various familiar operations on the
natural numbers or integers behave when mixed with modular arithmetic. One natural question of this
kind is to ask how the factorial behaves `mod n`.

The most obvious question of this kind is to ask what `n! mod n` is. Of course, one quickly
realises that this is a rather easy problem, since `n!` is clearly divisible by `n`, and so is
`0 mod n`. However, we can ask the same question but not incluse `n` in the product,
instead taking `(n-1)!`, and the question becomes somewhat more interesting.

Below are some computations showing the first few values of `(n-1)! mod n`,
(these are displayed in the format `(n, (n-1)! mod n)`. You can view all of these at once by
expanding the "All Messages" tab in your infoview.
-/

#eval (2, ((2-1)! : ZMod 2))
#eval (3, ((3-1)! : ZMod 3))
#eval (4, ((4-1)! : ZMod 4))
#eval (5, ((5-1)! : ZMod 5))
#eval (6, ((6-1)! : ZMod 6))
#eval (7, ((7-1)! : ZMod 7))
#eval (8, ((8-1)! : ZMod 8))
#eval (9, ((9-1)! : ZMod 9))
#eval (10, ((10-1)! : ZMod 10))
#eval (11, ((11-1)! : ZMod 11))
#eval (12, ((12-1)! : ZMod 12))
#eval (13, ((13-1)! : ZMod 13))

/-
Above we have evaluated `(n-1)!` for the first `13` natural numbers. It seems to have different
behaviour on primes and composite numbers! Let's start with the prime case and take `p` to be a
prime number.Below is a statement saying that `(p - 1)! = sorry`. Fill in this sorry value with
a conjectured value for `(p - 1)!` based on the above empirical evidence.

The `by plausible` will then check if your conjecture is plausible by generating many more examples
just like above and checking if they give the expected result based on your conjecture.
-/

variable {p : ℕ} [Fact p.Prime]

lemma wilson_test : ((p - 1)! : ZMod p) = sorry := by plausible








/-
Below this line are spoilers for the exercise above. Give it a go before scrolling down!
-/


---------------------------------------------------------------------------------------------------





/-
As you've (hopefully) discovered, it seems like the correct value for the sorry above is `-1` (or
possibly `p-1`, which is the same thing mod `p`).

Indeed, this is a theorem: in its simplest form, Wilsons's theorem says that
for any prime `p`, `(p-1)! ≡ -1 (mod p)`. We will use the following proof sketch as a guide:

Proof sketch:

First, note the definition of the factorial, `(p-1)! = 1*2*3*...*(p-3)*(p-2)*(p-1)`. These numbers
`1` through `p-1` are precisely the numbers with *multiplicative inverses* in `Zmod p`, which we
call *units*. SO, this factorial is just the product over all *units* of `Zmod p`. We denote the
group of all units of `Zmod p` by `(Zmod p)ˣ`.

This product can be broken down further into the product of those elements `a : (Zmod p)ˣ` with
`a = a⁻¹` times the product of those elements `b : (Zmod p)ˣ` with  `b ≠ b⁻¹`.

Since `a⁻¹` is just an element of `(Zmod p)ˣ`, if it is not equal to `a` then the expression `a*a⁻¹`
will appear in the first of these products. Indeed, this product is composed entirely of such pairs
and such pairs are clearly equal to `1`, hence the whole product is `1`.

For the second product, the condition `a = a⁻¹` implies `a² = 1` mod p,
meaning `a²-1 = (a-1)(a+1) = 0`, which means either `a` is `1` or `-1`.
Hence, this is just the product `-1 * 1 = -1`.
-/
#check Field

/--
In step 1, we just expand the definition of the factorial into its product definition.

This `Ico` constructor will most likely be unfamiliar to you. Hover over this and convince yourself
that this statement is saying what we expect.

Hint: loogle is your friend here! We've chosen to represent this statement with this funny Ico
thing for a reason...
-/
lemma factorial_is_prod : ((p - 1)! : ZMod p) = ∏ x ∈ Ico 1 (succ (p - 1)), (x : ZMod p) := by
  simp[← Finset.prod_Ico_id_eq_factorial]
  sorry

/--
In step 2, we say that our product is the same as taking the product over all those elements of
(ZMod p) with an inverse with respect to multiplication.
-/
lemma prod_to_units : ∏ x ∈ Ico 1 (succ (p - 1)), (x : ZMod p) = ∏ x : (ZMod p)ˣ, (x : ZMod p) :=

  sorry

/--
In this step, we split the our product into the product of those elements which are their own
inverse and those elements which are not.
-/
lemma prod_split : ∏ x : (ZMod p)ˣ, (x : ZMod p) =
    (∏ x : (ZMod p)ˣ with x = x⁻¹, (x : ZMod p)) *
    (∏ x : (ZMod p)ˣ with x ≠ x⁻¹, (x : ZMod p)) := by
  exact Eq.symm (prod_filter_mul_prod_filter_not univ (fun x ↦ x = x⁻¹) Units.val)

/--
Here we show that the product of all the elements with inverses not equal to themselves is `1`.
The idea here is that this product can be expressed as `a*a⁻¹*b*b⁻¹*...`, which must be `1` since
`a*a⁻¹ = 1`.
-/
lemma prod_pairs : (∏ x : (ZMod p)ˣ with x ≠ x⁻¹, x : ZMod p) = 1 := by
  /-
  The following is a loose sketch of how one might prove this statement. Note that our strategy
  might seem somewhat strange; we start the proof by stating that it suffices to show a stronger
  statement. The reason we do this is so that we can argue by induction, and this strengthening
  of statements to facilitate proofs via induction is fairly commonplace in formalization.
  -/
  suffices ∀ n, (∏ x : {y : (ZMod p)ˣ | y.val.val ≤ n ∧ y ≠ y⁻¹}, (x.1 : ZMod p)) = 1 by sorry
  intro n
  induction n with
  | zero =>

    sorry
  | succ n ih =>

    sorry


/--
Here we show that the product of all elements with inverses equal to themselves is `-1`.
The idea here is that if `a² = 1`, then `a² - 1 = 0`, and so `(a - 1)(a + 1) = 0`.
This means that either `a` is `1` or `a` is `-1`. Hence, our product is just `-1 * 1 = -1`.
-/
lemma prod_self_inverse : ∏ x : (ZMod p)ˣ with x = x⁻¹, (x : ZMod p) = -1 := by
  have : {y : (ZMod p)ˣ | y = y⁻¹} = {1, -1} := sorry
  suffices ∏ x ∈ ({1, -1} : Set (ZMod p)ˣ), (x : ZMod p) = -1 by sorry
  aesop


/--
Here we're just putting the previous pieces together to show that the product we're working with
is indeed -1. There are no new ideas in this proof.
-/
lemma prod_minus_one : ∏ x : (ZMod p)ˣ, (x : ZMod p) = -1 :=
  calc
    ∏ x : (ZMod p)ˣ, (x : ZMod p) = (∏ x : (ZMod p)ˣ with x = x⁻¹, x : ZMod p) *
                                    (∏ x : (ZMod p)ˣ with x ≠ x⁻¹, x : ZMod p) := prod_split
    _ = -1 := by simp [prod_pairs, prod_self_inverse]

/--
# Wilson's theorem

At long last we have our theorem, which only has this tiny little proof because we've already done
all the work in our lemmas.
-/
theorem wilson : ((p - 1)! : ZMod p) = -1 := by
  calc
    ((p - 1)! : ZMod p) = ∏ x ∈ Ico 1 (succ (p - 1)), (x : ZMod p) := factorial_is_prod
    _ = ∏ x : (ZMod p)ˣ, (x : ZMod p) := prod_to_units
    _ = -1 := prod_minus_one


section Composite

variable {n : ℕ} [Fact (¬ n.Prime)]


/-
A plausible variation on the above argument seems to suggest that for a composite number `n`,
we should have that `(n-1)! = 0 mod n`. The argument here is that we know that `n` splits up as
`a*b`, for `a, b ≤ n-1`, so `a*b` should appear in the expansion of `(n-1)!`, meaning the whole
thing must be `0`.
-/

theorem wilson2 {h : n ≠ 0} : n ≠ 4 → ((n - 1)! : ZMod n) = 0 := by plausible

/-
Oh no, our theorem doesn't hold! Indeed, we seem to be getting a counter example that 4! = 2 mod 4.
Can you see why the above argument sketch doesn't work for `n = 4`? Try to modify the guard (i.e.
the bit of the expression that currently says `n > 0`) to get an expression that plausible
doesn't complain about.
-/





/-
Again, spoilers below the line!
-/
---------------------------------------------------------------------------------------------------



/-
As it turns out, somewhat surprisingly `4` is the only counter example! So we have the following
statement for composite numbers. The argument structure is quite similar to above, try and take
inspiration to prove the following theorem:
-/

theorem wilson_composite (h : n ≠0 ∧ n ≠ 4) : ((n-1)! : ZMod n) = 0 := by sorry


end Composite

variable {a : ℕ}

/-
# Applications of Wilson's thoerem

Wilson's theorem is not only nice on its own, but it can also be used to show some other cool number
theory results. One of these you might have heard of is *Fermat's little theorem*. This says that
for any integer `a` and prime `p`, we have that `a^(p-1) = 1 mod p`.

The argument is the following:

From Wilson's theorem, we know that `1*2*3*...*(p-1)` is `-1 mod p`. Since `ZMod p` is a group,
the map `fun x ↦ (a : ZMod p) * x` is a bijection. Hence, this product can also be written as:
`(a*1)*(a*2)*...*(a*(p-1))`. But this is just `a^(p-1)*(p-1)!`, so `(-1)*a^(p-1) = -1`, hence
`a^(p-1) = 1`.

See if you can follow the proof sketch above to try and prove Fermat's little theorem. Note that
this question has quite a bit less structure than the questions above, so this question is
expected to be a bit tricky!
-/

theorem fermat_little {h : a ≠ 0} : (a^(p - 1) : ZMod p) = 1 := by sorry
