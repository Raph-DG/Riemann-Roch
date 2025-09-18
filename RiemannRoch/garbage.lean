/-
This seems a bit complicated for a 5 minute talk. I'm not sure how well this will go over tbh.
-/
example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    rw[Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    rw [Nat.factorization_mul, Nat.factorization_pow]
    simp [Nat.Prime.factorization_self prime_p]
    rw[add_comm]
    · intro h
      rw[h] at prime_p
      contradiction
    · simp [nnz]
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

example {m : ℕ} : ∃ k : ℕ, Even (m + k) := by
  use m
  unfold Even
  use m


-- Maybe this is a nice little example
example : ∀ x : ℝ, ∃ y : ℝ, x + y = 2 := by
  intro x
  use 2 - x
  ring

example : ¬ ∃ y : ℝ, ∀ x : ℝ, x + y = 2 := by
  intro h
  obtain ⟨y, hy⟩ := h
  have := hy 0
  have := hy 1
  linarith


 /-
 Maybe these examples like we had in the logic exercises of the summer school are more
 appropriate.
 -/
example {p q : Prop} : (p → q) → ¬ q → ¬ p := by
  intro pq nq hp
  specialize pq hp
  specialize nq pq
  exact nq
