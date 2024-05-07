import Mathlib.Tactic

-- # Induction and natural numbers


-- ### Class


example (n : ℕ) : 0 ≤ n := by
  induction' n with n ih
  · apply Nat.le.refl
  · apply Nat.le.step
    exact ih

example (n : ℕ) : 0 + n = n := by
  induction' n with n ih
  · rw [Nat.add_zero]
  · rw [Nat.add_succ]
    rw [ih]


-- ### Exercises

example (n m: ℕ) : 0 ≤ n + m := by
  sorry
