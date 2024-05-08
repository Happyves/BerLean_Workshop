
import Mathlib.Tactic



-- # Class

variable (a b c : ℝ)


example : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]


example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]


#eval 37 - 42

#eval 1 - (2 + 3)
#eval (1 - 2) + 3

#eval 1 + 2 - 3
#eval 1 - 3 + 2

#check Nat.sub_add_comm

variable (n m k : ℕ)

example (h : n + m - n = k) : m = k := by
  rw [Nat.sub_eq_iff_eq_add] at h
  · rw [add_comm] at h
    exact Nat.add_right_cancel h
  · apply Nat.le_add_right


-- # Exercises

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]
  rw [mul_comm a]
  rw [mul_assoc]


example (h : m ≤ n) (h' : k ≤ n - m) : (n - (n - m)) + k ≤ n := by
  rw [Nat.sub_sub_self h]
  rw [← Nat.le_sub_iff_add_le' h]
  exact h'

#check Nat.le_sub_iff_add_le'
#check Nat.sub_sub_self
