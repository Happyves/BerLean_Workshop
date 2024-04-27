
import Mathlib.Tactic


-- # Quantifiers


-- ### Computation

example : 2  + 2 = 4 := by norm_num

example : 2 + 2 ≠ 5 := by norm_num

example : 2 + 2 < 5 := by norm_num

example (x y : ℤ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by ring


-- ### Existence

example : ∃ x : ℝ, 3 * x + 7 = 12 := by
  use 5 / 3
  norm_num


-- ### Universal quantification

example : ∀ a b : ℤ, ∃ x, (a + b) ^ 3 = a ^ 3 + x * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 :=
  by
  intro a b
  use 3
  ring



-- ### Exercises

example : ∃ x : ℤ, 3 * x + 7 ≠ 12 := by
  use 0
  norm_num

example : ∃ x : ℤ, ∀ y, y + y = x * y := by
  use 2
  intro y
  ring

example : ∀ x : ℤ, ∃ y, x + y = 2 := by
  intro x
  use 2 - x
  ring
