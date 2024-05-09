
import Mathlib.Tactic



-- # Finite sets and big operators


-- ### Syntax

#check ({0,1,2} : Finset ℕ)

open BigOperators

#eval ∑ x in ({0,1,2} : Finset ℕ), x^2


-- ### Example


#eval Finset.range 7

#check Finset.sum_range_succ

example (n : ℕ) (f : ℕ → ℕ) :
  ∑ x in Finset.range (n + 1), f x = ∑ x in Finset.range n, f x + f n := by
  rw [Finset.range_succ]
  rw [Finset.sum_insert]
  · rw [add_comm]
  · rw [Finset.mem_range]
    apply lt_irrefl


#check Finset.card_range

example (n : ℕ) : (Finset.range n).card = n := by
  induction' n with n ih
  · rw [Finset.range_zero]
    rfl
  · rw [Finset.range_succ]
    rw [Finset.card_insert_of_not_mem]
    · rw [ih]
    · rw [Finset.mem_range]
      apply lt_irrefl



-- ### Exercises


example (n : ℕ) : 2*(∑ x in Finset.range (n+1), x) = n*(n+1) := by
  induction' n with n ih
  · rw [Finset.range_one]
    rw [Finset.sum_singleton]
  · rw [Finset.sum_range_succ]
    rw [mul_add]
    rw [ih]
    ring
