import Workshop.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  -- dualise the argument above
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

-- other ways for the "key step in the example below"
  -- most direct way: ≤ is transitive
example: min (min a b) c ≤ a := by
  apply le_trans
  apply min_le_left
  apply min_le_left

-- another, more indirect proof: apply lemma and use linarith
example: min (min a b) c ≤ a := by
  have h: min (min a b) c ≤ min a b := by apply min_le_left
  have h': min a b ≤ a := by apply min_le_left
  linarith [h,h']

example : min (min a b) c = min a (min b c) := by
  -- just case bashing; use calc blocks for the hard part
  apply le_antisymm
  · apply le_min
    · calc min (min a b) c
      _ ≤ min a b := by apply min_le_left
      _ ≤ a := by apply min_le_left
    · apply le_min
      · calc min (min a b) c
        _ ≤ min a b := by apply min_le_left
        -- can remove "by apply": `apply?` suggests a `by exact` thing which contains the proof term
        -- would be "min_le_right a b"; the apply tactic infers the arguments.
        _ ≤ b := by apply min_le_right
      · apply min_le_right
  · apply le_min
    · apply le_min
      · apply min_le_left
      · calc min a (min b c)
        _ ≤ min b c := by apply min_le_right
        _ ≤ b := by apply min_le_left
    · calc min a (min b c)
      _ ≤ min b c := by apply min_le_right
      _ ≤ c := by apply min_le_right

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  -- XXX can I apply this line to both subgoals? right now, just applies to the first
  -- apply add_le_add_right
  · apply add_le_add_right
    apply min_le_left
  · apply add_le_add_right
    apply min_le_right

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  · have h: min (a + c) (b + c) + -c ≤ min a b := by
      nth_rewrite 2 [← add_neg_cancel_right a c]
      nth_rewrite 2 [← add_neg_cancel_right b c]
      apply aux (a+c) (b+c) (-c)
    linarith

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  -- rewrite a as a-b+b, just on the first occurrence
  nth_rewrite 1 [←sub_add_cancel a b]
  -- alternative: rewrite everywhere and simplify a - b + b - b to a-b
  -- rw [←sub_add_cancel a b]
  -- have h: a - b + b - b = a - b := by ring
  -- rw [h]
  -- apply triangle inequality: lhs is |a-b|+|b|
  have h: |a - b + b| ≤ |a - b| + |b| := by apply abs_add (a-b) b
  -- cancel |b| on both sides, done
  linarith
end

-- same example, using a calc proof, TODO fix syntax!
-- example : |a| - |b| ≤ |a - b| := by
--   calc |a| - |b|
--   _ ≤ |a - b| + |b| - |b| := by sorry
--   _ = |a - b| := by ring

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
   apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  apply dvd_add
  · rw [← mul_assoc, mul_comm y x, mul_assoc] -- XXX should be amore direct way!
    apply dvd_mul_right
  · apply dvd_mul_left
  · apply dvd_pow h
    norm_num -- XXX style for use of such tactics?
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  induction' n
  · simp only [Nat.zero_eq, Nat.gcd_zero_right, Nat.gcd_zero_left]
  · rw [Nat.gcd_comm]
end
