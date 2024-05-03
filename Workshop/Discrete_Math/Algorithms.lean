/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.Tactic
import Mathlib.Data.List.Sort


/-- Inserting `x` into a list `l` at the first entry where it is smaller -/
def my_insert (x : ℕ) : List ℕ → List ℕ
| [] => [x]
| y :: l =>
    if x ≤ y
    then x :: (y :: l)
    else y :: (my_insert x l)

/-- `y` is in the list obtained by inserting `x` into `l` iff it is either `x` or it is in `l` -/
lemma mem_insertion (x y: ℕ) (l : List ℕ) : y ∈ my_insert x l ↔ (y = x ∨ y ∈ l) := by
  constructor
  · induction' l with z l ih
    · dsimp [my_insert]
      rw [List.mem_singleton]
      apply Or.inl
    · intro H
      dsimp [my_insert] at H
      split_ifs at H with Q
      · rw [List.mem_cons] at H
        exact H
      · rw [List.mem_cons] at H
        cases H with
        | inl lef =>
            right
            rw [lef]
            exact List.mem_cons_self z l
        | inr rig =>
            specialize ih rig
            cases ih with
            | inl a =>
                left
                exact a
            | inr b =>
                right
                exact List.mem_cons_of_mem z b
  · induction' l with z l ih
    · dsimp [my_insert]
      rw [List.mem_singleton]
      intro h
      cases h with
      | inl a => exact a
      | inr b => contradiction
    · intro H
      dsimp [my_insert]
      split_ifs with Q
      · cases H with
        | inl a =>
            rw [a]
            exact List.mem_cons_self x (z :: l)
        | inr b =>
            exact List.mem_cons_of_mem x b
      · cases H with
        | inl a =>
            apply List.mem_cons_of_mem z
            apply ih
            left
            exact a
        | inr b =>
            rw [List.mem_cons] at b
            cases b with
            | inl c =>
              rw [c]
              exact List.mem_cons_self z (my_insert x l)
            | inr d =>
                apply List.mem_cons_of_mem z
                apply ih
                right
                exact d

/-- If list `l` is sorted, then using `my_insert` to insert some number maintains this property -/
lemma insertion_maintains_sort (x: ℕ) (l : List ℕ) (hl : List.Sorted Nat.le l) :
    List.Sorted Nat.le (my_insert x l) := by
  induction' l with y l ih
  · dsimp [my_insert]
    exact List.sorted_singleton x
  · dsimp [my_insert]
    split_ifs with H
    · rw [List.sorted_cons]
      constructor
      · intro z z_def
        rw [List.mem_cons] at z_def
        cases z_def with
          | inl lef =>
              rw [lef]
              apply H
          | inr rig =>
              rw [List.sorted_cons] at hl
              apply le_trans H
              exact hl.left z rig
      · exact hl
    · push_neg at H
      rw [List.sorted_cons] at *
      constructor
      · intro z z_def
        rw [mem_insertion] at z_def
        cases z_def with
        | inl a =>
            rw [a]
            exact le_of_lt H
        | inr b =>
            exact hl.left z b
      · exact ih hl.right
