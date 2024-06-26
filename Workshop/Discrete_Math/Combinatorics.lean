/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.Tactic



-- # Combinatorics



#eval Nat.gcd 12 9
#eval decide (Nat.Coprime 3 4)
#eval decide (Nat.Coprime 2 4)


lemma succ_coprime
    {n m : Nat} (h : n = m + 1) : Nat.Coprime n m := by
  rw [h]
  rw [Nat.coprime_self_add_left]
  exact Nat.coprime_one_left m

open Finset

example
  (n : ℕ) (h : 1 ≤ n)
  (A : Finset ℕ) (Adef : A ∈ (powersetCard (n+1) (Icc 1 (2*n)))) :
  ∃ a ∈ A, ∃ b ∈ A, (a≠b) ∧ (Nat.Coprime a b) :=
  by
  rw [mem_powersetCard] at Adef
  set g := (fun x => (x+1) / 2) with g_def


  have Lem1 :
      ∃ a ∈ A, ∃ b ∈ A, (a≠b) ∧ (g a = g b) :=
      by
      have map_condition : (∀ a, a ∈ A → g a ∈ (Icc 1 n)) :=
        by
        intro x xdef
        rw [g_def]
        replace xdef := Adef.1 xdef
        rw [mem_Icc] at *
        constructor
        · rw [Nat.le_div_iff_mul_le]
          · linarith
          · norm_num
        · rw [Nat.div_le_iff_le_mul_add_pred]
          · linarith
          · norm_num

      have card_condition : (Icc 1 n).card < A.card :=
        by
        rw [Nat.card_Icc]
        rw [Nat.add_sub_cancel]
        rw [Adef.2]
        exact lt_add_one n

      -- this is the pigeonhole principle
      apply exists_ne_map_eq_of_card_lt_of_maps_to card_condition map_condition


  rcases Lem1 with ⟨a, aA, b, bA, anb, abeq⟩
  use a ; constructor ; use aA ;
  use b ; constructor ; use bA ;
  constructor ; exact anb ;

  have Lem2 :
    (a+1)%2 ≠ (b+1)%2 :=
    by
    intro con
    have : a + 1 = b + 1 := by
      rw [← Nat.div_add_mod (a+1) 2]
      rw [← Nat.div_add_mod (b+1) 2]
      dsimp [g] at abeq
      rw [abeq, con]
    apply anb
    exact Nat.add_right_cancel this

  wlog H : (a+1)%2 < (b+1)%2 with Sym
  · push_neg at H
    rw [ne_comm] at *
    rw [eq_comm] at abeq
    replace H := lt_of_le_of_ne H Lem2
    specialize Sym _ h _ Adef
    specialize Sym g_def b bA a aA anb abeq Lem2 H
    rw [Nat.coprime_comm]
    exact Sym

  · have := Nat.mod_lt (b+1) (show 0<2 from by {norm_num})
    interval_cases bcase : ((b+1)%2)
    · exfalso
      exact (Nat.not_lt_zero _) H
    · rw [Nat.lt_one_iff] at H
      rw [Nat.coprime_comm]
      apply succ_coprime
      apply @Nat.add_right_cancel _ 1 _
      rw [← Nat.div_add_mod (a+1) 2]
      rw [← Nat.div_add_mod (b+1) 2]
      dsimp [g] at abeq
      rw [abeq, bcase, H]



-- # Exercise

example
  (n : ℕ)
  (A : Finset ℕ) (Adef : A ∈ (powersetCard (n+1) (Icc 1 (2*n)))) :
  ∃ a ∈ A, ∃ b ∈ A, (a≠b) ∧ a + b = 2*n + 1 :=
  by
  sorry
  -- You're not expected to finish this exercise in time :)
