/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.Tactic



-- # Combinatorics

lemma succ_coprime
    {n m : Nat} (h : n = m + 1) : Nat.Coprime n m := by
  rw [h]
  rw [Nat.coprime_self_add_left]
  exact Nat.coprime_one_left m

open Finset

<<<<<<< HEAD:Content/Discrete_Math/Combinatorics.lean
example
  (n : ℕ) (h : 1 ≤ n)
  (A : Finset ℕ) (Adef : A ∈ (powersetCard (n+1) (Icc 1 (2*n)))) :
  ∃ a ∈ A, ∃ b ∈ A, (a≠b) ∧ (Nat.Coprime a b) :=
  by
=======
lemma claim_1
    {n : ℕ} (h : 1 ≤ n)
    {A : Finset ℕ} (Adef : A ∈ (powersetCard (n+1) (Icc 1 (2*n)))) :
    ∃ a ∈ A, ∃ b ∈ A, (a≠b) ∧ (Nat.Coprime a b) := by
>>>>>>> 46541b1f73e9269933b74c8bbdff6eae59c26a9f:Workshop/Discrete_Math/Combinatorics.lean
  rw [mem_powersetCard] at Adef
  have Lem1 :
      ∃ a ∈ A, ∃ b ∈ A, (a≠b) ∧
      ((fun (x : ℕ) => (x+1) / 2) a = (fun (x : ℕ) => (x+1) / 2) b) := by
    let group_fn := (fun x => (x+1) / 2)
<<<<<<< HEAD:Content/Discrete_Math/Combinatorics.lean

    have map_condition : (∀ a, a ∈ A → group_fn a ∈ (Icc 1 n)) :=
      by -- this as exercise ?
=======
    -- A condition to apply `exists_ne_map_eq_of_card_lt_of_maps_to`
    have map_condition : (∀ a, a ∈ A → group_fn a ∈ (Icc 1 n)) := by
>>>>>>> 46541b1f73e9269933b74c8bbdff6eae59c26a9f:Workshop/Discrete_Math/Combinatorics.lean
      intro x xdef
      dsimp [group_fn]
      replace xdef := Adef.1 xdef
      rw [mem_Icc] at *
      constructor
      · rw [Nat.le_div_iff_mul_le]
        · linarith
        · norm_num
      · rw [Nat.div_le_iff_le_mul_add_pred]
        · linarith
        · norm_num

    -- this is the pigeonhole principle
    apply exists_ne_map_eq_of_card_lt_of_maps_to _ map_condition
<<<<<<< HEAD:Content/Discrete_Math/Combinatorics.lean

=======
    -- We're left to show the condition on the sizes
>>>>>>> 46541b1f73e9269933b74c8bbdff6eae59c26a9f:Workshop/Discrete_Math/Combinatorics.lean
    rw [Nat.card_Icc]
    simp only [add_tsub_cancel_right]
    rw [Adef.2]
    simp only [lt_add_iff_pos_right, eq_self_iff_true, Nat.lt_one_iff]
  rcases Lem1 with ⟨a, aA, b, bA, anb, abeq⟩
  dsimp at abeq
  use a ; constructor ; use aA ;
  use b ; constructor ; use bA ;
  constructor ; exact anb ;
<<<<<<< HEAD:Content/Discrete_Math/Combinatorics.lean

  have Lem2 :
    (a+1)%2 ≠ (b+1)%2 :=
    by -- this as exercise ?
=======
  -- To determine which of a and b is the successor,
  -- we investigate the remainders
  have Lem2 : (a + 1) % 2 ≠ (b + 1) % 2 := by
>>>>>>> 46541b1f73e9269933b74c8bbdff6eae59c26a9f:Workshop/Discrete_Math/Combinatorics.lean
    intro con
    have : a + 1 = b + 1 := by
      rw [← Nat.div_add_mod (a+1) 2]
      rw [← Nat.div_add_mod (b+1) 2]
      rw [abeq, con]
    apply anb
    exact Nat.add_right_cancel this

  wlog H : (a+1)%2 < (b+1)%2 with Sym
  · push_neg at H
    rw [ne_comm] at *
    rw [eq_comm] at abeq
    replace H := lt_of_le_of_ne H Lem2
    specialize Sym h Adef
    specialize Sym b bA a aA anb abeq Lem2 H
    rw [Nat.coprime_comm]
    exact Sym

  · have := Nat.mod_lt (b+1) (show 0<2 from by {norm_num})
    interval_cases bcase : ((b+1)%2)
    · exfalso
      exact (Nat.not_lt_zero _) H
    · rw [Nat.lt_one_iff] at H
      rw [Nat.coprime_comm]
<<<<<<< HEAD:Content/Discrete_Math/Combinatorics.lean
      apply succ_coprime b a
=======
      apply @succ_coprime b a -- we may now put out plan to action
>>>>>>> 46541b1f73e9269933b74c8bbdff6eae59c26a9f:Workshop/Discrete_Math/Combinatorics.lean
      apply @Nat.add_right_cancel _ 1 _
      rw [← Nat.div_add_mod (a+1) 2]
      rw [← Nat.div_add_mod (b+1) 2]
      rw [abeq, bcase, H]
