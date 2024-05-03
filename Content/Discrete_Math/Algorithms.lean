/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.Tactic


-- # Lists and algorithms on lists

-- ### Class

#check [1,2,3,4]

#check 1 :: 2 :: 3 :: 4 :: []

#check List.cons 1 (List.cons 2 (List.cons 3 (List.cons 4 [])))


def length : List α → ℕ
| [] => 0
| _ :: l => 1 + length l

#eval length [4,2,3,7]

#check List.length


def concat : List α → List α → List α
| [], l => l
| x :: l , L => List.cons x (concat l L)

#eval concat [1,2] [3,4]

#check List.append
#eval [1,2] ++ [3,4]

example (l : List ℕ) : concat l [] = l := by
  induction' l with x l ih
  · unfold concat
    rfl
  · unfold concat
    rw [ih]


def map (f : ℕ → ℕ) : List ℕ → List ℕ
| [] => []
| x :: l => f x :: (map f l)

#eval map (fun x : ℕ => x^2) [1,2,5]

#check List.map
#eval [1,2,5].map (· ^2)

example (l : List ℕ) (f : ℕ → ℕ): length (map f l) = length l := by
  induction' l with x l ih
  · unfold map
    rfl
  · unfold map
    unfold length
    rw [ih]


def get (l : List ℕ) (i : ℕ) (wow : i < l.length): ℕ :=
  match l with
  | [] => (by exfalso ; rw [List.length_nil] at wow ; apply Nat.not_lt_zero _ wow )
  | x :: xs => match i with
              | 0 => x
              | n+1 => get xs n (by rw [List.length_cons] at wow ; apply Nat.lt_of_add_lt_add_right wow )

#eval get [7,8,9] 1 (by decide)


-- ### Exercise

#check List.sublists

#check List.length_sublists

def sublists : List α → List (List α)
| [] => [[]]
| x :: l => (sublists l) ++ ((sublists l).map (List.cons x))

#eval sublists [1,2,3]

example (l : List α) : List.length (sublists l) = 2 ^ List.length l := by
  induction' l with x l ih
  · unfold sublists
    rw [List.length_singleton]
    rw [List.length_nil]
    norm_num
  · unfold sublists
    rw [List.length_append]
    rw [List.length_map]
    rw [ih]
    rw [List.length_cons]
    rw [Nat.succ_eq_add_one]
    rw [pow_add]
    rw [pow_one]
    rw [mul_two]
