import Mathlib.Tactic

open Nat

-- # Functions : Syntax


-- ### Class

-- Two syntaxes for functions

def first_ver (n : ℕ) : ℕ := n^2

def second_ver := fun n : ℕ => n^2

#check (first_ver)
#check (second_ver)

-- Computability:

#eval first_ver 1
#eval first_ver 2
#eval first_ver 3
#eval first_ver 4


-- No partial functions. Instead, we use:

def pf_1 (n : ℕ) (hn : Odd n) : ℕ := n^2

def pf_2 : {n : ℕ | Odd n} → ℕ := fun n => n^2

#check (pf_1)
#check (pf_2)

#eval pf_2 ⟨3, (by decide)⟩

#eval pf_1 3 (by decide)

-- What do we need partial functions for ?

#eval List.get [1,2,3] ⟨1 , (by decide)⟩


-- "Piecewise" definition

def ite_fn (n : ℕ) := if Odd n then 1 else 0

#eval ite_fn 0
#eval ite_fn 1
#eval ite_fn 2
#eval ite_fn 3

def match_fn (n : ℕ) :=
  match n with
  | 42 => 42
  | _ => 0

#eval match_fn 0
#eval match_fn 37
#eval match_fn 42

def match_fn_2 (n : ℤ) :=
  match decide (n > 0) with
  | true => 42
  | false => 0

#eval match_fn_2 (-4)
#eval match_fn_2 37
#eval match_fn_2 42

def Fermat (n : ℕ) := ∃ x : ℕ, x > 0 ∧ ∃ y > 0, ∃ z > 0, x^n +y^n = z^n

open Classical in
noncomputable
def match_fn_3 (n : ℕ) :=
  match decide (Fermat n) with
  | true => 42
  | false => 0

#check match_fn_3



-- ### Exercise

-- Define the ReLU on ℚ

def ReLU (x : ℚ) : ℚ :=
  if x ≤ 0
  then 0
  else x

#eval ReLU 1
#eval ReLU (1/2)
#eval ReLU (-3)
