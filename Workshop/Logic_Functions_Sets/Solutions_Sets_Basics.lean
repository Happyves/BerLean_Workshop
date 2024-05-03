
import Mathlib.Tactic


-- # Sets, basics


-- ### Syntax


def IsEven (n : ℕ) : Prop :=
  ∃ t, n = 2 * t

#check {n : ℕ | IsEven n}

example : 74 ∈ {n : ℕ | IsEven n} := by
  use 37

example : 74 ∈ {n : ℕ | IsEven n} := by
  rw [Set.mem_def]
  use 37



-- ### Operations

variable (X : Type) (A B C D : Set X)  (x : X)


example : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B := by
  rfl

#check Set.subset_def


example : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := by
  rfl

#check Set.mem_union

#check Set.mem_inter


example : x ∈ (Set.univ : Set X) := by
  apply Set.mem_univ

example : x ∈ (∅ : Set X) → False := by
  rw [Set.mem_empty_iff_false]
  trivial


example : x ∉ A → x ∈ A → False := by
  intro h
  exact h

example : x ∈ A → x ∉ A → False := by
  intro h1 h2
  exact h2 h1


example : x ∉ (∅ : Set X) := by
  intro h
  exact h

example : x ∈ Aᶜ ↔ x ∉ A := by rfl

example : A ⊆ B → B ⊆ A → A = B := by
  intro hAB hBA
  ext x
  constructor
  · intro h
    apply hAB
    exact h
  · intro h
    apply hBA
    exact h


-- ### Exercises

example : A ⊆ B → A ⊆ C → A ⊆ B ∩ C := by
  intro hAB hAC x hxA
  constructor
  · apply hAB
    exact hxA
  · exact hAC hxA

example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A :=
  by
  rintro hBA hCA x (hxB | hxC)
  · exact hBA hxB
  · exact hCA hxC

example : ∅ ⊆ A := by
  intro x hx
  rw [Set.mem_empty_iff_false] at hx
  exfalso
  exact hx

example : A ⊆ B → x ∉ B → x ∉ A := by
  intro hAB hB hA
  apply hB
  exact hAB hA
