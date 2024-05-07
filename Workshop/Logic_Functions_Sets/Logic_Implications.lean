import Mathlib.Tactic -- imports all of the tactics in Lean's maths library


-- # Implications


-- ### Class

-- just a quick example to remind people that the stuff taught in this section will be used in concrete contexts
example (hP : 1 + 1 = 2) (hQ : ∀ n : ℕ, ∃ m : ℕ, n < m) (hR : 1 = 0) : 1 + 1 = 2 := by
  exact hP

-- but, for clarity, we'll use dummy propositions for th rest of the section
variable {P Q R : Prop}


example (hP : P) (hQ : Q) (hR : R) : P := by
  exact hP

-- intro
example (hQ : Q) : P → Q := by
  intro h
  exact hQ

-- apply v1
example (h : P → Q) (hP : P) : Q := by
  apply h at hP
  exact hP

-- apply v2
example (h : P → Q) (hP : P) : Q := by
  apply h
  exact hP
  done

-- assumption
example : P → Q → P := by
  intro hP
  intro hQ
  assumption

-- multiple intro, multiple goals, focus
example : (P → Q → R) → (P → Q) → P → R := by
  intro hPQR hPQ hP
  apply hPQR
  · exact hP
  · apply hPQ
    exact hP

-- tauto
example :
    (((P → Q → Q) → (P → Q) → Q) → R) →
      ((((P → P) → Q) → P → P → Q) → R) → (((P → P → Q) → (P → P) → Q) → R) → R := by
  tauto


-- ### Exercises

variable (S T : Prop)

example : (P → Q) → ((P → Q) → P) → Q := by
  sorry

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by
  sorry
