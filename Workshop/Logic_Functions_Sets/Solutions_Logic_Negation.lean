import Mathlib.Tactic -- imports all the Lean tactics


-- # Negation

-- ### Class

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable {P Q R : Prop}

example : True := by trivial

example : True → True := by
  intro h
  exact h

example : False → True := by
  intro h
  trivial

example : False → False := by
  intro h
  exact h

-- exfalso
example : False → P := by
  intro h
  exfalso
  exact h

-- negation
example : False → ¬True := by
  intro h
  intro h2
  exact h


example : False → ¬P := by
  intro h
  intro hP
  exact h

example : P → ¬P → False := by
  intro hP
  intro hnP
  apply hnP
  exact hP

example : P → ¬¬P := by
  intro hP
  intro hnP
  apply hnP
  exact hP

-- by_contra
example : (¬Q → ¬P) → P → Q := by
  intro h hP
  by_contra hnQ
  apply h
  · exact hnQ
  · exact hP

-- same but with contrapose
example : (¬Q → ¬P) → P → Q := by
  intro h
  contrapose
  exact h



-- ### Exercises

example : (True → False) → False := by
  intro h
  apply h
  trivial

example : (True → False) → P := by
  intro h
  exfalso
  apply h
  trivial

example : ¬¬P → P := by
  intro h
  by_contra h2
  apply h
  exact h2
