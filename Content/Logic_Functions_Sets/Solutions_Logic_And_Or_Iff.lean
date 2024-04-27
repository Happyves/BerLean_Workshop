
import Mathlib.Tactic


-- # Conjunction, disjunction, equivalence


variable (P Q R S : Prop)


-- three syntaxes for elimination
example : P ∧ Q → P := by
  intro hPaQ
  cases' hPaQ with hP hQ
  exact hP

example : P ∧ Q → Q := by
  intro ⟨hP, hQ⟩
  assumption

example : P ∧ Q → P := by
  intro hPaQ
  exact hPaQ.1


-- combinator
example : (P → Q → R) → P ∧ Q → R := by
  intro hPQR ⟨hP, hQ⟩
  apply hPQR <;> assumption


-- introduction
example : P → Q → P ∧ Q := by
  intro hP
  intro hQ
  constructor
  · exact hP
  · exact hQ

-- introduction rules
example : P → P ∨ Q := by
  intro hP
  left
  exact hP

example : Q → P ∨ Q := by
  intro hQ
  right
  exact hQ

-- elimination
example : P ∨ Q → (P → R) → (Q → R) → R :=
  by
  intro hPoQ hPR hQR
  cases' hPoQ with hP hQ
  · apply hPR
    exact hP
  · exact hQR hQ

-- rintro and instant match
example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
  by
  rintro hPR hQS (hP | hQ)
  · left; apply hPR; exact hP
  · right; exact hQS hQ

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hPQ h
  cases' h with hP hR
  · left; apply hPQ; exact hP
  · right; exact hR


-- ### Equivalences

-- rfl
example : P ↔ P := by
  rfl

-- constructor and rw
example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  constructor
  · intro q
    rw [h]
    exact q
  · intro p
    rw [← h]
    exact p

-- shorter
example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  rw [h]

-- rwa is rw + assumption
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  rwa [h1]

-- by_cases
example : ¬(P ↔ ¬P) := by
  intro h
  cases' h with h1 h2
  by_cases hP : P
  · apply h1 <;> assumption
  · apply hP
    apply h2
    exact hP

-- constructive proof, have
example : ¬(P ↔ ¬P) := by
  intro h
  have hnP : ¬P := by
    cases' h with h1 h2
    intro hP
    apply h1 <;> assumption
  apply hnP
  rw [h]
  exact hnP




-- # Exercises

example : P ∧ Q → Q ∧ P := by
  intro ⟨hP, hQ⟩
  exact ⟨hQ, hP⟩

example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro ⟨hP, _⟩ ⟨_, hR⟩
  exact ⟨hP, hR⟩

example : P ∨ Q → Q ∨ P := by
  intro hPoQ
  cases' hPoQ with hP hQ
  · right
    assumption
  · left
    assumption

example : P ∧ Q ↔ Q ∧ P := by
  constructor <;>
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1⟩

example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h
    constructor
    · intro hP
      apply h
      left
      exact hP
    · intro hQ
      apply h
      right
      exact hQ
  · rintro ⟨hnP, hnQ⟩ (hP | hQ)
    · apply hnP; exact hP
    · exact hnQ hQ
