import Mathlib.Tactic

-- # Functions : Properties

-- ### Class


open Function

variable {X Y Z : Type}

theorem injective_def (f : X → Y) : Injective f ↔ ∀ a b : X, f a = f b → a = b := by
  rfl

theorem surjective_def (f : X → Y) : Surjective f ↔ ∀ b : Y, ∃ a : X, f a = b := by
  rfl

theorem id_eval (x : X) : id x = x := by
  rfl

-- Function composition
theorem comp_eval (f : X → Y) (g : Y → Z) (x : X) : (g ∘ f) x = g (f x) := by
  rfl


example : Injective (id : X → X) := by
  rw [injective_def]
  intro x₁ x₂ h
  rw [id_eval, id_eval] at h
  exact h

-- with definitional equality and unfolding
example : Injective (id : X → X) := by
  intro x₁ x₂ h
  exact h

example : Surjective (id : X → X) := by
  intro x
  use x
  rfl


-- ### Exercises

example {f : X → Y} {g : Y → Z} (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) :=  by
  sorry

example {f : X → Y} {g : Y → Z} (hgf : Surjective (g ∘ f)) : Surjective g := by
  sorry
