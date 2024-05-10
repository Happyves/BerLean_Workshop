import Mathlib.Tactic

-- # Preimages and images

-- ### Class

variable {X Y Z : Type} (f : X → Y) (S : Set X) (T : Set Y)

example : S ⊆ f ⁻¹' (f '' S) := by
  intro x hx
  rw [Set.mem_preimage]
  rw [Set.mem_image]
  use x

example : S ⊆ f ⁻¹' (f '' S) := by
  intro x hx
  use x

example : f '' (f ⁻¹' T) ⊆ T := by
  intro x hx
  rw [Set.mem_image] at hx
  cases' hx with y hy
  rw [Set.mem_preimage] at hy
  rw [← hy.2]
  exact hy.1

example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by
  constructor
  · intro h x hxS
    refine h ⟨x, hxS, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    refine h hx


-- ### Exercises

example (g : Y → Z) : g ∘ f '' S = g '' (f '' S) := by
  sorry
