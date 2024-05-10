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
  ext x
  constructor
  · intro hxS
    cases' hxS with y hy
    rw [Set.mem_image]
    use f y
    constructor
    · use y
      constructor
      · exact hy.1
      · rfl
    · exact hy.2
  · intro h
    cases' h with y hy
    cases' hy.1 with z hz
    use z
    constructor
    · exact hz.1
    · rw [← hz.2] at hy
      exact hy.2
