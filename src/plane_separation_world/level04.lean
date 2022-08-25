import plane_separation_world.level03 --hide
open IncidencePlane --hide

/-
# Plane Separation World

## Level 4: the Pasch's Axiom in action...
To solve the following levels, we may want to use the lemma that we are going to prove now. Here you have some hints that could help you to step through it!
**Hint 1:** Whenever you see the word `collinear`, the `unfold` tactic will make progress.
**Hint 2:** Whenever you find a goal or hypothesis of the form `∀ {X : Ω}, X ∈ {A, B, C} → X ∈ r`, the `simp` tactic will make progress.
**Hint 3:** To solve the first goal, you may want to use the theorem statement `incidence` with the `rewrite` tactic.
-/

/- Hint : Click here for a hint, in case you get stuck.
... Still bewildered? Click on "View source" (located on the top right
corner of the game screen) to see the solution. 
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/- Lemma :
Given three distinct points, they are on the same line if and only if they are collinear.
-/
lemma exists_point_on_line (ℓ : Line Ω): ∃ A : Ω, A ∈ ℓ :=
begin
	have A2 := line_contains_two_points ℓ,
  cases A2 with A hA,
  cases hA with B hB,
  cases hB with HAB hl,
  use A,
  rw hl,
  exact line_through_left A B,
end
