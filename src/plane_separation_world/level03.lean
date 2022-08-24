import plane_separation_world.level01 --hide
open IncidencePlane --hide

/-
# Plane Separation World

## Level 3: proving useful lemmas...

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
lemma collinear_iff_on_line_through (h : A ≠ B) : collinear ({A, B, C} : set Ω) ↔ C ∈ line_through A B :=
begin
split,
{
  intro h1,
  unfold collinear at h1,
  cases h1 with ℓ hℓ,
  simp at hℓ,
  rw ← (incidence h hℓ.1 hℓ.2.1),
  exact hℓ.2.2,
},
{
  intro h1,
  unfold collinear,
  use line_through A B,
  simp,
  exact h1,
},
end
