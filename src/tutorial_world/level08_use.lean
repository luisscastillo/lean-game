import tutorial_world.level07_split --hide
open IncidencePlane --hide
open set --hide

/- Tactic : use

## Summary
The tactic use specializes the goal with a particular case.
For example, if we want to prove the statement "there exists a natural number which is odd",
we will need to provide a concrete number like 3. 
-/

/-
Sometimes we will need to prove that there exists an object satisfying certain properties.
The goal will then look like ⊢ ∃ x, P x. In this case, the `use` tactic is useful. If we know
that an object `a` satisfies the  property `P`, then `use a` will transform the goal into ⊢ P a.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma : no-side-bar
Given a point, there is always a line containing it.
-/
lemma line_containing_point (P : Ω) : ∃ ℓ : Line Ω, P ∈ ℓ :=
begin
  use line_through P P,
  exact line_through_left P P,


end