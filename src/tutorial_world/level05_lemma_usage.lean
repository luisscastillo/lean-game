import tutorial_world.incidenceplane --hide
open IncidencePlane --hide

/- Axiom :
line_through_left (P Q : Ω) : P ∈ (line_through P Q)
-/
/- Axiom :
line_through_right (P Q : Ω) : Q ∈ (line_through P Q)
-/

/-
# Tutorial World

## The first axiom of incidence.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma :  no-side-bar
A point lies in the line through it.
-/
lemma point_on_line {A B : Ω} {r : Line Ω} :
B ∈ line_through A B :=
begin
  
  exact line_through_right A B,

end



