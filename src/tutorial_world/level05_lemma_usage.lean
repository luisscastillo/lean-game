import tutorial_world.incidenceplane --hide
open IncidencePlane --hide

/- Axiom :
line_through_left : P ∈ (line_through P Q)
-/
/- Axiom :
line_through_right : Q ∈ (line_through P Q)
-/

/-
We can apply a theorem that we have already proven by using `exact`
and the appropriate hypotheses.
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



