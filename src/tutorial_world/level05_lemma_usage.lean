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

Just as the roof of a building cannot stand without the bricks that are glued to the floor, 
neither can theorems stand without axioms. In mathematics, we need to set down some starting points 
to build our knowledge, and this is why axioms should join the game. What are axioms? - you will be
wondering... Axioms are unprovable statements which are assumed to be true because of their self-evidence. 
They are served as a premise for further reasoning and arguments, so that we can reach new conclusions from them.

By travelling back in time to 300 B.C., we meet the great mathematician Euclid, who formalized the very 
first axioms of geometry in his well-known book *`The Elements`*.

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



