import incidence_world.level06 --hide
open IncidencePlane --hide

/-
# Betweenness

## Level 1: ...

explanation

-/

/- Hint : Click here for a hint, in case you get stuck.
... Still bewildered? Click on "View source" (located on the top right
corner of the game screen) to see the solution. 
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma :
There...
-/
lemma three_distinct_lines : ∃ (r s t: Line Ω), (∀ (P : Ω),
¬(P ∈ r ∧ P ∈ s ∧ P ∈ t)) :=
begin
  
  
  
end
