import incidence_world.level03 --hide
open IncidencePlane --hide

/-
Remember that a couple of levels ago we proved that a line could help
us deciding that two points were different. Now we will see that
a point can help us deciding that two lines are different.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {P : Ω} {r s : Line Ω} --hide

/- Lemma :
If two lines `r` and `s` do not share a point, then they are not equal.
-/
lemma ne_of_not_share_point  (hPr : P ∈ r)
(hPs : P ∉ s): r ≠ s:=
begin
  intro H,
  rw H at hPr,
  exact hPs hPr,
  
  
  



end