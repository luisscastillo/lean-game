import incidence_world.level01 --hide
open IncidencePlane --hide

/-
The next lemma is not hard to prove, but it will be useful
in the coming levels.
-/

/- Hint : Click here for a hint, in case you get stuck.
Remember that `¬ P` is the same as `P → false`, so `intro` may
get you going.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables  {P Q: Ω} {r : Line Ω}  -- hide

/- Lemma :
If a point P is in a line and a point Q is not, then they are different.
-/
lemma point_in_line_not_point (hP : P ∈ r) (hQ : Q ∉ r): P ≠ Q :=
begin
  intro H,
  rw H at hP,
  exact hQ hP,
  


  
  
  
  
end
