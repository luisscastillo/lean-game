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
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide


/- Lemma :
There...
-/
lemma not_between_of_between : (A * B * C) → ¬ (B * A * C) :=
begin

  intro h,
  have h' := between_of_collinear (collinear_of_between h),
  unfold xor3 at h',
  tauto,
  
end
