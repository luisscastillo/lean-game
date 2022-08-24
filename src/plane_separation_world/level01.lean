import plane_separation_world.hilbertaxioms --hide
open IncidencePlane --hide

/-
# Plane Separation World

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
lemma not_in_line_of_same_side_left (h : same_side ℓ A B) : A ∉ ℓ :=
begin
  by_contradiction h1,
  unfold same_side at h,
  simp at h,
  have h2 : A ∈ pts(A⬝B) ∩ ℓ,
  {
    split;
    simp [h1],
  },
  finish,
end
