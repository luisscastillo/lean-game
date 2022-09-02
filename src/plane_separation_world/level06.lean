import plane_separation_world.level05 --hide
open IncidencePlane --hide

/-
# Plane Separation World

## Level 6: on the way to the final level (III).

This is the third of five lemmas that we need to prove before jumping into the final level of the game! You will be provided with 
its mathematical proof in paper right below. Remember that you can use all the theorem statements from the left-hand side box.

## Mathematical proof in paper...

**Claim:** Given a line ℓ and the segments A·B and B·C, if both segments are on the same side of ℓ, then `A ∉ ℓ ∧ B ∉ ℓ ∧ C ∉ ℓ`.

**Proof:**

By the lemma `not_in_line_of_same_side_left`, since the points A and B are on the same side of ℓ, then `A ∉ ℓ`.

By the lemma `not_in_line_of_same_side_right`, since the points A and B are on the same side of ℓ, then `B ∉ ℓ`. 

By the lemma `not_in_line_of_same_side_right`, since the points B and C are on the same side of ℓ, then `C ∉ ℓ`. Hence, we have shown that `A ∉ ℓ ∧ B ∉ ℓ ∧ C ∉ ℓ`. 

-/

/- Hint : Click here for a hint, in case you get stuck.
Starting the proof by typing `repeat {split},` may get you going. In case you feel bewildered, do not hesitate
to click on "View source" (located on the top right corner of the game screen) to see the solution.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/- Lemma :
Given a line ℓ and the segments A·B and B·C, if both segments are on the same side of ℓ, then `A ∉ ℓ ∧ B ∉ ℓ ∧ C ∉ ℓ`. 
-/
lemma same_side_of_noncollinear_ne_line (hlAB : same_side ℓ A B) (hlBC : same_side ℓ B C) : 
A ∉ ℓ ∧ B ∉ ℓ ∧ C ∉ ℓ :=
begin
  repeat {split},
  apply not_in_line_of_same_side_left hlAB,
  apply not_in_line_of_same_side_right hlAB,
  apply not_in_line_of_same_side_right hlBC,
end
