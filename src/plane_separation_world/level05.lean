import plane_separation_world.level04 --hide
open IncidencePlane --hide

noncomputable theory --hide
open_locale classical --hide

/-
# Plane Separation World

## Level 5: on the way to the final level (II).

This is the second of five lemmas that we need to prove before jumping into the final level of the game! You will be provided with 
its mathematical proof in paper right below. Remember that you can use all the theorem statements from the left-hand side box.

## Mathematical proof in paper...

**Claim:** Given three non-collinear points A, B and C, then B is not incident with the line through A and C.

**Proof:**

By the lemma `noncollinear_ne_points`, since A, B and C are non-collinear points, then `A ≠ C`.

By the lemma `collinear_iff_on_line_through`, since `A ≠ C`, then it suffices to prove that the points A, C, B are not collinear. 

By the assumption of the lemma `hCol : ¬ collinear ({A, C, B} : set Ω))`, then we show that `B ∉ line_through A C`.

-/

/- Hint : Click here for a hint, in case you get stuck.
If you have a theorem statement called `theorem1`, which shows `x` by using the hypothesis `h : P`, then `have htheorem := theorem1 h` will
add the hypothesis `htheorem : x` to the local context. In case you feel bewildered, do not hesitate
to click on "View source" (located on the top right corner of the game screen) to see the solution.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/- Lemma :
Given three non-collinear points A, B and C, then B is not incident with the line through A and C.
-/
lemma noncollinear_ne_line (hCol : ¬ collinear ({A, C, B} : set Ω)) : B ∉ line_through A C :=
begin
  have hAC := noncollinear_ne_points hCol,
  rw ← collinear_iff_on_line_through hAC,
  exact hCol,
end
