import incidence_world.level04 --hide
open IncidencePlane --hide

/-
# Incidence World

## Level 6: almost there...

Congratulations! You're almost there! To solve this level, we provide you with the mathematical proof in paper. Read it carefully and make
an effort to understand every bit of it. Then, try to type the mathematical proof in Lean by your own. If needed, you can go back to the previous 
levels to remember how to use some tactics. By the way, don't forget your list of theorem statements! Just as a final hint, you may want to start 
your proof by typing `rcases (point_existence_postulate P) with ⟨Q, R, ⟨hPQ, hPR, hQR,H⟩⟩,`... Good luck!

## The mathematical proof in paper...

**Claim:** There are at least two different lines passing through a given point.

**Proof:** Let P be the given point.

By the lemma `point_existence_postulate`, there exist two points Q and R such that the points P, Q and R are non-collinear.

By the first axiom of incidence, let `r` be the line that passes through (= is incident with) the points P and Q.

By the first axiom of incidence, let `s` be the line that passes through the points P and R.

By the lemma `ne_of_not_share_point`, since the point R is incident with the line through P and R and it is not incident with the 
line through P and Q, then the lines `r` and `s` are not equal.

Hence, we have shown that there at least two different lines passing through a given point.

-/

/- Hint : Click here for a hint, in case you get stuck.
This is not a proof by cases. The `use` tactic may get you going with the second and third lines of the proof. To close the last goal,
go back to Level 3 of this world and try to see how we used the `point_in_line_not_point` lemma. Still bewildered? Click on "View source" 
(located on the top right corner of the game screen) to see the solution. 
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma :
There are at least two different lines passing through a given point.
-/
lemma point_exists_two_lines (P : Ω) : ∃ (r s: Line Ω), P ∈ s ∧ P ∈ r ∧ s ≠ r :=
begin
  rcases (point_existence_postulate P) with ⟨Q, R, ⟨hPQ, hPR, hQR,H⟩⟩,
  use line_through P Q,
  use line_through P R,
  split,
  {
    exact line_through_left P R,
  },
  split,
  {
    exact line_through_left P Q,
  },
  {
    exact ne_of_not_share_point (line_through_right P R) H,
  },

end
