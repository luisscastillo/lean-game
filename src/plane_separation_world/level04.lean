import plane_separation_world.level03 --hide
open IncidencePlane --hide

noncomputable theory --hide
open_locale classical --hide

/-
# Plane Separation World

## Level 4: on the way to the final level (I).

Welcome to the last trip of The Euclid Game! This is the first of five lemmas that we need to prove before jumping into the final level of the game! You will be provided with 
their mathematical proof in paper so as to solve them with ease. Remember to read the lemma and do a drawing of the situation. Let's get started!  

## Mathematical proof in paper...

**Claim:** Given three non-collinear points A, B and C, then A ≠ C.

**Proof:**

Let us assume that `A ≠ C`. That is, `(A = C) → false`. Then, let us assume that `A = C`. Now, we want to prove that this is false. 
We know that A, B, C are non-collinear. That is, `collinear {A, C, B} → false`. Then, it suffices to prove that A, B, C are collinear points.
Because `A = C`, then `collinear {A, C, B} = collinear {C, C, B}`. For this reason, there has to exist a line ℓ and a point P, such that `P ∈ {C, C, B} → P ∈ ℓ`.
Let the line ℓ be the line through B and C. Then, `P ∈ line_through B C`. Because `P ∈ {C, C, B}`, then either P = C or P = B. If P = C, then 
`(P ∈ line_through B C) = (C ∈ line_through B C)`. By the first axiom of incidence (`line_through_right`), we prove that `C ∈ line_through B C`. 
If P = B, then `(P ∈ line_through B C) = (B ∈ line_through B C)`. By the first axiom of incidence (`line_through_left`), we prove that `B ∈ line_through B C`.
-/

/- Hint : Click here for a hint, in case you get stuck.
To solve this level, remember that you can type `unfold collinear,` in order to make progress. In case you feel bewildered, do not hesitate
to click on "View source" (located on the top right corner of the game screen) to see the solution.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/- Lemma :
Given three non-collinear points A, B and C, then A ≠ C.
-/
lemma noncollinear_ne_points (hCol : ¬ collinear ({A, C, B} : set Ω)) : A ≠ C :=
begin
  intro h,
  apply hCol,
  rw h,
  unfold collinear,
  use line_through B C,
  intros P H,
  cases H,
  rw H,
  exact line_through_right B C,
  cases H,
  rw H,
  exact line_through_right B C,
  cases H,
  exact line_through_left B C,
end
