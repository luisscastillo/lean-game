import incidence_world.level06 --hide
open IncidencePlane --hide

/-
# Incidence World

## Level 7: triangles, triangles...

We end this world by proving the existence of triangles using only incidence axioms. To solve this level, the mathematical proof in paper will be
provided to you. The goal is to divide it in two cases and reach a contradiction in each of them. In this sense, it is because we want to reach a contradiction
that we don't need to look for all the possible distributions in each of these two cases. As early as a contradiction is reached, we can prove the opposite of what
the last conclusion has shown us. 

To give you some hints, remember these three Lean tips that might help you to step through the proof. 

**Tip 1:** whenever a hypothesis looks like `h1 : P ∧ Q`, we can refer to `P` and `Q` as `h1.1` and `h1.2`, respectively.]

**Tip 2:** whenever you have a goal of the form `⊢ ∀ (P : Ω), ¬ (P ∧ Q ∧ R)`, the `intros` tactic wil make progress.

**Tip 3:** whenever we use the terms `r`, `s`, `t` to talk about lines in a mathematical proof in paper, we may want to use the terms of the
form `line_through A B` in Lean.

If needed, you can go back to the previous levels to remember how to use some tactics. Good luck! Let's do this!

## The mathematical proof in paper...

**Claim:** There exist three lines that do not have a point in common.

**Proof:** Let P be the point in common.

By the third axiom of incidence, let A, B and C be three non-collinear points that lie on the plane Ω. 

By the first axiom of incidence, let `r` be the line that passes through the points A and B.

By the first axiom of incidence, let `s` be the line that passes through the points A and C.

By the first axiom of incidence, let `t` be the line that passes through the points B and C.

Let us assume that `r ≠ s`. By the lemma `ne_of_not_share_point`, since C ∈ s and C ∉ r, then the lines `r` and `s`
are not equal. 

Now, we proceed with the proof by cases.

**Case 1:** Let P = A. 

Let the point A be incident with the line `t`. Because A = P, then P ∈ t. 

Let `s = t`. By the lemma `equal_lines_of_contain_two_points`, because A ≠ C, A ∈ s, A ∈ t, C ∈ s and C ∈ t, then `s = t`.

Let `s = r`. Because `s = t`, then `t = r`. By the lemma `equal_lines_of_contain_two_points`, because A ≠ B, A ∈ r, A ∈ t, B ∈ r and B ∈ t, then `t = r`.

But this is a contradiction because we previously proved that `r ≠ s`.

Therefore, it is not possible that three lines share a point in common, when P = A.

**Case 2:** Let P ≠ A.

Let `r = s`. By the lemma `equal_lines_of_contain_two_points`, because P ≠ A, P ∈ r, P ∈ s, A ∈ r and A ∈ s, then `r = s`.

But this is a contradiction because we previously proved that `r ≠ s`.

Therefore, it is not possible that three lines share a point in common, when P ≠ A.

Hence, we have shown that there exist three lines that do not have a point in common. 

-/

/- Hint : Click here for a hint, in case you get stuck.
Remember that, when using a lemma, to prove the conclusion of the statement, you have to provide Lean with the previous hypotheses. To finish the proof, 
the `tauto` tactic might help you. Try to write curly braces to structure the proof. Still bewildered? Click on "View source" (located on the top right
corner of the game screen) to see the solution. 
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma :
There exist three lines that do not have a point in common.
-/
lemma three_distinct_lines : ∃ (r s t: Line Ω), (∀ (P : Ω),
¬(P ∈ r ∧ P ∈ s ∧ P ∈ t)) :=
begin
  rcases existence Ω with ⟨A, B, C, ⟨hAB, hAC, hBC, h⟩⟩,
  use line_through A B,
  use line_through A C,
  use line_through B C,
  intros P H,
  have h1 : line_through A C ≠ line_through A B, 
  {
    exact ne_of_not_share_point (line_through_right A C) h,
  },
  by_cases hPA : P = A,
  {
    have hAlBC : A ∈ line_through B C,
    {
      rw ← hPA,
      exact H.2.2,
    },
    have H1 : line_through A C = line_through B C,
    {
      exact equal_lines_of_contain_two_points hAC (line_through_left A C) hAlBC (line_through_right A C) (line_through_right B C),
    },
    have H2 : line_through A C = line_through A B, 
    {
      rw H1,
      exact equal_lines_of_contain_two_points hAB hAlBC (line_through_left A B) (line_through_left B C) (line_through_right A B),
    },
    exact h1 H2,
  },
  {
    have h2 : line_through A C = line_through A B, 
    {
      exact equal_lines_of_contain_two_points hPA H.2.1 H.1 (line_through_left A C) (line_through_left A B),
    },
    tauto,
  },
  
end
