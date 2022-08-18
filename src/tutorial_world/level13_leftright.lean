import tutorial_world.level12_cases3_exists --hide
open IncidencePlane --hide
open set --hide

/- Tactic : left and right
## Summary
`left` and `right` work on the goal, and they change
`⊢ P ∨ Q` to `⊢ P` and `⊢ Q` respectively.
## Details
The tactics `left` and `right` work on a goal which is a type with
two constructors, the classic example being `P ∨ Q`. 
To prove `P ∨ Q` it suffices to either prove `P` or prove `Q`,
and once you know which one you are going for you can change
the goal with `left` or `right` to the appropriate choice.
-/

/- Tactic : unfold
## Summary
`unfold` works both on the goal and the hypotheses. It transforms some
mathematical expressions into others which are simpler to read. 
## Example
If we find the expression `⊢ collinear {A, B, C}`, then typying `unfold collinear`
will change the goal into `⊢ ∃ (ℓ : Line Ω), ∀ {P : Ω}, P ∈ {A, B, C} → P ∈ ℓ`, which makes 
it easier to understand what `tactic` we should apply to solve the goal.
-/

/-
# Tutorial World

## Level 13: The `unfold`, and the `left` and `right` tactics.

Read the lemma. Do a drawing of the situation. Once you're done, come back here. Until now, we have seen how to 
prove a goal of the form `P ∧ Q` with the `split` tactic. In this level, you will learn how to prove a goal of the
form `P ∨ Q`, which means that either `P` holds or `Q` holds. In this case, you will have to decide whether you can
prove `P` or `Q`. The `left` and `right` tactics will allow you to change the goal to `⊢ P` or `⊢ Q`, respectively.
[**Tip:** Before typing any line, try to think which is the shortest path to finish the proof, either P or Q.]

variables {Ω : Type} [IncidencePlane Ω] -- hide

/- Lemma : no-side-bar
Given three distinct points A, B and C, if C lies in the line through A and B, either A = C or A, B and C are collinear points. 
-/
lemma left_right_example (A B C : Ω) (h : C ∈ line_through A B) :
A = C ∨ collinear ({A, B, C} : set Ω) :=
begin
  right,
  use line_through A B,
  intros P hP,
  cases hP,
  {
    rw hP,
    exact line_through_left A B
  },
  cases hP,
  {
    rw hP,
    exact line_through_right A B,
  },
  {
    cases hP,
    exact h,
  }






end
