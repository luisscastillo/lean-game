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

/-
We have seen how to prove a goal of the form `P ∧ Q`, now you will learn how to prove
a goal of the form `P ∨ Q`, which means that either `P` holds or `Q` holds.
In this case, you will have to decide whether you can prove `P` or `Q`. The `left` and `right`
tactics will allow you to change the goal to ⊢ P or ⊢ Q accordingly.
-/

variables {Ω : Type} [IncidencePlane Ω] -- hide

/- Lemma : no-side-bar
Example of the usage of left and right
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
