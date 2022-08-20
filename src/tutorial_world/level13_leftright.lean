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
If we find the expression `⊢ collinear {A, B, C}`, then typing `unfold collinear`
will change the goal into `⊢ ∃ (ℓ : Line Ω), ∀ {P : Ω}, P ∈ {A, B, C} → P ∈ ℓ`, which makes 
it easier to understand what `tactic` we should apply to solve the goal.
-/

/-
# Tutorial World

## Level 13: the `unfold`, and the `left` and `right` tactics.

Until now, we have seen how to 
prove a goal of the form `P ∧ Q` with the `split` tactic. In this level, you will learn how to prove a goal of the
form `P ∨ Q`, which means that either `P` holds or `Q` holds. In this case, you will have to decide whether you can
prove `P` or `Q`. The `left` and `right` tactics will allow you to change the goal to `⊢ P` or `⊢ Q`, respectively.

[**Tip:** Before typing any line, try to think which is the shortest path to finish the proof, either P or Q.] To
take the best decision, read the lemma and do a drawing of the situation. Once you're done, come back here. In this 
case, it seems clear that proving `⊢ A = C` is not possible, since we don't have any hypotheses we can use to make progress.
In case you are not sure about that, try to prove `⊢ A = C` by typing `left,` and you will see that is not possible to move on from there.
Because of this reason, changing the goal into `⊢ collinear {A, B, C}` by typing `right,` will be the right path to complete this level. 
[**Remember:** In geometry, collinearity is the property of a set of points lying on the same line. In Lean, the elements of a set are
written between curly brackets, separated by commas {A, B, C}.]

Now, you may be wondering how we could step through `⊢ collinear {A, B, C}` if there isn't any `tactic` that works with this form 
of goal. To your surprise, there exists a tactic called `unfold` whose purpose is transforming some mathematical expressions into
others which are simpler to read. Type `unfold collinear,` to see how the goal changes into `⊢ ∃ (ℓ : Line Ω), ∀ {P : Ω}, P ∈ {A, B, C} → P ∈ ℓ`.
This last goal is read as **there exists a line ℓ in the plane Ω "for all" (∀) points P in the plane Ω, such that P being an element of the set of points
A, B and C implies that P is an element of the line ℓ.**

I'm sure that you know now what tactic makes progress with this type of goal. To give you a hint, we need to consider a specific line ℓ in the plane Ω.
Can you see that the hypothesis `h` assumes that the point C is an element of the `line_through A B`? Then, because the goal says that the point P is an
element of the set of points A, B and C, there is no other way than changing the line ℓ into the `line_through A B`. Once you've done that, use the `intros`
tactic to add two new hypotheses to the local context until you see the goal `⊢ P ∈ line_through A B`. From there, 

-/

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
    exact line_through_left A B,
  },
  cases hP,
  {
    rw hP,
    exact line_through_right A B,
  },
  {
    cases hP,
    exact h,
  },

end
