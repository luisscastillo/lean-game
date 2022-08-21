import tutorial_world.level17_by_cases --hide
open IncidencePlane --hide

/- Tactic : by_contra

## Summary

It changes the goal from `⊢ P` to `⊢ false` and adds a new hypothesis
of the form `h : ¬ P` to the local context. 

## Real Life Example

If we want to prove `⊢ SKY_ALWAYS_BLUE`, but we assume that `h : SKY_GREY_WHEN_RAINS`, 
type `by_contra z` to add `z : ¬ (SKY_ALWAYS_BLUE)` to the local context and change the
goal into `⊢ false`. Then, argue that `h : SKY_GREY_WHEN_RAINS` to finish the proof.
-/

/-
Congratulations! You are about to finish the first world of The Euclid Game! 
In this level, we introduce the `by_contra` tactic. Mathematicians would use
it to provide a **proof by contradiction**. This tactic changes the goal from 
`⊢ P` to `⊢ false` and adds a new hypothesis of the form `h : ¬ P` to the local context. 

To finish this world, we would like to prove that two distinct lines have **at most**
one point in common. Delete the `sorry` to see the goal appear as `⊢ A = B`. Now, take a look
to the hypotheses that we have in our local context and try to do a drawing of the situation 
by using all of them. Once you're done, note that the points A and B must be equal so that the 
lines r and s satisfy the hypothesis `hrs: r ≠ s`. Then, try to look for a theorem statement which
could be useful for this level. As you've well deduced, `equal_lines_of_contain_two_points`
is the right path to choose. However, note that it states `A ≠ B` and `r = s` instead of `A = B`and
`r ≠ s`, respectively. Because of this reason, the `by_contra` tactic has to join the party. 

Now, try to solve this level by your own in just three lines of code. [**Remember:** whenever you see
a hypothesis of the form `h : P ≠ Q`, Lean can also understand it as `h : ¬ (P = Q)`, or `h : (P = Q) → false`.]
-/

/- Hint : Click here for a hint, in case you get stuck.
Starting the proof by typing `by_contra h,` will change the goal into proving `⊢ false` and add the hypothesis `h : ¬ (A = B)` to the
local context. Now, note that `hrs : r ≠ s` can be also understood as `h : (r = s) → false`. Then, `apply hrs,` will make progress. To finish with,
try to close the goal in just one line by using the `equal_lines_of_contain_two_points` theorem statement.
Still bewildered? Click on "View source" (located on the top right corner of the game screen) to see the solution. 
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B : Ω} --hide
variables {r s : Line Ω} --hide
/- Lemma : 
Two distinct lines have at most one point in common.
-/
lemma distinct_lines_have_at_most_one_common_point
	(hrs: r ≠ s)
	(hAr: A ∈ r) (hAs: A ∈ s) (hBr: B ∈ r) (hBs: B ∈ s) :
	A = B :=
begin

  by_contra h, 
  apply hrs,
  apply equal_lines_of_contain_two_points h hAr hAs hBr hBs,

end
