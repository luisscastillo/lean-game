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
lines r and s satisfy the hypothesis `hrs: r ≠ s`. Then, try to look for 
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
