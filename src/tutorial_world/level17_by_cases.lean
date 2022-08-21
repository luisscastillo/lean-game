import tutorial_world.level16_exfalso --hide
open IncidencePlane --hide

/- Tactic : by_cases

## Summary

Generates two goals corresponding to a given statement being
true or false

## Details

Suppose that we want to prove a statement `P x`, where `x`
is some number. We may know how to prove it when `x ≤ 5`
and also when `x > 5`, but using a different method.
In this situation, using `by_cases h : x ≤ 5,` will produce
two new goals, the first one with `h : x ≤ 5` in the context
and the second one with `h : ¬ x ≤ 5`.
-/

/-
# Tutorial World 

## Level 17: the `by_cases` tactic.

In this level, we introduce the `by_cases` tactic. Mathematicians would use it to provide a **proof by cases**.
This is useful when we need to split a proof into different cases.
For example, if we are asked to solve a goal of the form `⊢ P ∨ ¬ P`, then `by_cases h : P` will split the goal into two cases, 
assuming `h : P` in the first branch, and `h : ¬ P` in the second branch. With that being said, let's try to solve this level!

[**Tip:** You may want to write the `∈` symbol to solve this level. To do so, type **`\in`** and then hit the space bar. Analogously, 
you can write the `∉` symbol by typing **`\notin`** and then hitting the space bar.]

-/

/- Hint : Click here for a hint, in case you get stuck.
Starting the proof by typing `by_cases h : A ∈ r` will split the goal into two cases, assuming `h : A ∈ r` in the first branch, 
and h : A ∉ r` in the second branch. Then, try to look for a tactic that changes the goal from `⊢ P ∨ Q` to either `⊢ P` or `⊢ Q`.
Still bewildered? Click on "View source" (located on the top right corner of the game screen) to see the solution. 
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma : no-side-bar
Either a point is in a line or it is not.
-/
lemma point_in_line_or_not {A : Ω}	{r : Line Ω} : A ∈ r ∨ A ∉ r :=
begin

  by_cases h : A ∈ r,
  { 
    left,
    exact h,
  },
  { 
    right,
    exact h,
  },
  
end
