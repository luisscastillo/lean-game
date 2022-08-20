import tutorial_world.level15_simp -- hide
open IncidencePlane -- hide

/- Tactic : exfalso

## Summary

Changes the goal to `⊢ false`.

## Details

This may seem hard to prove,
but it is useful when we have a contradiction in the hypotheses.

For example, if we have `h : ¬ P` as a hypothesis and we apply `exfalso`
we can then `apply h` to transform the goal into `⊢ P`.
-/


/-
# Tutorial World

## Level 16: the `exfalso` tactic. 

In this level we introduce the new tactic `exfalso`. It satifies the **Principle of explosion** of classical logic, 
according to which any statement can be proven from a contradiction. In Lean, if we type `exfalso`, the goal will turn
into `⊢ false`. Let's solve this level to see how it works! 

Delete the `sorry` and take a look at the hypothesis `h`, according to which the point P is not an element of the line 
that passes through the points P and Q. This is a contradiction that can be rewritten as `¬ (P ∈ line_through P Q)`, where 
the symbol **¬** means "not". Moreover, it can also be rewritten as `P ∈ line_through P Q → false`. This last way of representing
the contradiction is key to complete this level. By typing `exfalso`, we know that the goal will change into `⊢ false`. Then, look
for a tactic that can turn the goal into `⊢ P ∈ line_through P Q` and you will be almost done! In case you get stuck, click right below for a hint.
-/

/- Hint : Click here for a hint, in case you get stuck.
The `apply` tactic changes the goal from `⊢ Q` to `⊢ P` when we have a hypothesis of the form `h : P → Q`. In this case, `h : P ∉ line_through P Q`
can be interpreted as `P ∈ line_through P Q → false`. Then, because the goal is `⊢ false', `apply h,` will make progress. Still bewildered? Click on "View source" 
(located on the top right corner of the game screen) to see the solution. 
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma : no-side-bar
Prove that 2+2 is 5, using a false hypothesis.
-/
lemma two_plus_two_equals_five (P Q : Ω) (h: P ∉ line_through P Q) : 2 + 2 = 5:=
begin

  exfalso,
  apply h,
  exact line_through_left P Q,
  
end 
