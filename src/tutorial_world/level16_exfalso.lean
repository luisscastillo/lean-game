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
In this level we introduce the new tactic `exfalso`. Look at what it does, it is a bit
strange at first. We will also need one of the axioms for our plane, the one that says that
the line through two points contains each of them. You can see the statement of this theorem
on the left sidebar.
-/

/- Hint : Click here for a hint, in case you get stuck.
In Lean, the  negation `¬ P` of a statement is a shorthand for `P → false`. Therefore
start with `exfalso`, and remember that negation is the same as `→ false`.
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