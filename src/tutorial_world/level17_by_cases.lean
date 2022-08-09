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
Sometimes we need to split a proof into different cases,
because the arguments depend on some condition. The `by_cases`
tactic does precisely this.
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
  }


  



  
end
