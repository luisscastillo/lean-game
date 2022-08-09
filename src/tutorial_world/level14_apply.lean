import tutorial_world.level13_leftright --hide
open IncidencePlane --hide
/- Tactic : apply

## Summary

If `h : P → Q` is a hypothesis, and the goal is `⊢ Q` then
`apply h` changes the goal to `⊢ P`. 

## Details

If you have a function `h : P → Q` and your goal is `⊢ Q`
then `apply h` changes the goal to `⊢ P`. The logic is
simple: if you are trying to create a term of type `Q`,
but `h` is a function which turns terms of type `P` into
terms of type `Q`, then it will suffice to construct a
term of type `P`. A mathematician might say: "we need
to construct an element of $Q$, but we have a function $h:P\to Q$
so it suffices to construct an element of $P$". Or alternatively
"we need to prove $Q$, but we have a proof $h$ that $P\implies Q$
so it suffices to prove $P$".

-/

/-
In this level we introduce the new tactic `apply`. Suppose that you have a theorem `h`
that states exactly that your goal is true, provided that some hypotheses are satisfied. Then
`apply h` will change your goal into proving your new hypotheses.
-/

variables {Ω : Type} [IncidencePlane Ω] -- hide
variables {P Q : Ω} -- hide

/- Lemma :
The line through two points is a symmetrical concept
-/
lemma line_through_symmetrical (h : P ≠ Q) : line_through Q P = line_through P Q :=
begin
  apply incidence,
  {
    exact h,
  },
  {
    exact line_through_right Q P,
  },
  {
    exact line_through_left Q P,
  }




end

