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
# Tutorial World

## Level 14: the `apply` tactic.

In this level, we introduce the new tactic `apply`. Suppose you are asked to prove a goal of the form `⊢ R` and you have a theorem statement called `h` which 
ensures that `h : P → Q → R`. Then, `apply h` will change your goal into proving `⊢ Q` and `⊢ P`. Now, read the lemma and do a drawing of the situation. Once, 
you're done, delete the 'sorry' and try to look for a theorem statement that ends with the form of the goal shown for this level: `⊢ line_through Q P = line_through P Q`.
Can you see that `incidence` is the right theorem statement to use? Type `apply incidence,` and make an effort to finish the proof by your own.

-/

/- Hint : Click here for a hint, in case you get stuck.
The tactic that comes handy for solving the three remaining goals is `exact`. You may need to use a theorem statement to
close two of the goals. Bewildered? Click on "View source" (located on the top right corner of the game screen) to see the solution. 
-/

variables {Ω : Type} [IncidencePlane Ω] -- hide
variables {P Q : Ω} -- hide

/- Lemma :
The line through two points is a symmetrical concept.
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
  },

end

