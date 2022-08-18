/- Tactic : exact

## Summary 

If the goal is `⊢ X` then `exact x` will close the goal if
and only if `x` is a term of type `X`. 

## Details

Say `P`, `Q` and `R` are types (i.e., what a mathematician
might think of as either sets or propositions),
and the local context looks like this: 

```
p : P,
h : P → Q,
j : Q → R
⊢ R
```

If you can spot how to make a term of type `R`, then you
can just make it and say you're done using the `exact` tactic
together with the formula you have spotted. For example the
above goal could be solved with

`exact j(h(p)),`

because `j(h(p))` is easily checked to be a term of type `R`
(i.e., an element of the set `R`, or a proof of the proposition `R`).

-/

/-
# Tutorial World

## Level 4: the `exact` tactic.

In this level, we learn the `exact` tactic, which solves a goal that is exactly one of the hypotheses.
For example, if the finishing goal is ⊢ `A = B` and we have the hypothesis `z : A = B`, then `exact z`
will complete the level.

This level is a new variant of the the previous one, but we will solve it in a different way. As you can imagine, 
mathematical proofs can be solved in many differents ways, which is something that definitely makes this field special.

## The tactics index

In case you forgot how to use some of the tactics, click on the top left menu to see what we have learned so far. 
Play around with the menus on the left and see what is there currently. More information will appear as you progress.
-/

/- Hint : Click here for a hint, in case you get stuck.
By using the `rw` tactic you will get the goal to look exactly like one of the hypotheses...
-/

variables {Ω : Type} -- hide

/- Lemma : no-side-bar
If A, B and C are points with A = B and B = C, then A = C.
-/
lemma example_exact (A B C: Ω) (h1 : A = B) (h2 : B = C) : A = C :=
begin
  rw h1,
  exact h2,

  
end
