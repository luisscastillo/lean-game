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
In this level we learn the tactic `exact`, which solves a goal that is exactly one of the hypotheses.
The lemma is the same as in the previous level, but we will solve it in a different way.
-/

/- Hint : Click here for a hint, in case you get stuck.
By doing a `rw` you will get the goal to look exactly like one of the hypotheses...
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

