/- Tactic : rw

## Summary

If `h` is a proof of `X = Y`, then `rw h,` will change
all `X`s in the goal to `Y`s. 

**Variants:** `rw ← h` changes
`Y` to `X` and
`rw h at h2` changes `X` to `Y` in hypothesis `h2` instead
of the goal.

## Details

The `rw` tactic is a way to do "substituting in". There
are two distinct situations where use this tactics.

1) If `h : A = B` is a hypothesis (i.e., a proof of `A = B`)
in your local context (the box in the top right)
and if your goal contains one or more `A`s, then `rw h`
will change them all to `B`'s. 

2) The `rw` tactic will also work with proofs of theorems
which are equalities (look for them in the drop down
menu on the left, within Theorem Statements).

**Important note:** if `h` is not a proof of the form `A = B`
or `A ↔ B` (for example if `h` is a function, an implication,
or perhaps even a proposition itself rather than its proof),
then `rw` is not the tactic you want to use. For example,
`rw (P = Q)` is never correct: `P = Q` is the true-false
statement itself, not the proof.
If `h : P = Q` is its proof, then `rw h` will work.

**Pro tip 1:** If `h : A = B` and you want to change
`B`s to `A`s instead, try `rw ←h` (get the arrow with `\l`,
note that this is a small letter L, not a number 1).

### Example:
If it looks like this in the top right hand box:
```
A B C : Point
h1 : A = B
h2 : B = C
⊢ A = C
```

then

`rw h1,`

will change the goal into `⊢ B = C`.

### Example: 
You can use `rw` to change a hypothesis as well. 
For example, if your local context looks like this:
```
A B C : Point
h1 : A = C
h2 : A = B
⊢ B = C
```
then `rw h1 at h2` will turn `h2` into `h2 : C = B` (remember operator precedence).

-/


/-
# Tutorial World

## Level 2: The rewrite (`rw`) tactic.

The next tactic we will learn is `rw` (from rewrite). Rewriting is one of the most basic methods of proof, 
where we "substitute" one object that we know that is equal to another.

For example, if `h : A = B` is a hypothesis (i.e., a proof of `A = B`) in your local context (the box in the top right)
and if your goal contains one or more `A`s, then `rw h` will change them all to `B`'s.

Now, delete the sorry and take a look in the top right box at what we have. The variables `A`, `B` and `C` are 
points that lie in the plane `Ω`. Here we have to prove that if the point $A$ is equal to the point $B$, 
and the point $B$ is equal to the point $C$, then the point $A$ is equal to the point $C$.

Now try to use a sequence of rewrite steps to prove the lemma below by typing them into the box underneath, 
between the begin and end lines that tell Lean you are starting and finishing a proof.

Right below this explanation, you will find a grey box where a "Hint" is hidden in case you get stuck. Click on
it to step through this level faster, but remember to use it wisely! From now on, you will find a "Hint" for each level.

-/

/- Hint : Click here for a hint, in case you get stuck.
Delete `sorry` and type `rw h1,` (don't forget the comma!). Then, note how the goal changes into ⊢ B = C. Directly after,
try to think what would happen if you write `rw h2,`. Typying that line will finish the proof instead of wiritng ⊢ C = C . This is
because Lean tries to apply `refl` right after some tactics, and `rw`is one of them!
-/

variables {Ω : Type} -- hide

/- Lemma : no-side-bar
If A, B and C are points with A = B and B = C, then A = C.
-/
lemma example_rw (A B C: Ω) (h1 : A = B) (h2 : B = C) : A = C :=
begin
  rw h1,
  rw h2,
  
end

## Exploring your proof

Click on `rw h1`, and then use the arrow keys to move your cursor around the proof. 
Go up and down and note that the goal changes -- indeed you can inspect Lean's "state" at 
each line of the proof (the hypotheses, and the goal). Try to figure out the exact place 
where the goal changes. The comma tells Lean "I've finished writing this tactic now, please
process it." Lean ignores new lines, but pays great attention to commas.
