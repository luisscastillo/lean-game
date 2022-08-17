import tutorial_world.incidenceplane --hide
open IncidencePlane --hide

/- Axiom :
incidence (P Q : Point) (ℓ : Line) : P ≠ Q → P ∈ ℓ → Q ∈ ℓ → ℓ = line_through P Q
-/

/- Tactic : intro

## Summary:

`intro p` will turn a goal `⊢ P → Q` into a hypothesis `p : P`
and goal `⊢ Q`. If `P` and `Q` are sets `intro p` means "let $p$ be an arbitrary element of $P$".
If `P` and `Q` are propositions then `intro p` says "assume $P$ is true". 

## Details

If your goal is a function or an implication `⊢ P → Q` then `intro`
will always make progress. `intro p` turns

`⊢ P → Q`

into 

```
p : P
⊢ Q
```

The opposite tactic to intro is `revert`; given the situation
just above, `revert p` turns the goal back into `⊢ P → Q`.

**Variant:** Instead of calling `intro` multiple times, you can use
`intros`. That is, `intros h₁ h₂` is equivalent to `intro h₁, intro h₂`.

## Example

If your goal is an implication $P\implies Q$ then Lean writes
this as `⊢ P → Q`, and `intro p,` can be thought of as meaning
"let $p$ be a proof of $P$", or more informally "let's assume that
$P$ is true". The goal changes to `⊢ Q` and the hypothesis `p : P`
appears in the local context.

-/

/-
#Tutorial World

## Level 6: the `intro` tactic.

This level introduces the `intro` tactic. This allows you to create
a new hypothesis in the local context, just above the goal with the `⊢` symbol, whenever you see
the **`→`** symbol in the "goal" section. [**Remember:** the **`→`** symbol refers to the idea of 
an **implication**. `P → Q` is read as "P implies Q" and interpreted as "If P happens, then Q also happens".]  
In Lean, if we have the goal `⊢ IT RAINS → I GET WET`, by typing `intro h` we will get a new hypothesis in 
the local context of the type `h : IT RAINS` and the goal will just change into  `⊢ I GET WET`.

To solve this level, you will need to use a new statement that has been added to the list of "Theorem statements": 

incidence (P Q : Point) (ℓ : Line) : P ≠ Q → P ∈ ℓ → Q ∈ ℓ → ℓ = line_through P Q

Now, delete the `sorry` and note how the goal changes into a list of implications. [**Pro tip:** instead of writing 
several lines of code with the `intro` tactic, try to use the `intros` tactic. This will make the computer understand 
that you want to create more than one hypothesis at the same time.] For example, if you type `intros h1 h2 h3 h4`, four 
new hypotheses will be added to your local context. Once you've added all the possible hypotheses to it, try to compare
the goal with the `incidence` statement. Did you notice that we can `rewrite` that statement? Because we have the first
three **hypotheses** of the statement, we can change the line `r` into `line_through A B`! Type `rewrite h1 h2 h4` and 
see how the goal changes. To close the goal, try to apply the same argument to the line `s`. 

Bewildered? Click on the box right below for a hint.

/- Hint : Click here for a hint, in case you get stuck.
In case you wrote `intros h1 h2 h3 h4 h5` in the first line, after typying `rewrite h1 h2 h4`, click on enter and
write `rewrite h1 h3 h5`. Now, the goal should change into `⊢ line_through A B = line_through A B`, but Lean finishes the 
proof for us because it realises that automatically!
-/


variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B : Ω} {r s : Line Ω} -- hide

/- Lemma :
If two lines contain two distinct points, then they are the same
-/
lemma equal_lines_of_contain_two_points :
A ≠ B → A ∈ r →  A ∈ s → B ∈ r → B ∈ s → 	r = s :=
begin

  intros hAB hAr hAs hBr hBs,
  rw incidence hAB hAr hBr,
  rw incidence hAB hAs hBs,

end

## Another proof for the same level

Mathematics is not black or white. We can provide different proofs to solve the same lemma. In the explanation showed above, 
we've seen how we the goal changes into `⊢ line_through A B = s` after writing `rewrite h1 h2 h4`. But, what would happen if we type
`rewrite h1 h3 h5` just before that line? If you try it, you will see that the goal changes into `⊢ r = line_through A B`. Make an
effort to understand why that happens so that you're ready to face the next level with ease! 
 




