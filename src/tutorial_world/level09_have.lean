import tutorial_world.level08_use --hide
open IncidencePlane --hide
/- Tactic : have

## Summary
`have h : P,` will create a new goal of creating a term of type `P`, and will add `h : P` to the hypotheses for the goal you were working on.

## Details
If you want to name a term of some type (because you want it in your local context for some reason), and if you have the formula for the term, you can use have to give the term a name.

## Example (have q := ... or have q : Q := ...)
If the local context contains

```
f : P → Q
p : P
```
then the tactic `have q := f(p),` will add `q` to our local context, leaving it like this:

```
f : P → Q
p : P
q : Q
```

If you think about it, you don't ever really need `q`, because whenever you think you need it you coudl just use `f(p)` instead. But it's good that we can introduce convenient notation like this.

## Example (have q : Q,)
A variant of this tactic can be used where you just declare the type of the term you want to have, finish the tactic statement with a comma and no :=, and then Lean just adds it as a new goal. The number of goals goes up by one if you use `have` like this.

For example if the local context is

```
P Q R : Prop/Type,
f : P → Q,
g : Q → R,
p : P
⊢ R
```
then after `have q : Q,`, there will be the new goal

```
f : P → Q,
g : Q → R,
p : P,
⊢ Q
```
and your original goal will have `q : Q` added to the list of hypotheses.
-/

/-
# Tutorial World 

## Level 9: The `have` tactic.

Congratulations! You are half of the way to finish this world! In this level, we introduce the new tactic `have`. It is used to add a new hypothesis
to the context (which, of course, you will have to prove!). This is sometimes useful to structure our proofs. In this particular level, it is convenient
to prove first that `r = line_through B C`, and then that `s = line_through B C`. This strategy will allows us to finish the prove very easily!

To use the tactic `have`, we should follow the following structure: `have h : A = B,`. This line will add the hypothesis `h : A = B` to the local
context and break the proof into two goals. First, Lean will ask us to prove `⊢ A = B` without the hypothesis `h : A = B`. Then, it will ask us to
prove the goal that existed before using the tactic `have` with the support of the new hypothesis `h : A = B` that we have added to the local context.

**Pro tip:** Because you're getting better at this, proofs are going to be more challenging as time goes by. Whenever you see that you have to prove two 
or more goals to finsih one level, you may want to use **curly braces**; that is to say, the **{** - **}** symbols. Inside each of them, you just have to
prove one goal. Then, whenever you want to prove the following one, just open curly braces again. **Don't forget to close them with a comma at the end!**

For example, the first line of this proof will be `have hr : r = line_through B C,` (you can change `hr` into whatever name you are comfortable with to
make reference to the hypothesis `r = line_through B C`). Now, because two goals have appeared, you can type the following structure: 

{
  
  sorry,
  
}, 

{

  sorry, 
  
}, 

In this way, by deleting the `sorry`'s, you will be able to prove the goals separately. Now, let's try solve this level together so that you can
easily understand how the syntax of Lean works! 

First, we are going to prove the first goal, which is `⊢ r = line_through B C,`. To begin with, let's look at the "theorem statements" we have. 
Can you note that `incidence` finishes with the same structure as our goal? Then, we have to check if we have the previous implications of `incidence`
in our local context. 

-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma : no-side-bar
If two lines share two distinct points then they are the same
-/
lemma equal_lines_example (B C : Ω) (h : B ≠ C) (r s : Line Ω)
(h1 :  B ∈ r ∧ C ∈ r)
(h2 : B ∈ s ∧ C ∈ s)
: r = s :=
begin
  have hr : r = line_through B C,
  {
    exact incidence h h1.1 h1.2,
  },
  rw hr,
  have hs : s = line_through B C,
  {
    exact incidence h h2.1 h2.2,
  },
  rw hs,
end
