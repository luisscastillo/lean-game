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

## Level 9: the `have` tactic (boss level).

Congratulations! You are half of the way to finish this world! In this level, we introduce the new tactic `have`. It is used to add a new hypothesis
to the context (which, of course, you will have to prove!). This is sometimes useful to structure our proofs. In this particular level, it is convenient
to prove first that `r = line_through B C`, and then that `s = line_through B C`. This strategy will allow us to finish the prove very easily!

To use the tactic `have`, we should follow the following structure: `have h : A = B,`. This line will add the hypothesis `h : A = B` to the local
context and break the proof into two goals. First, Lean will ask us to prove `⊢ A = B` without the hypothesis `h : A = B`. Then, it will ask us to
prove the goal that existed before using the tactic `have` with the support of the new hypothesis `h : A = B` that we have added to the local context.

**Pro tip:** Because you're getting better at this, proofs are going to be more challenging as time goes by. Whenever you see that you have to prove two 
or more goals to finsih one level, you may want to use **curly braces**; that is to say, the **{** - **}** symbols. Inside each of them, you just have to
prove one goal. Then, whenever you want to prove the following one, just open curly braces again. **Don't forget to close them with a comma at the end!**

For example, the first line of this proof will be `have hr : r = line_through B C,` (you can change `hr` into whatever name you are comfortable with to
make reference to the hypothesis `r = line_through B C`). Now, because two goals have appeared, you can type the following structure: 

{
  
(delete this parenthesis and type double space)sorry,
  
}, 

{

(delete this parenthesis and type double space)sorry, 
  
}, 

In this way, by deleting the `sorry`'s, you will be able to prove the goals separately. Now, let's try solve this level together so that you can
easily understand how the syntax of Lean works! 

First, we are going to prove the first goal, which is `⊢ r = line_through B C,`. To begin with, let's look at the "theorem statements" we have. 
Can you note that `incidence` finishes with the same structure as our goal? Then, we have to check if we have the previous implications of `incidence`
in our local context. On the face of it, `h : B ≠ C` and `h1 : B ∈ r ∧ C ∈ r` are what we are looking for. However, `h1` should be divided into `B ∈ r`
and `C ∈ r`, right? [**Rule of thumb:** whenever a hypothesis looks like `h1 : P ∧ Q`, we can refer to `P` and `Q` as `h1.1` and `h1.2`, respectively.]
Then, notice how `exact incidence h h1.1 h1.2,` closes the first goal! 

Before jumping onto the second goal, we may want to rewrite something first. Can you see that we can `rw hr,` (where `hr : r = line_through B C`) to change 
the goal `⊢ r = s` into `⊢ line_through B C = s`. Now, you will be wondering if `exact incidence h h2.1 h2.2,` finishes the proof, but it does not. Do you 
know why? Because the theorem statement called `incidence` works with the goal `⊢ s = line_through B C`, but not with `⊢ line_through B C` = s`. Because of 
this reason, we should create another hypothesis by using the `have` tactic. That is to say, type `have hs : s = line_through B C,` right before the curly braces.

Now, two final goals are waiting to be proved! I'm sure that you are able to complete the level by your own! Make an effort to apply the knowledge that
we have acquired so far! In case you get stuck, click right below for a hint. 

-/

/- Hint : Click here for a hint, in case you get stuck.
Do you see that `exact incidence h h2.1 h2.2,` closes the above goal? It is similar to the case that we have proved earlier. 
Now, try to finish the proof by rewriting one of the hypotheses. Still bewildered? Click on "View source" (located on the
top right corner of the game screen) to see the solution.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma : no-side-bar
If two lines share two distinct points, then they are the same line.
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
