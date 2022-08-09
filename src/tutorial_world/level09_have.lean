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
In this level we introduce the new tactic `have`. It is used to add a new hypothesis
to the context (of course, you will have to prove it!). This is sometimes useful to
structure our proofs. In this particular level, it is convenient to prove first that
`r = line_through B C`, then that `s = line_through B C` and that allows us to
finish the prove very easily.
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
