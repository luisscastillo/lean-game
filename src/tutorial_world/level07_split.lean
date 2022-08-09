import tutorial_world.level06_intro --hide
open IncidencePlane --hide

/- Tactic : split

## Summary:

If the goal is `P ∧ Q` or `P ↔ Q` then `split` will break it into two goals.

## Details

If `P Q : Prop` and the goal is `⊢ P ∧ Q`, then `split` will change it into
two goals, namely `⊢ P` and `⊢ Q`. 

If `P Q : Prop` and the goal is `⊢ P ↔ Q`, then `split` will change it into
two goals, namely `⊢ P → Q` and `⊢ Q → P`.  

## Example:

If your local context (the top right window) looks like this
```
X : Type
A B : set X
x : X
⊢ x ∈ A ↔ x ∈ B
```

then after

`split,`

it will look like this:

```
2 goals
X : Type
A B : set X
x : X
⊢ x ∈ A → x ∈ B


X : Type
A B : set X
x : X
⊢ x ∈ B → x ∈ A
```
-/

/-
In this level we will learn the `split` tactic. It breaks a goal `P ∧ Q` into two goals (proving `P`, and then proving `Q`),
and also breaks goals of the form `P ↔ Q` into proving each of the implications separately.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide


/- Lemma : no-side-bar
If two lines contain two distinct points, then they are the same
-/
lemma line_through_contains_points (P Q : Ω) : P ∈ (line_through P Q) ∧ Q ∈ (line_through P Q)
:=
begin
  split,
  exact line_through_left P Q,
  exact line_through_right P Q,
end

