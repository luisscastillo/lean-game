/- Tactic : refl

## Summary

`refl` is a tactic which proves goals of the form `X = X`.

## Details

The `refl` tactic will close any goal of the form `A = B`
where `A` and `B` are *exactly the same thing*.

### Example:
If it looks like this in the top right hand box:
```
A : Point
⊢ A = A
```

then

`refl,`

will close the goal and solve the level. Don't forget the comma.

-/

/-
We will start by practising with the simplest tactic, namely *refl*. This just proves goals
of the form $A = A$, no matter how complicated $A$ is. Let's see it in action!
-/

/- Hint : Click here for a hint, in case you get stuck.
Just delete `sorry` and type `refl,` (don't forget the comma!).
-/

variables {Ω : Type} -- hide

/- Lemma : no-side-bar
If A is a point, then A = A.
-/
lemma refl_example (A : Ω) : A = A :=
begin
  refl,
  
end
