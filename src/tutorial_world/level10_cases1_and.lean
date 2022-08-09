import tutorial_world.level09_have --hide
open set IncidencePlane --hide

/- Tactic : cases

## Summary:

`cases` is a tactic which works on hypotheses.
If `h : P ∧ Q` or `h : P ↔ Q` is a hypothesis then `cases h with h1 h2` will remove `h`
from the list of hypotheses and replace it with the "ingredients" of `h`,
i.e. `h1 : P` and `h2 : Q`, or `h1 : P → Q` and `h2 : Q → P`. Also
works with `h : P ∨ Q` and with `h : ∃ x, P x`. 

## Details

How does one prove `P ∧ Q`? The way to do it is to prove `P` and to
prove `Q`. There are hence two ingredients which go into a proof of
`P ∧ Q`, and the `cases` tactic extracts them. 

More precisely, if the local context contains
```
h : P ∧ Q`
```

then after the tactic `cases h with p q,` the local context will
change to
```
p : P,
q : Q
```
and `h` will disappear. 

Similarly `h : P ↔ Q` is proved by proving `P → Q` and `Q → P`,
and `cases h with hpq hqp` will delete our assumption `h` and
replace it with
```
hpq : P → Q,
hqp : Q → P
```

Be warned though -- `rw h` works with `h : P ↔ Q` (`rw` works with
`=` and `↔`), whereas you cannot rewrite with an implication.

`cases` also works with hypotheses of the form `P ∨ Q`. Here the situation
is different however. 
To prove `P ∨ Q` you need to give either a proof of `P` *or* a proof
of `Q`, so if `h : P ∨ Q` then `cases h with p q` will change one goal
into two, one with `p : P` and the other with `q : Q`.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/-
The next tactic we introduce is `cases`, and since it does many things
we will have a couple levels seeing when to apply it. This tactic works
always on hypotheses, and it transforms them in different ways. The first
instance that we learn arises when you have a hypothesis that says that `P`
or `Q` holds. That is, you have `h : P ∧ Q`. Then `cases h with h₁ h₂` will 
replace `h` with two new hypotheses, namely `h₁ : P` and `h₂ : Q`.

This is done usually for aesthetic reasons, since `h.1` and `h.2` also serve
as proofs of `P` and `Q`.
-/

/- Lemma : no-side-bar
The line ℓ is the line through P and Q as long as P ≠ Q and both P and Q are in ℓ
-/
lemma line_through_from_and (P Q : Ω) (ℓ : Line Ω) (h1 : P ≠ Q)
(h2 : P ∈ ℓ ∧ Q ∈ ℓ) : ℓ = line_through P Q :=
begin
  cases h2 with hP hQ,
  exact incidence h1 hP hQ,



end

