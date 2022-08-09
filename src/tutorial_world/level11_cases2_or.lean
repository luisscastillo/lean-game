import tutorial_world.level10_cases1_and --hide
open set IncidencePlane --hide

variables {Ω : Type} [IncidencePlane Ω] --hide

/-
Suppose now that your hypothesis says that `P`
**or** `Q` holds. That is, you have `h : P ∨ Q`. Then `cases h` will
create two new goals, and in each of them it will
replace `h` with `h : P` in the first case, and with `h : Q` in the second.

-/

/- Lemma : no-side-bar
If X is any set in Ω and either P or Q is in X, then X is not empty.
-/
lemma nonempty_example (P Q : Ω) (X : set Ω) (h : P ∈ X ∨ Q ∈ X) : ∃ R, R ∈ X :=
begin
  cases h,
  {
    use P,
    exact h
  },
  {
    use Q,
    exact h
  }




end

