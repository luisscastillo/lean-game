import tutorial_world.level10_cases1_and --hide
open set IncidencePlane --hide

variables {Ω : Type} [IncidencePlane Ω] --hide

/-
# Tutorial World

## Level 11: The `cases` tactic (II).

Suppose now that your hypothesis says that `P` **or** `Q` holds. That is, you have `h : P ∨ Q`. Then `cases h` will create
two new goals, and in each of them it will replace `h` with `h : P` in the first case, and with `h : Q` in the second.

To solve this level, you may need to remember how to employ the `use` tactic. As a reminder, note that if the goal is of 
the form `⊢ ∃ (R : Ω), R ∈ X`, then you can type `use ?,', where `?` is any object that satisfies the property of R, so that it
turns the goal into `⊢ ? ∈ X`. The object you are looking for either is found in "Theorem statements" or in the hypotheses located 
right above the goal of this level. [**Reminder:** if the goal breaks into two goals, remember that you can use curly braces to make 
the look of the proof more visual.]
-/

/- Hint : Click here for a hint, in case you get stuck.
After typying `cases h,`, two goals will appear. Write curly braces to structure the proof. Then, start each goal by typying `use P` 
and `use Q`, respectively. The line that closes the goal is the same for both cases. Still bewildered? Click on "View source" (located on the
top right corner of the game screen) to see the solution.
-/

/- Lemma : no-side-bar
If ℓ is any line in the plane Ω and either the point P or the point Q is in ℓ, then ℓ is not an empty line.
-/
lemma nonempty_example (P Q : Ω) (ℓ : Line Ω) (h : P ∈ ℓ ∨ Q ∈ ℓ) : ∃ R, R ∈ ℓ :=
begin

  cases h,
  {
    use P,
    exact h,
  },
  {
    use Q,
    exact h,
  },
  
end

