import incidence_world.level01 --hide
open IncidencePlane --hide

/- Axiom :
line_contains_two_points (ℓ : Line Ω) : ∃ P Q : Ω, P ≠ Q ∧ ℓ = line_through P Q
-/

/-
# Incidence World

## Level 2: proving useful lemmas (I).

If you look at the list of your theorem statements, you will note that the lemma of the previous level has been added. Despite not
being useful now, it will come handy for next levels. Analogously, the lemma of this level will be added to the list of theorem 
statements, so that the computer can remember it in case you need to use it again.

To solve this level, another theorem statement has been added to the list as well. It is called `line_contains_two_points` and makes
reference to the second axiom of incidence. You will need to use it now. Here you have some hints that may help you to prove the lemma. 

1) Add the hypothesis `A2 : ∃ (P Q : Ω), P ≠ Q ∧ ℓ = line_through P Q` by using the `have` tactic.

2) Prove the hypothesis A2 by using the `line_contains_two_points` theorem statement (remember to type the line that you are using).+

3) Work on the hypothesis A2 with the `cases` tactic.

4) You may want to finish the proof with the `line_through_left` or the `line_through_right` theorem statement.

In case you get stuck, click right below for a hint.
-/

/- Hint : Click here for a hint, in case you get stuck.
You will have to use the `cases` tactic three times. Go back to the tutorial world if you don't remember how to use it. Then, "use" one of the points
that you generated and "rewrite" the line ℓ by using one of the hypotheses that you have in the local context. Still bewildered? Click on "View source" 
(located on the top right corner of the game screen) to see the solution. 
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables  {P Q: Ω} {r : Line Ω}  -- hide

/- Lemma :
Given a line, there exists one point in that line.
-/
lemma exists_point_on_line (ℓ : Line Ω): ∃ A : Ω, A ∈ ℓ :=
begin
	have A2 : ∃ (P Q : Ω), P ≠ Q ∧ ℓ = line_through P Q,
  {
    exact line_contains_two_points ℓ,
  },
  cases A2 with A hA,
  cases hA with B hB,
  cases hB with HAB hl,
  use A,
  rw hl,
  exact line_through_left A B,
end
