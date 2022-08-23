import betweenness_world.level01 --hide
open IncidencePlane --hide


/-
# Betweenness World

## Level 2: don't try to break a point into two pieces...

In this level, we are asked to show that points cannot be splitted. You may want to use the theorem statement `different_of_between`. In case you get 
stuck, click right below for a hint. 
-/

/- Hint : Click here for a hint, in case you get stuck.
You can add the hypothesis `hAx : A ≠ x ∧ A ≠ A ∧ x ≠ A` and use the theorem statement commented above to prove it. Then, the `tauto` tactic may help you
to close the goal. Still bewildered? click on "View source" (located on the top right corner of the game screen) to see the solution.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/- Lemma :
A point cannot be between one point. 
-/
lemma no_point_between_a_point (A x : Ω) : (A * x * A) ↔ false :=
begin
    split,
    {
      intro h,
      have hAx : A ≠ x ∧ A ≠ A ∧ x ≠ A,
      apply different_of_between,
      exact h,
      cases hAx with hA hB,
      cases hB with hC hD,
      apply hC,
      refl,
    },
    tauto,
end
