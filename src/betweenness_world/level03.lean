import betweenness_world.level02 --hide
open IncidencePlane --hide


/-
# Betweenness World

## Level 3: don't try to break a point into two pieces...


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
lemma between_points_share_line (hAr : A ∈ r) (hCr : C ∈ r) : 
	(A * B * C) → B ∈ r :=
begin
    intro H,
	have h : ∃ ℓ, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ,
    apply collinear_of_between,
    exact H,
    cases h with s h1,
    have hAC : A ≠ C,
    {
      intro hAC,
      rw hAC at H,
      have hCBC : C ≠ B ∧ C ≠ C ∧ B ≠ C,
      apply different_of_between,
      exact H,
      cases hCBC with hCB hCC,
      cases hCC with hC hBC,
      apply hC,
      refl,
    },
    have hrs : r = s,
    exact equal_lines_of_contain_two_points hAC hAr h1.1 hCr h1.2.2,
    rw ← hrs at h1,
    exact h1.2.1,
end
