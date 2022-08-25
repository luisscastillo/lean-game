import plane_separation_world.level03 --hide
open IncidencePlane --hide

/- Axiom :
not_on_line_iff_not_collinear (h2 : A ≠ B) (h1: ¬ collinear({A,B,C} : set Ω ))
: C ∉ line_through A B
-/

/-
# Plane Separation World

## Level 4: the Pasch's Axiom in action... (final level)

To solve this level, a new theorem statement has been added to the list. It is called `not_on_line_iff_not_collinear`. Because this level is challenging, 
you may want to read the following hints:

**Hint 1:** Make sure that you have all the hypotheses needed to use the Pasch's Axiom. 

**Hint 2:** Whenever you see the hypothesis `h : ¬∃ (x : Ω), x ∈ ℓ ∧ x ∈ line_through P Q ∧ P*x*Q`, type `push_neg at h` to make progress.

**Hint 3:** Whenever you see a goal of the form `⊢ {x : Ω | x = P ∨ x = Q ∨ P*x*Q} ∩ ↑ℓ = ∅`, type `ext,` to make progress.

Before typing anything in Lean, read the lemma and try to write a proof in paper. In case you want to see a possible solution to this level, 
click on "View souce" (located on the top right corner of the game screen). 

## Next version of The Euclid Game

In the next version of The Euclid Game, it would be nice to extend the Plane Separation World with more levels and add the Congruence World. 

## What's next?

If you liked the game and want to learn more, look <a href="https://github.com/ImperialCollegeLondon/natural_number_game/blob/master/WHATS_NEXT.md"
target="blank">here</a> for more ideas about what to do next.
-/

/- Hint : Click here for a hint, in case you get stuck.
You may want to start the proof with the `by_contra` tactic. Click on "View source" (located on the top right
corner of the game screen) to see the solution, in case you get stuck.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/- Lemma :
Given three non-collinear points A, B, C and a line ℓ that is not incident with them, if A and B are not on the same side of 
ℓ and A and C are not on the same side of ℓ, then B and C are on the same side of ℓ.
-/
lemma at_most_two_classes_of_noncollinear (hA : A ∉ ℓ) (hB : B ∉ ℓ) (hC : C ∉ ℓ)
    (hBneqC : B ≠ C) (hAB: ¬ same_side ℓ A B) (hAC: ¬ same_side ℓ A C)
    (h : ¬ collinear ({A, B, C} : set Ω)) : same_side ℓ B C :=
begin
  --Step 1: First, prove that A is not equal to B and A is not equal to C
  have HAB : A ≠ B,
  {
    intro H,
    rw H at hAB,
    unfold same_side at hAB,
    simp at hAB,
    apply hB,
    exact hAB,
  },
  have HAC : A ≠ C,
  {
    unfold same_side at hAC,
    intro H,
    rw H at hAC,
    simp at hAC,
    apply hC,
    exact hAC,
  },
--Step 1: Done
--Step 2: Prove that there exists a point D that is both on line ℓ and on line AB such that A*D*B
  have HADB: ∃ (D : Ω), D ∈ ℓ ∧ D ∈ line_through A B ∧ A*D*B,
  {
    unfold same_side at hAB,
    simp at hAB,
    by_contra hc,
    apply hAB,
    push_neg at hc,
    ext,
    split,
    {
      intro H,
      exfalso,
      have h1: x ∈ line_through A B,
      {
        cases H with H hxl,
        simp  at H,
        cases H,
          rw H,
          exact line_through_left A B,
        cases H,
          rw H,
          exact line_through_right A B,
        rw ← collinear_iff_on_line_through HAB,
        have H1:= collinear_of_between H,
        cases H1 with r hr,
        use r,
        simp,
        tauto,
      },
      specialize hc x H.2,
      finish,
    },
    tauto,
    },
    -- D POINT CREATED
  -- Repeat the same process for another point E that should lie on line ℓ and line AC
  have HAEC: ∃ (E : Ω), E ∈ ℓ ∧ E ∈ line_through A C ∧ A*E*C,
  {
    unfold same_side at hAC,
    simp at hAC,
    by_contra hc,
    apply hAC,
    push_neg at hc,
    ext,
    split,
    {
      intro H,
      exfalso,
      have h1: x ∈ line_through A C,
      {
        cases H with H hxl,
        simp  at H,
        cases H,
          rw H,
          exact line_through_left A C,
        cases H,
          rw H,
          exact line_through_right A C,
        rw ← collinear_iff_on_line_through HAC,
        have H1:= collinear_of_between H,
        cases H1 with r hr,
        use r,
        simp,
        tauto,
      },
      specialize hc x H.2,
      finish,
    },
    tauto,
    },

  --BOTH E AND D POINTS HAVE BEEN PROVED

  -- WE NEED TO SHOW THAT C IS NOT IN BETWEEN A and B
  -- USE LEMMA (not_on_line_iff_not_collinear) STATING THAT IF POINTS A B C ARE NOT COLLINEAR AND A≠B,  THEY CANNOT BE IN THE SAME LINE
  cases HADB with D r,
  {
    cases r with l1 r1,
    {
      cases r1 with l2 r2,
      {
        --PASCH AXIOM
        --MAKE PASCH A HYPOTHESIS AND THEN SOLVE THE TWO CASES
        have w := pasch (not_on_line_iff_not_collinear HAB h) hA hB hC l1 r2,
        unfold same_side,
        cases w,
        {
        --FIRST PASCH CASE 
          cases w,
          {
              simp,
              ext,
              split,
              {
                intro H,
                exfalso,
                have x1: x ∈ line_through B C,
                {
                    cases H with H hxl,
                    simp at H,
                    cases H,
                      rw H,
                      exact line_through_left B C,
                    cases H,
                      rw H,
                      exact line_through_right B C,
                    rw ← collinear_iff_on_line_through hBneqC,
                    have H1:= collinear_of_between H,
                    cases H1 with r0 hr,
                    use r0,
                    simp,
                    tauto,
                },
                simp at H,
                cases H,
                finish,
              },
              {
                intro H,
                exfalso,
                
                simp at H,
                cases H,
              },
          }, 
        },
        {
          --SECOND PASCH CASE
          simp,
              ext,
              split,
              {
                intro H,
                exfalso,
                have x1: x∈ line_through B C,
                {
                    cases H with H hxl,
                    simp at H,
                    cases H,
                      rw H,
                      exact line_through_left B C,
                    cases H,
                      rw H,
                      exact line_through_right B C,
                    rw ← collinear_iff_on_line_through hBneqC,
                    have H1:= collinear_of_between H,
                    cases H1 with r0 hr,
                    use r0,
                    simp,
                    tauto,
                },
                simp at H,
                cases H,
                finish,
                
                
              },
              {
                intro H,
                exfalso,
                
                simp at H,
                cases H,
              },
          },
        },
      },
    },
  -- BOTH PASCH CASES SOLVED AND PROOF COMPLETED
end
