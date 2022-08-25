import plane_separation_world.level03 --hide
open IncidencePlane --hide

/- Axiom :
not_on_line_iff_not_collinear (h2 : A ≠ B) (h1: ¬ collinear({A,B,C} : set Ω ))
: C ∉ line_through A B
-/

/-
# Plane Separation World

## Level 4: the Pasch's Axiom in action...

To solve this level, a new theorem statement has been added to the list. It is called `not_on_line_iff_not_collinear`. Take a look at it and

-/

/- Hint : Click here for a hint, in case you get stuck.
... Still bewildered? Click on "View source" (located on the top right
corner of the game screen) to see the solution. 
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
  have HAB: A ≠ B,
  {
    by_contra,
    unfold same_side at hAB,
    rw h at hAB,
    simp at hAB,
    exact hB hAB,
  },
  have HAC: A ≠ C,
  {
    by_contra,
    unfold same_side at hAC,
    rw h at hAC,
    simp at hAC,
    exact hC hAC,
  },
--Step 1: Done
--Step 2: Prove that there exists a point D that is both on line ℓ and on line AB such that A*D*B.
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
    -- Step 2: done
  -- Step 3: Repeat step 2 for another point E that lies on line ℓ and on line AC such that A*E*C.
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
  --Step 3: done.
  -- WE NEED TO SHOW THAT C IS NOT IN BETWEEN A and B
  -- USE LEMMA (not_on_line_iff_not_collinear) STATING THAT IF POINTS A B C ARE NON-COLLINEAR AND A ≠ B, THEY CANNOT BE IN THE SAME LINE.
  cases HADB with D r,
  {
    cases r with l1 r1,
    {
      cases r1 with l2 r2,
      {
        --PASCH AXIOM
        --MAKE PASCH A HYPOTHESIS AND THEN SOLVE THE TWO CASES.
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
        {
          --SECOND PASCH CASE
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
      },
    },
  -- BOTH PASCH CASES SOLVED. PROOF COMPLETED.
end
