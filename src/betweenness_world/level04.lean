import betweenness_world.level03 --hide
open IncidencePlane --hide


/-
# Betweenness World

## Level 4: another version of the previous level...

To solve this level, the mathematical proof in paper will be given to you **inside the Hint Box** (right below). 
Remember that you can use theorem statements from previous worlds. Make an effort to write the proof by your own. 
You may find the proof of the previous level very helpful for this one.

-/

/- Hint : Click here for a hint, in case you get stuck.
**Claim:** Given two different collinear points A and B, there is a third C that shares the same line with them and satisfies A * B * C.

**Proof:** Let `r` be the line that is incident with the points A and B.

**(i)** Let us assume that A ≠ B ∧ A ≠ C ∧ B ≠ C. By the first axiom of order `different_of_between`, since A * B * C, then we prove that 
A ≠ B ∧ A ≠ C ∧ B ≠ C.
 
**(ii)** Let us assume that ∃ ℓ, such that A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ. By the first axiom of order `collinear_of_between`, since A * B * C, then 
we prove that ∃ ℓ, such that A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ. Let this line be called `s`. Then, A ∈ s ∧ B ∈ s ∧ C ∈ s.

**(iii)** Let us assume that r = s. By the lemma `equal_lines_of_contain_two_points`, since A ≠ B, A ∈ r, A ∈ s, B ∈ r and B ∈ s, then we prove that
r = s. Because C ∈ s, which we proved in **(ii)**, and r = s, then we prove that C ∈ r. 

Hence, we have shown that given two different collinear points A and B, there is a third C that shares the same line with them and satisfies A * B * C.

Still bewildered? Click on "View source" (located on the top right corner of the game screen) to see the solution.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/- Lemma :
Given two different collinear points A and B, there is a third C that shares the same line with them and satisfies A * B * C.
-/
lemma between_points_share_line_v2 (hAr : A ∈ r) (hBr : B ∈ r) : 
	(A * B * C) → C ∈ r :=
begin
    intro H,
    have h1 : A ≠ B ∧ A ≠ C ∧ B ≠ C,
    {
        exact different_of_between H,
    },
    have h2 : ∃ ℓ, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ,
    { 
        apply collinear_of_between,
        exact H,
    },
    cases h2 with s hs,
    have h3 : r = s,
    {
        exact equal_lines_of_contain_two_points h1.1 hAr hs.1 hBr hs.2.1,
    },
    rw h3,
    exact hs.2.2,
	
end
