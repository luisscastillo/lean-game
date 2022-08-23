import betweenness_world.level03 --hide
open IncidencePlane --hide


/-
# Betweenness World

## Level 4: another version of the previous level...

To solve this level, the mathematical proof in paper will be given to you. Remember that you can use theorem statements from previous worlds.

**Claim:** A point that lies between two different collinear points shares the same line with them.

**Proof:** Let B be the point that lies between A and B, where these two are different collinear points that lie on the line `r`.
**(i)** Let us assume that there exists a line ℓ such that A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ. By the first axiom of order `collinear_of_between`, since A * B * C,  
we prove that there exists a line ℓ such that A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ. Let this line be called `s`. Then, A ∈ s ∧ B ∈ s ∧ C ∈ s.
**(ii)** Let us assume that A ≠ C. By contradiction, if A = C, then A * B * C would be equal to C * B * C. By the lemma `no_point_between_a_point`, this is 
not possible, so we prove that A ≠ C.
**(iii)** Let us assume that r = s. By the lemma `equal_lines_of_contain_two_points`, since A ≠ C, A ∈ r, A ∈ s, C ∈ r and C ∈ s, then we prove that
r = s. Because r = s, then B ∈ s, which we proved in **(i)**, must be equivalent to B ∈ r. Therefore, the point B shares the same line `r` with the points
A and C and satisfies that A * B * C.
Hence, we have shown that a point that lies between two different collinear points shares the same line with them.
-/

/- Hint : Click here for a hint, in case you get stuck.
Whenever we have a hypothesis of the form `h : P ∧ Q ∧ R`, we write `h.1` to refer to `P` and we type `h.2` to refer to `Q ∧ R`. If we want to refer to just 
`Q`, we need to write `h.2.1`. Analogously, if we want to refer to just `R`, then we type `h.2.2`. 
In case you don't know how to use the lemma `no_point_between_a_point`, look how you proved it in the previous level, so that you can adapt that code
for this one.
Still bewildered? Click on "View source" (located on the top right corner of the game screen) to see the solution.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/- Lemma :
A point that lies between two different collinear points shares the same line with them.
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
