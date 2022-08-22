import incidence_world.level02--hide
open IncidencePlane --hide

/-
## Incidence World

# Level 3: in search of the extreme cases. 

In axiomatic geometry, when we are given a point, we can't determine where it is. Then, if we need to
generate more points to prove a lemma, it might be the case where one of these points drops exactly where 
the given point was located. Analogously, it might be the case where two of the points generated make a line with 
the given point, or perhaps they don't... Because of this reason, we should think about all the possible
distributions that are needed to satisfy a lemma. Let's learn how to come up with them by solving this level! 

## Step 1: Thinking of a mathematical proof!

To begin with, read the lemma and do a drawing of the situation. To solve this level, we are given a point; call it P. 
Now, try to think of an axiom to set up our proof. If you are not sure about which one to choose, let's step through them one by one. 
It might be the case where some of them cannot be used, thus reducing the number of usable axioms and hence increasing the probability 
of using the ideal one. 

For example, let's say that we want to start our proof with the first axiom of incidence. In this case, we would generate two 
points (A and B) to make a line that passes through them. In case we are lucky, these points won't be dropped exactly where the given point P is spotted.
Then, we would be done because the points A, B and P are not collinear. However, it might be also the case where these three points happened to pass through
the same line. Then, the points A, B and P would be collinear, and this is not what we want. For this reason, the first axiom of incidence is not a good candidate
to set up our proof.

Following the above train of thought, you wil get to the point where the third axiom of incidence is the correct one to choose. Still and all, 
we have to think of all the possible distributions that could arise when having three non-collinear points (A, B and C) and the given point P. 
It might be the case where the point P concurs with one of these three, or it might not... Consequently, we must proceed the proof by cases: one
where P = A (note that it would be the same if P = B or P = C, since P cannot be equal to two of these points at the same time), another one where P ≠ A.

If P = A, then we are done because the points B, C and P are not collinear. Read the lemma and see how this case satisfies it. 

If P ≠ A, it might be the case where P is not incident with any of the lines that passes through A and B, or trough A and C, or through B and C.
However, it might be also the case where P is incident with the line through A and B, **or** with line through A and C, **or** with the line through B and C.
In all of these last three situations, three points would be collinear and only one point which is not P would be non-collinear with it. 
Read the lemma and note that this is not what we want. For this reason, we have to come up with an **auxiliary point** (call it E). 

## Step 2: Writing a mathematical proof in paper!




Using the lemma `point_in_line_not_point` that you proved in the previous
level, we can prove a stronger version of the existence axiom. Remember that
this axiom says that there are three distinct non-collinear points. The
result in this level says that if we fix one point P, then we can find
two other distinct points such that the three of them are non-collinear.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma :
Given a point P, there exist two points Q and R, such that the three points are not collinear.
-/
lemma point_existence_postulate (P : Ω) : ∃ (Q R : Ω), P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧ 
R ∉ (line_through P Q) :=
begin
  rcases existence Ω with ⟨A, B, C, ⟨hAB, hAC, hBC, h⟩⟩,
  by_cases hA : P = A,
  {
    rw hA,
    use B, use C,
    exact ⟨hAB, hAC, hBC, h⟩,
  },
  {
    have htmp := exists_point_not_in_line (line_through' P A),
    cases htmp with D hD,
    use A, use D,
    have hPD := point_in_line_not_point (line_through_left P A) hD,
    have hAD := point_in_line_not_point (line_through_right P A) hD,
    exact ⟨hA, hPD, hAD, hD⟩,
  }










  




  
end
