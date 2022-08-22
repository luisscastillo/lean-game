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

Now, read the mathematical proof in paper for this lemma and try to grasp every bit of it! You will see that we are using two Lean theorem statements!

**Claim:** Given a point P, there exist two points Q and R, such that the three points are not collinear.

**Proof:** 

By the third axiom of incidence, let A, B and C be three non-collinear points that lie on the plane Ω. 

Now, we proceed with the proof by cases.

**Case 1:** Let P = A. By the third axiom of incidence, we prove that the points P, B and C are not collinear.

**Case 2:** Let P ≠ A. By the first axiom of incidence, let ℓ be the line that is incident with the points A and P.
By the lemma `exists_not_point_in_line`, there exists a point that is not incident with the line ℓ. Let E be that point. 
By the lemma `point_in_line_not_point`, since the point E is not incident with the line ℓ, then P ≠ E and A ≠ E. By the 
third axiom of incidence, we prove that the points P, A and E are not collinear.

Hence, we have shown that, given a point P, there exist two points Q and R, such that the three points are not collinear.

## Step 3: Writing a mathematical proof in Lean!

To begin with, we generate three non-collinear points A, B and C in the plane Ω by using the following theorem statement:

`existence (Ω : Type) : ∃ P Q R : Ω, P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧ R ∉ (line_through P Q)`

To do so, delete the `sorry` and type `rcases existence Ω with ⟨A, B, C, ⟨hAB, hAC, hBC, h⟩⟩,` where Ω is the plane, A, B and C are the points that lie on 
that plane and `hAB`, `hAC`, `hBC` and `h` are the hypotheses `A ≠ B`, `A ≠ C`, `B ≠ C` and `C ∉ (line_through A B)`, respectively.

Then, we proceed with the proof by cases. First, we type `by_cases h : P = A,`. This will break the proof into two cases. On the one hand, the one where the 
point P is equal to A. On the other hand, the one where the point P is not equal to A. [**Recommendation:** Write curly braces to structure the proof. See level
9 of Tutorial World in case you don't remember how to do it.] Now, try to solve the first case by your own! Then, come back here to prove the second case together!

When it comes to the second case, you can add the hypothesis `H : ∃ (E : Ω), E ∉ line_through P A,` by using the `have` tactic. Then, `apply exists_point_not_in_line,` 
will prove your hypothesis, so that you can use it to prove this second case. Right after, `cases H with E hE` will generate the point E. By typing `use A, use E,` we
tell the computer which points are non-collinear with P. Now, `split` the goal. Remember that `¬ P = A` is equivalent to `P ≠ A`. To finish with, you will have to prove
that P ≠ E and A ≠ E. Remember that the lemma `point_in_line_not_point` states that `P ∈ r → Q ∉ r → P ≠ Q`. Because your first goal is to prove the conclusion of
the statement, that is, `⊢ P ≠ E`, then you have to provide Lean with the two previous hypotheses. To do so, type `exact point_in_line_not_point (line_through_left P A) hE,`. 
Now, try to finish the remaining goals by your own. In case you get stuck, click right below for a hint.
-/

/- Hint : Click here for a hint, in case you get stuck.
You can close the first case just by using the `split`, `exact` and `rewrite` tactics. To finish the second case, you may have to change `line_through_left P A` into
`line_through_right P A` for the remaining goals. Try to understand why that happens. Still bewildered? Click on "View source" (located on the top right corner of the
game screen) to see the solution. 
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma :
Given a point P, there exist two points Q and R, such that the three points are not collinear.
-/
lemma point_existence_postulate (P : Ω) : ∃ (Q R : Ω), P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧ 
R ∉ (line_through P Q) :=
begin
  rcases ( existence Ω ) with ⟨ A, B, C, ⟨ h1, h2, h3, h4  ⟩ ⟩,
by_cases h : P = A,
 {
  use B,
  use C,
  split,
  rw h,
  exact h1,
  split,
  rw h,
  exact h2,
  split,
  exact h3,
  rw h,
  exact h4,
},
{
   have H : ∃ (E : Ω), E ∉ line_through P A,
   {  
      apply exists_point_not_in_line,
   }, 
   cases H with E hE,
   use A,
   use E,
   split,
   exact h,
   split,
   exact point_in_line_not_point (line_through_left P A) hE,
   split,
   exact point_in_line_not_point (line_through_right P A) hE,
   exact hE,
   
},

end
