import plane_separation_world.level07 --hide
open IncidencePlane --hide

/-
# Plane Separation World

## Level 8: on the way to the final level (V).

This is the last of the five lemmas that we need to prove before jumping into the final level of the game! You will be provided with 
its mathematical proof in paper right below. Remember that you can use all the theorem statements from the left-hand side box.

## Mathematical proof in paper...

**Claim:** If the segments A·B and B·C are on the same side of the line ℓ, there exists a point P, which satisfies that `(P = A ∨ P = C ∨ A*P*C) ∧ P ∈ ℓ`, 
such that A * P * C. 

**Proof:** 

**(i)** By the lemma `same_side_of_noncollinear_ne_line`, since the segments A·B and B·C are on the same side of ℓ, then `A ∉ ℓ ∧ B ∉ ℓ ∧ C ∉ ℓ`.

Now we proceed with the proof by cases: 

**Case 1:** Let us assume that `P ≠ A`. That is, `(P = A) → false`. Then, let us assume that `P = A`. Now, we want to prove that this is false. In (i) we proved 
that `A ∉ ℓ`. That is, `(A ∈ ℓ) → false`. Because we want to prove `false`, it suffices to prove that `A ∈ ℓ`. Because we assumed that `P = A` and we know 
that `P ∈ ℓ`, then `A ∈ ℓ`. Therefore, we have shown that `P ≠ A`.

**Case 2:** Let us assume that `P ≠ C`. That is, `(P = C) → false`. Then, let us assume that `P = C`. Now, we want to prove that this is false. In (i) we proved 
that `C ∉ ℓ`. That is, `(C ∈ ℓ) → false`. Because we want to prove `false`, it suffices to prove that `C ∈ ℓ`. Because we assumed that `P = C` and we know that `P ∈ ℓ`,
then `C ∈ ℓ`. Therefore, we have shown that `P ≠ C`.

**Case 3:** Let us assume that `A * P * C`. Given that the point P either satisfies `P = A ∨ P = C ∨ A*P*C`, because we proved that `P ≠ A` in Case 1 and 
that `P ≠ C` in Case 2, then P must satisfy that `A * P * C`. [In Lean, the `tauto` tactic should close this case automatically.] 
 
-/

/- Hint : Click here for a hint, in case you get stuck.
If you have a theorem statement called `theorem1`, which shows `x` by using the hypothesis `h : P`, then `have htheorem := theorem1 h` 
will add the hypothesis `htheorem : x` to the local context. In case you feel bewildered, do not hesitate
to click on "View source" (located on the top right corner of the game screen) to see the solution.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/- Lemma :
If the segments A·B and B·C are on the same side of the line ℓ, there exists a point P, which satisfies that `(P = A ∨ P = C ∨ A*P*C) ∧ P ∈ ℓ`, such that A * P * C. 
-/
lemma not_same_side_point_in_between (hlAB : same_side ℓ A B) (hlBC : same_side ℓ B C) (hPAC: (P = A ∨ P = C ∨ A*P*C) ∧ P ∈ ℓ) : A * P * C :=
begin 
  have c := same_side_of_noncollinear_ne_line hlAB hlBC,
  have hPA : P ≠ A,
  {
    intro hc,
    apply c.1,
    rw hc at hPAC,
    exact hPAC.2,
  },
  have hPA : P ≠ C,
  {
    intro hc,
    apply c.2.2,
    rw hc at hPAC,
    exact hPAC.2,
  },
  tauto,
end
