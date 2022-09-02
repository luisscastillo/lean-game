import plane_separation_world.level06 --hide
open IncidencePlane --hide

/-
# Plane Separation World

## Level 7: on the way to the final level (IV).

This is the fourth of five lemmas that we need to prove before jumping into the final level of the game! You will be provided with 
its mathematical proof in paper right below. Remember that you can use all the theorem statements from the left-hand side box.

## Mathematical proof in paper...

**Claim:** If two points A and C are not on the same side of the line ℓ, there exists a point in the segment A·C which is incident with the line ℓ. 

**Proof:** 

Let us assume that there exists a point P, such that `P ∈ pts (A⬝C) ∧ P ∈ ℓ`. Then, either `P = A` or `A * P * C` or `P = C`, and `P ∈ ℓ`. Now, we proceed with 
the proof of by contradiction. If there does not exist such point P, we have to prove that the intersection of the segment `A·C` with the line ℓ is empty, and `P ∉ ℓ`.
That is, there exists a point X such that `x ∈ pts (A⬝C) ∩ ↑ℓ ↔ x ∈ ∅`. Then we have to prove (a) `x ∈ pts (A⬝C) ∩ ↑ℓ → x ∈ ∅` and (b) `x ∈ ∅ → x ∈ pts (A⬝C) ∩ ↑ℓ`.

**Proof (a):** Let us assume that `x ∈ pts (A⬝C) ∩ ↑ℓ`. Then, we have to prove that `x ∈ ∅`. That is, 
`x ∈ U → false`, where `U` is the `universal set`. Because of this reason, we assume that `x ∈ U` is true and then it suffices to prove `false`. At this point,
let the point P be `x`, such that `x = A` or `A * x * C` or `x = C`, and `x ∉ ℓ`. If we assume that `A * x * C`, the `finish` tactic will close the goal.
Because the fact that `A * x * C` implies that `x ∈ ℓ`, then we reach a contradiction with `x ∈ ∅`. Therefore, the first case is proved. 

**Proof (b):** Note that the point `x` being an element of the empty set cannot imply that `x` is an element of 
the intersection between the segment `A·C` and the line ℓ, since this is not an empty set. Then, propositional logic proves this case. (You can use the `tauto` tactic
to solve it in Lean.)

Therefore, we have proved that there exists a point P such that P is an element of the segment `A·C` and that `P ∈ ℓ`. 
 
-/

/- Hint : Click here for a hint, in case you get stuck.
To solve this level, we have used high levels tactics which weren't taught in the Tutorial World.. In case you feel bewildered, do not hesitate
to click on "View source" (located on the top right corner of the game screen) to see the solution.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/- Lemma :
If two points A and C are not on the same side of the line ℓ, there exists a point in the segment A·C which is incident with the line ℓ. 
-/
lemma not_same_side_intersection (h : ¬ same_side ℓ A C) : ∃ P , P ∈ pts (A⬝C) ∧ P ∈ ℓ :=
begin
  simp,
  by_contra hlAC,
  push_neg at hlAC,
  apply h,
  unfold same_side,
  ext,
  split,
    {
      intro hx,
      simp,
      specialize hlAC x,
      have hAxC : A*x*C,
      {
        finish,
      },
      apply hlAC,
      {
        tauto,
      },
      {
        finish,
      },  
    },
    {
      tauto,
    },
  
end 
