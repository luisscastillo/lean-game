import plane_separation_world.level03 --hide
open IncidencePlane --hide

noncomputable theory --hide
open_locale classical --hide

/-
# Plane Separation World

## Level 4: the Pasch's Axiom in action... (final level)

Welcome to the final level of The Euclid Game! This is perhaps the most challenging level with difference. For this reason, you will be provided with
a very rigorous proof in paper. In case you want to see a possible solution to this level, click on "View source" (located on the top right corner of the
game screen). Have fun, and let maths be with you! 

## Next version of The Euclid Game

In the next version of The Euclid Game, it would be nice to extend the Plane Separation World with more levels and add the Congruence World. 

## What's next?

If you liked the game and want to learn more, look <a href="https://github.com/ImperialCollegeLondon/natural_number_game/blob/master/WHATS_NEXT.md"
target="blank">here</a> for more ideas about what to do next.

## Step by step proof in paper...

**Claim:** Given three non-collinear points A, B, C and a line ℓ, if A and B are on the same side of 
ℓ and B and C are on the same side of ℓ, then A and C are on the same side of ℓ.

**Proof:**

**(i)** Let us assume that `A ≠ C`. That is, `(A = C) → false`. Then, let us assume that `A = C`. Now, we want to prove that this is false. 
We know that A, B, C are non-collinear. That is, `collinear {A, C, B} → false`. Then, it suffices to prove that A, B, C are collinear points.
Because `A = C`, then `collinear {A, C, B} = collinear {C, C, B}`. For this reason, there has to exist a line ℓ and a point P, such that `P ∈ {C, C, B} → P ∈ ℓ`.
Let the line ℓ be the line through B and C. Then, `P ∈ line_through B C`. Because `P ∈ {C, C, B}`, then either P = C or P = B. If P = C, then 
`(P ∈ line_through B C) = (C ∈ line_through B C)`. By the first axiom of incidence (`line_through_right`), we prove that `C ∈ line_through B C`. 
If P = B, then `(P ∈ line_through B C) = (B ∈ line_through B C)`. By the first axiom of incidence (`line_through_left`), we prove that `B ∈ line_through B C`.
Therefore, because we have shown that that A, B, C are collinear points and this is as false as the fact that `A = C`, then we prove that A ≠ C.  

Let us assume that A and B are on the same side of ℓ and that B and C are on the same side of ℓ. Then, we have to prove that A and C are on the same side of ℓ.
Now, we proceed with the proof by contradiction. That is, let us assume that the intersection of the segment `A·C` with the line ℓ is not empty. 

**(ii)** Let us assume that there exists a point D, such that `D ∈ pts (A⬝C) ∧ D ∈ ℓ`. Then, either `D = A` or `A*D*C` or `D = C`, and `D ∈ ℓ`. Now, we proceed with 
the proof of (ii) by contradiction. If there does not exist such point D, we have to prove that the intersection of the segment `A·C` with the line ℓ is empty, and `D ∉ ℓ`.
That is, there exists a point X such that `x ∈ pts (A⬝C) ∩ ↑ℓ ↔ x ∈ ∅`. Now we have to prove that `x ∈ pts (A⬝C) ∩ ↑ℓ → x ∈ ∅` and that `x ∈ ∅ → x ∈ pts (A⬝C) ∩ ↑ℓ`.

**(ii.A)** **Claim**: `x ∈ pts (A⬝C) ∩ ↑ℓ → x ∈ ∅`. **Proof:** Let us assume that `x ∈ pts (A⬝C) ∩ ↑ℓ`. Then, we have to prove that `x ∈ ∅`. That is, 
`x ∈ U → false`, where `U` is the `universal set`. Because of this reason, we assume that `x ∈ U` is true and that it suffices to prove `false`. At this point,
let the point D that we assumed at (ii) be `x`, such that `x = A` or `A*x*C` or `x = C`, and `x ∉ ℓ`. If we assume that `A*x*C`, the `finish` tactic will close the goal.
Because the fact that `A*x*C` implies that `x ∈ ℓ`, then we reach a contradiction with `x ∈ ∅`. Therefore, the first case is proved. 

**(ii.B)** **Claim:** `x ∈ ∅ → x ∈ pts (A⬝C) ∩ ↑ℓ`. **Proof:** Note that the point `x` being an element of the empty set cannot imply that `x` is an element of 
the intersection between the segment `A·C` and the line ℓ, since this is not an empty set. Then, propositional logic proves this case. (You can use the `tauto` tactic
to solve it in Lean.)

Therefore, we have proved that there exists a point D such that D is an element of the segment `A·C` and that `D ∈ ℓ`. 

**(iii)** Let us assume that `A ∉ ℓ ∧ B ∉ ℓ ∧ C ∉ ℓ`. By the lemma `not_in_line_of_same_side_left`, since the points A and B are on the same side of ℓ, then `A ∉ ℓ`.
By the lemma `not_in_line_of_same_side_right`, since the points A and B are on the same side of ℓ, then `B ∉ ℓ`. By the lemma `not_in_line_of_same_side_right`, since 
the points B and C are on the same side of ℓ, then `C ∉ ℓ`. Hence, we have shown that `A ∉ ℓ ∧ B ∉ ℓ ∧ C ∉ ℓ`. 



-/



variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/- Lemma :
Given three non-collinear points A, B, C and a line ℓ, if A and B are on the same side of 
ℓ and B and C are on the same side of ℓ, then A and C are on the same side of ℓ.
-/
lemma same_side_trans_of_noncollinear (hCol : ¬ collinear ({A, C, B} : set Ω)):
    same_side ℓ A B → same_side ℓ B C → same_side ℓ A C :=
begin
  have hAC : A ≠ C,
  {
    intro h,
    apply hCol,
    rw h,
    use line_through B C,
    simp, 
  },
-- Suppose l meets A·C (proving by contradiction)
-- By Pasch l meets A·B or l meets B·C
    -- If l meeets A·B then A, B on different sides
    -- IF l meets B·C then B, C on different sides 
  intros p q,
  by_contradiction,
  unfold same_side at h,
  have h' : ∃ D , D ∈ pts (A⬝C) ∧ D ∈ ℓ,
  {
    simp,
    by_contra h',
    push_neg at h',
    apply h,
    ext,
    split,
    {
      intro h'',
      simp,
      specialize h' x,
      have h''' : A*x*C,
      {
        finish,
      },
      apply h',
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
},

cases h' with P r,
have c : A ∉ ℓ ∧ B ∉ ℓ ∧ C ∉ ℓ,
{
  repeat {split},
  apply not_in_line_of_same_side_left p,
  apply not_in_line_of_same_side_right p,
  apply not_in_line_of_same_side_right q,
},
simp at r,
have x : A*P*C,
{
  have hPA : P ≠ A,
  {
    intro hc,
    apply c.1,
    rw hc at r,
    exact r.2,
  },
  have hPA : P ≠ C,
  {
    intro hcon,
    apply c.2.2,
    rw hcon at r,
    exact r.2,
  },
  tauto,
},
have a1 : B ∉ line_through A C,
{
  rw ← collinear_iff_on_line_through hAC,
  exact hCol,
},

have fact := pasch a1 c.1 c.2.2 c.2.1 r.2 x,
cases fact,
{
unfold same_side at p,
cases fact.1 with E,
simp [set.eq_empty_iff_forall_not_mem] at p,
replace p := p.2.2 E h_1.2,
apply p,
exact h_1.1,
},
unfold same_side at q,
cases fact.1 with F,
simp [set.eq_empty_iff_forall_not_mem] at q,
rw between_symmetric at h_1,
replace q := q.2.2 F h_1.2,
apply q,
exact h_1.1,
end

