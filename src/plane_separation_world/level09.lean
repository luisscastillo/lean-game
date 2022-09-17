import plane_separation_world.level08 --hide
open IncidencePlane --hide

/-
# Plane Separation World

## Level 9: the Pasch's Axiom in action... (final level)

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

Let us assume that A and B are on the same side of ℓ and that B and C are on the same side of ℓ. Then, we have to prove that A and C are on the same side of ℓ.
Now, we proceed with the proof by contradiction. That is, let us assume that that A and C are on the same side of ℓ.

**(i)** By the lemma `not_same_side_intersection`, since we have assumed that A and C are on the same side of ℓ, then there exists a point P such that
`P ∈ pts (A⬝C) ∧ P ∈ ℓ`. Let that point P be called D. Then, there exists a point D such that `D ∈ pts (A⬝C) ∧ D ∈ ℓ`. That is, `(D = A ∨ D = C ∨ A*D*C) ∧ D ∈ ℓ`.

**(ii)** By the lemma `not_same_side_point_in_between`, since A and B are on the same side of ℓ, B and C are on the same side of ℓ, and `(D = A ∨ D = C ∨ A*D*C) ∧ D ∈ ℓ`,
then D satisfies that `A * D * C`.

**(iii)** By the lemma `noncollinear_ne_line`, since A, B and C are not collinear, then `B ∉ line_through A C`.

**(iv)** By the lemma `same_side_of_noncollinear_ne_line`, since A and B are on the same side of ℓ, and B and C are on the same side of ℓ, then
`A ∉ ℓ ∧ B ∉ ℓ ∧ C ∉ ℓ`.

**(v)** By the Pasch's Axiom, since `A ∉ ℓ ∧ B ∉ ℓ ∧ C ∉ ℓ` (proved in (i)), and `D ∈ ℓ` and `A * D * C` (proved in (ii)), then there exists a point E, such that 
`E ∈ ℓ`, and either E satisfies that `A * E * B` or `C * E * B`. Now, we proceed with (vi) by cases. 

**(v.A)** Let us assume that there exists a point E, such that `E ∈ ℓ` and `A * E * B`. Because `pts (A⬝B) ∩ ↑ℓ = ∅`, the point E has to satisfy that
`A * E * B` and `E ∉ ℓ`. By contradiction with the Pasch's Axiom, there cannot exist a point E such that `A * E * B` and `E ∈ ℓ`.

**(v.B)** Let us assume that there exists a point E, such that `E ∈ ℓ` and `C * E * B`. By the first axiom of order `between_symmetric`, let `C * E * B` be
equivalent to `B * E * C`. Because `pts (B⬝C) ∩ ↑ℓ = ∅`, the point E has to satisfy that `B * E * C` and `E ∉ ℓ`. By contradiction with the Pasch's Axiom, 
there cannot exist a point E such that `B * E * C` and `E ∈ ℓ`.

Because we have shown that there cannot exist a point E such that `E ∈ ℓ` and either `A * E * B` or `B * E * C`, then the segment `A·B` is on the same side of ℓ and
the segment `B·C` is on the same side of ℓ. Therefore, we prove, as a consequence, that the segment `A·C` is on the same side of ℓ.
-/

/- Hint : Click here for a hint, in case you get stuck.
To solve this level, we have used high levels tactics which weren't taught in the Tutorial World. In case you are bewildered, do not hesitate
to click on "View source" (located on the top right corner of the game screen) to see the solution.
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
intros p q,
by_contradiction,
have h' := not_same_side_intersection h,
cases h' with D hPAC,
simp at hPAC,
have x := not_same_side_point_in_between p q hPAC,
have a1 := noncollinear_ne_line hCol,
have c := same_side_of_noncollinear_ne_line p q,
have fact := pasch a1 c.1 c.2.2 c.2.1 hPAC.2 x,
cases fact,
{
  unfold same_side at p,
  cases fact.1 with E,
  simp [set.eq_empty_iff_forall_not_mem] at p,
  replace p := p.2.2 E h_1.2,
  apply p,
  exact h_1.1,
},
{
  unfold same_side at q,
  cases fact.1 with F,
  simp [set.eq_empty_iff_forall_not_mem] at q,
  rw between_symmetric at h_1,
  replace q := q.2.2 F h_1.2,
  apply q,
  exact h_1.1,
},
end
