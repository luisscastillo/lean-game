import plane_separation_world.level03 --hide
open IncidencePlane --hide

noncomputable theory --hide
open_locale classical --hide

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

