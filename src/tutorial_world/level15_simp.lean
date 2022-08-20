import tutorial_world.level14_apply --hide
open IncidencePlane --hide

/- Tactic : simp

## Summary
The `simp` tactic is a high-level tactic which tries to prove equalities using facts in its database.

## Details
The `simp` tactic does basic automation. It uses lemmas already proved that have been tagged
with a special label, to simplify either a goal or a hypothesis.

## Example:
For `S` a segment, we have a lemma
`mem_pts : P ∈ S ↔ P = S.A ∨ P = S.B ∨ (S.A * P * S.B)`, and it is tagged as a simp lemma
in this game. This means that the `simp` tactic will replace occurrences of `P ∈ S` with
the right-hand side, which is more concrete.
-/

/-
# Tutorial World

## Level 15: the `simp` tactic.

In this level, we introduce a high level tactic called `simp`. This is an Artificial Intelligence (AI) tactic which 
can nail some really tedious-for-a-human-to-solve goals. It uses lemmas that are already in our database to make 
the goal easier to solve. 

Now, read the lemma and do a drawing of the situation. In this level, we also introduce a geometric concept which may be useful to remember. **A segment 
As a simple example, for `S` being a segment, we have a lemma
`mem_pts : P ∈ S ↔ P = S.A ∨ P = S.B ∨ (S.A * P * S.B)`, and it is tagged as a simp lemma
in this game. This means that the `simp` tactic will replace occurrences of `P ∈ S` with
the right-hand side, which is more concrete. Try it below.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma : no-side-bar
A point in between the endpoints of a segment is in the segment.
-/
lemma simp_example (P : Ω) (S : Segment Ω) (h : S.A * P * S.B) : P ∈ S :=
begin
  simp,
  right,
  right,
  exact h,




end

