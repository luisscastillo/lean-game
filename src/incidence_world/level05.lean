import incidence_world.level04 --hide
open IncidencePlane --hide

/-
Using the lemma we have just proved, we can now prove that
a single point never determines a line. That is, that there are
always at least two lines passing through any given point.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma :
There are at least two different lines passing through a given point.
-/
lemma point_exists_two_lines (P : Ω) : ∃ (r s: Line Ω), P ∈ s ∧ P ∈ r ∧ s ≠ r :=
begin
  rcases (point_existence_postulate P) with ⟨Q, R, ⟨hPQ, hPR, hQR,H⟩⟩,
  use line_through P Q,
  use line_through P R,
  split,
  {
    exact line_through_left P R,
  },
  split,
  {
    exact line_through_left P Q,
  },
  {
    exact ne_of_not_share_point (line_through_right P R) H,
  }
















end