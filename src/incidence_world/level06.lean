import incidence_world.level05 --hide
open IncidencePlane --hide

/-
We end this world by proving the existence of triangles
using only incidence axioms.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma :
There exist three lines that do not have a point in common.
-/
lemma three_distinct_lines : ∃ (r s t: Line Ω), (∀ (P : Ω),
¬(P ∈ r ∧ P ∈ s ∧ P ∈ t)) :=
begin
  rcases existence Ω with ⟨A, B, C, ⟨hAB, hAC, hBC, h⟩⟩,
  use line_through A B,
  use line_through A C,
  use line_through B C,
  intros P H,
  have h1 : line_through A C ≠ line_through A B, 
  {
    exact ne_of_not_share_point (line_through_right A C) h,
  },
  by_cases hPA : P = A,
  {
    have hAlBC : A ∈ line_through B C,
    {
      rw ← hPA,
      exact H.2.2,
    },
    have H1 : line_through A C = line_through B C,
    {
      exact equal_lines_of_contain_two_points hAC (line_through_left A C) hAlBC (line_through_right A C) (line_through_right B C),
    },
    have H2 : line_through A C = line_through A B, 
    {
      rw H1,
      exact equal_lines_of_contain_two_points hAB hAlBC (line_through_left A B) (line_through_left B C) (line_through_right A B),
    },
    exact h1 H2,
  },
  {
    have h2 : line_through A C = line_through A B, 
    {
      exact equal_lines_of_contain_two_points hPA H.2.1 H.1 (line_through_left A C) (line_through_left A B),
    },
    exact h1 h2,
  }
  















  
  
  
end