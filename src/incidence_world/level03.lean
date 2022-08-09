import incidence_world.level02--hide
open IncidencePlane --hide

/-
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
