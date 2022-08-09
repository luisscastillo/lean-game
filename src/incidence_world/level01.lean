import tutorial_world.level18_practice --hide
open IncidencePlane --hide

/- Axiom :
existence : ∃ P Q R : Ω, P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧ R ∉ (line_through P Q)
-/

/-
Now that we have introduced the basic Lean tactics, 
let's move on to proving our first theorems.

The goal of this world is to prove the existence of
triangles, but we will start showing that there is no line
that covers the whole plane. That is, every line misses
at least one point.
-/

/- Hint : Click here for a hint, in case you get stuck.
This is really a proof `by_cases`, and you will need to come up
with some candidate points...
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma :
Every line misses at least one point.
-/
lemma exists_point_not_in_line (ℓ : Line Ω) : ∃ (P : Ω), P ∉ ℓ :=
begin
  rcases existence Ω with ⟨A, B, C, ⟨hAB, hAC, hBC, h⟩⟩,
  by_cases hA : A ∈ ℓ,
  {
    by_cases hB : B ∈ ℓ,
    {
      use C,
      have ltA := line_through_left A B,
      have ltB := line_through_right A B,
      rw (incidence hAB hA hB),
      exact h,
    },
    {
      use B,
    }
  },
  {
    use A,
  }








  
  
end