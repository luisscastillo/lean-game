import tutorial_world.level11_cases2_or --hide
open set IncidencePlane --hide

variables {Ω : Type} [IncidencePlane Ω] --hide

/-
Suppose now that your hypothesis says there is some element `x` satisfying a certain
property `P`. That is, you have `h : ∃ x, P x`. Then `cases h with x hx` will
replace `h` with `x : X` and `hx : P x`. That is, from the fact that you know that
some `x` exists, it will give you one such `x` with the property that it is supposed
to satisfy.

-/

/- Lemma : no-side-bar
A line through 4 points given lines through two subsets of three
-/
lemma exists_line_example (P Q R S : Ω) (h : Q ≠ R) (h1 : ∃ ℓ : Line Ω, P ∈ ℓ ∧ Q ∈ ℓ ∧ R ∈ ℓ)
(h2 : ∃ ℓ : Line Ω, Q ∈ ℓ ∧ R ∈ ℓ ∧ S ∈ ℓ) :
∃ ℓ : Line Ω, P ∈ ℓ ∧ Q ∈ ℓ ∧ R ∈ ℓ ∧ S ∈ ℓ :=
begin
  cases h1 with r hr,
  cases h2 with s hs,
  have H : r = s,
  {
    exact equal_lines_of_contain_two_points h hr.2.1 hs.1 hr.2.2 hs.2.1,
  },
  use r,
  split,
  exact hr.1,
  split,
  exact hr.2.1,
  split,
  exact hr.2.2,
  rw H,
  exact hs.2.2,
  






end

