import tutorial_world.level17_by_cases --hide
open set IncidencePlane --hide

/-
This is an extra level you can use for practice.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma :
The only point on the segment A⬝A is A itself.
-/
@[simp] lemma one_point_segment (A B : Ω) : B ∈ A⬝A ↔ B = A :=
begin
  split,
  {
    intro hx,
    cases hx,
    {
      exact hx,
    },
    {
      cases hx,
      {
        exact hx,
      },
      {
        exfalso,
        apply (different_of_between hx).2.1,
        refl,
      }
    }
  },
  {
    intro h,
    rw h,
    left,
    refl,
  },








end