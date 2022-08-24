import betweenness_world.level04 --hide
open IncidencePlane --hide


/-
# Betweenness World

## Level 5: the definition of segment.

We've already seen how to define some primitive notions from a given set of axioms, such as **point**, **line**, **incidence** or **betweenness**. In
mathematics, we can also define new concepts by combining those that we've learned so far. In this way, the notion of **segment** joins the party.

**Definition:** a point C is in the segment A·B if and only if A * C * B or C = A or C = B.

In Lean, a segment is represented as A·B. When we refer to the point A, it is represented as (A·B).A. When we refer to the point B, it is represented 
as (A·B).B. With that being said, you can try to solve this level by your own. You may want to use the first axiom of order once (`different_of_between`).

In case you get stuck, click right below for a hint.

-/

/- Hint : Click here for a hint, in case you get stuck.

Still bewildered? Click on "View source" (located on the top right corner of the game screen) to see the solution.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/- Lemma :
The only point on the segment A⬝A is A itself.
-/
lemma one_point_segment (A B : Ω) : B ∈ A⬝A ↔ B = A :=
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
