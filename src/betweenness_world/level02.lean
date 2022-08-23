import betweenness_world.level01 --hide
open IncidencePlane --hide


/-
# Betweenness World

## Level 2: don't try to break a point into two pieces...

In this level, we are asked to show that points cannot be splitted. 
-/

/- Hint : Click here for a hint, in case you get stuck.
You can assume that exactly one point is between the other two by typing `have h2 : xor3 (A * B * C) ( B * A * C ) (A * C * B),`. Then, use the theorem
statements commented above to prove that `h2` is true. After that, remember the **rule of thumb** of this level. To finish with, the `tauto` tactic may 
finish the proof. In case you want to see how to avoid the `tauto` tactic, click on "View source" (located on the top right
corner of the game screen).
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/- Lemma :
A point cannot be between a point. 
-/
lemma no_point_between_a_point (A x : Ω) : (A * x * A) ↔ false :=
begin
    split,
    {
        intro h,
        have H := different_of_between h,
        tauto,
    },
    tauto,
