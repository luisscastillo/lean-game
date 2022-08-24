import plane_separation_world.level01 --hide
open IncidencePlane --hide

/-
# Plane Separation World

## Level 2: another version of the previous level.

If you managed to solve the previous level, then you know how to prove this lemma with flying colours. Use the same structure as Level 1 to complete this 
level by your own. But be careful! Later on, we may need to use them both, so make sure you understand what they mean!
-/

/- Hint : Click here for a hint, in case you get stuck.
... Still bewildered? Click on "View source" (located on the top right
corner of the game screen) to see the solution. 
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/- Lemma :
If the segment P·Q is on the same side of a line ℓ, then Q ∉ ℓ.
-/
lemma not_in_line_of_same_side_right (h : same_side ℓ A B) : B ∉ ℓ :=
begin
  unfold same_side at h,
  simp at h,
  by_contradiction h1,
  have h2 : B ∈ pts(A⬝B) ∩ ℓ,
  {
    split,
    simp [h1],
    simp [h1],
  },
  finish,
end
