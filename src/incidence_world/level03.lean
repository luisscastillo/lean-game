import incidence_world.level01 --hide
open IncidencePlane --hide

/-
# Incidence World

## Level 3: proving useful lemmas (II).

If you look at the list of your theorem statements, you will note that the lemma of the previous level has been added. Despite not
being useful now, it will come handy for next levels. Analogously, the lemma of this level will be added to the list of theorem 
statements, so that the computer can remember it in case you need to use it again.

To solve this level, you just need three lines of code. Try to finish it by your own. Here you have a clue for each of the lines:

**Line 1:** Remember that a goal of the form `⊢ P ≠ Q` can be read as `⊢ (P = Q) → false` as well.

**Line 2:** If you have the hypotheses `h : A = B` and `h2 : A ∈ r`, then `rw h at h2,` will change `h2` into `h2 : B ∈ r`.

**Line 3:** If the current goal is `⊢ false` and you have the hypotheses `h : ¬ P` and `h2 : P`, which contradict each other, then `tauto,`
will make progress.
-/

/- Hint : Click here for a hint, in case you get stuck.
Remember that `¬ P` is the same as `P → false`, so `intro` may get you going. 
Still bewildered? Click on "View source" (located on the top right corner of the game screen) to see the solution. 
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables  {P Q: Ω} {r : Line Ω}  -- hide

/- Lemma :
If a point P is in a line and a point Q is not, then they are different.
-/
lemma point_in_line_not_point (hP : P ∈ r) (hQ : Q ∉ r): P ≠ Q :=
begin

  intro H,
  rw H at hP,
  tauto,

end
