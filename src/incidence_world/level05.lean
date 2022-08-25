import incidence_world.level04 --hide
open IncidencePlane --hide

/-
# Incidence World

## Level 5: proving useful lemmas (III).

Remember that a couple of levels ago we proved that a line could help us deciding that two points were different. Now we will see that
a point can help us deciding that two lines are different.

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
variables {P : Ω} {r s : Line Ω} --hide

/- Lemma :
If two lines `r` and `s` do not share a point, then they are not equal.
-/
lemma ne_of_not_share_point  (hPr : P ∈ r)
(hPs : P ∉ s): r ≠ s:=
begin
  
  intro H,
  rw H at hPr,
  tauto,

end
