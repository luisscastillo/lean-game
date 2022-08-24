import plane_separation_world.hilbertaxioms --hide
open IncidencePlane --hide

/-
# Plane Separation World

## Level 1: a new world of possibilities...

The notion of **plane separation** comes from the fourth axiom of order, which is the Pasch's Axiom. 

**B.4) Pasch's Axiom:** Let A, B, C be three non-collinear points and let ℓ be a line lying in the plane ABC
and not passing through any of the points A, B, C. Then, if the line ℓ passes through a point of the segment A·B, 
it will also pass through either a point of the segment B·C or a point of the segment A·C (but not both).

In Lean, the Pasch's Axiom may be useful to complete following levels:

* `lemma pasch {A B C D : Ω} {ℓ : Line Ω} (hnc: ¬ C ∈ line_through A B)
(hnAl: ¬ (A ∈ ℓ)) (hnBl: ¬ B ∈ ℓ) (hnCl: ¬ C ∈ ℓ) (hDl: D ∈ ℓ) (hADB: A * D * B) :
(∃ E ,  E ∈ ℓ ∧ (A * E * C)) xor (∃ E, E ∈ ℓ ∧ (B * E * C))`

Thanks to this, we can define what "being on the same side" means. 

**Definition:** Given a line ℓ and the points A and B, such that A, B ∉ ℓ, we say that A and B are on the same side if
the segment A·B does not meet ℓ or A = B.

In Lean, the definition of `same_side` is represented as follows: 

* `def same_side (ℓ : Line Ω) (P Q : Ω) :=  pts (P⬝Q) ∩ ℓ = ∅`

The text `pts (P⬝Q) ∩ ℓ = ∅` can be read as "the intersection (**∩**) of the points in the segment P⬝Q and the line ℓ is an empty set (**∅**)". Therefore, 
P and Q are on the same side of ℓ. 

[**Rule of thumb:** Whenever you see `same_side` in Lean, use the `unfold` tactic. In this way, it will be easier to understand what it means. If it is 
located at the hypothesis `h2`, for example, then `unfold same_side at h2,` will make progress. If it is located at the goal, then `unfold same_side,` will be enough 
to rewrite the goal. This will change `same_side` into a text of the form `pts (P⬝Q) ∩ ℓ = ∅`. Then, you can use the `simp` tactic in the same way to change a text
of the form `pts (P⬝Q) ∩ ℓ = ∅` into `{x : Ω | x = P ∨ x = Q ∨ P*x*Q} ∩ ↑ℓ = ∅`, which may feel more understandable to you.]

## Let Lean put in the donkey work...

Do you remember when we said that Lean can complete some moderately difficult statements on its own?  To solve this level, we are going to learn some AI
`tactics`. Before anything else, read the lemma and try to think of a mathematical proof. Can you see that we can prove it by contradiction? Let's solve this!

To begin with, delete the `sorry` and note that the hypothesis `h` shows the definition of `same_side`. Then, we can type `unfold same_side at h,` to change it
into `h: pts (A⬝B) ∩ ↑ℓ = ∅`. 

Subsequently, we can tell Lean to help us. Type `simp at h,` and see how it now turns into `h: {x : Ω | x = A ∨ x = B ∨ A*x*B} ∩ ↑ℓ = ∅`.

Now it comes the genius idea. Because we know that the segment A·B does not intersect the line ℓ, let us assume the opposite of what we want to
prove. That is, type `by_contradiction h1,` to add the hypothesis `h1 : A ∈ ℓ` and change the goal into `⊢ false`.

Right after, add the hypothesis `A ∈ pts(A⬝B) ∩ ℓ`. That is, assume that the point A is an element of the intersection between the segment A·B and the line ℓ.
To prove it, you will need to type `split,` and type `simp [h1],` twice. What does this mean? The `simp` tactic will look for the lemmas that Lean remembers and
try to close the goal with them. 

To finish with, can you see that the hypothesis that you've just proved (A ∈ pts(A⬝B) ∩ ℓ) contradicts the hypothesis `h : {x : Ω | x = A ∨ x = B ∨ A*x*B} ∩ ↑ℓ = ∅`?
Because of this reason, we can type `finish,` to "finish" the proof. This tactic uses propositional logic and works only when the laws of logic are able to close a goal.
In this case, since the `finish` tactic finds a contradiction between two hypotheses, then it can close the goal and hence finish the proof.

-/

/- Hint : Click here for a hint, in case you get stuck.
... Still bewildered? Click on "View source" (located on the top right
corner of the game screen) to see the solution. 
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/- Lemma :
If the segment P·Q is on the same side of a line ℓ, then P ∉ ℓ.
-/
lemma not_in_line_of_same_side_left (h : same_side ℓ A B) : A ∉ ℓ :=
begin
  unfold same_side at h,
  simp at h,
  by_contradiction h1,
  have h2 : A ∈ pts(A⬝B) ∩ ℓ,
  {
    split,
    simp [h1],
    simp [h1],
  },
  finish,
end
