import plane_separation_world.hilbertaxioms --hide
open IncidencePlane --hide

/-
# Plane Separation World

## Level 1: a new world of possibilities...

The notion of **plane separation** comes from the fourth axiom of order, which is the Pasch's Axiom. 

**B.4) Pasch's Axiom:** Let A, B, C be three non-collinear points and let ℓ be a line lying in the plane ABC
and not passing through any of the points A, B, C. Then, if the line ℓ passes through a point of the segment A·B, 
it will also pass through either a point of the segment B·C or a point of the segment A·C (but not both).

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
-/

/- Hint : Click here for a hint, in case you get stuck.
... Still bewildered? Click on "View source" (located on the top right
corner of the game screen) to see the solution. 
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/- Lemma :
There...
-/
lemma not_in_line_of_same_side_left (h : same_side ℓ A B) : A ∉ ℓ :=
begin
  by_contradiction h1,
  unfold same_side at h,
  simp at h,
  have h2 : A ∈ pts(A⬝B) ∩ ℓ,
  {
    split;
    simp [h1],
  },
  finish,
end
