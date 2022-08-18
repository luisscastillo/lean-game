import tutorial_world.level11_cases2_or --hide
open set IncidencePlane --hide

variables {Ω : Type} [IncidencePlane Ω] --hide

/-
# Tutorial World 

## Level 12: the `cases` tactic (III) (boss level).

Suppose now that your hypothesis says there is some element `x` satisfying a certain
property `P`. That is, you have `h : ∃ x, P x`. Then `cases h with z hz` will
replace `h` with `z : x` and `hz : P z`. That is, from the fact that you assume that
some `z` exists (`z : x`), it will give you another hypothesis in which `z` satisfies the 
property `P` (`hz : P z`).

Let's try to understand this with a real life example! Say that we have the hypothesis 
`h: ∃ CAR, FOUR_WHEELS CAR`. That is, **there exists a CAR such that "FOUR_WHEELS" is an 
element of the CAR**. Then, `cases h with FERRARI hFERRARI` will break `h` into two goals:
`FERRARI : CAR`, which is read as **the term "FERRARI" is an element of the type "CAR"**, and
`hFERRARI: FOUR_WHEELS FERRARI, which is read as **the hypothesis hFERRARI assumes that "FOUR_WHEELS"
is an element of the "FERRARI"**. Is it better for you now? [**Tip:** Whenever you don't
understand an abstract concept, try to apply a real life example to it.]

Now, let's try to solve this level! From now on, it will be better if we start by reading the lemma 
as many times as we need to understand it. Then, do a drawing of the situation. In this way, we can
think of a clearer path to close the goal. Once you feel ready, delete the `sorry` and take a look 
to the hypothesis h1 and h2. As you may be thinking, we can apply the `cases` tactic to them. Following
the guiding thread of the real life example, we need to think about a specific line for each of them. 
In geometry, lines are usually represented by the letters `r` and `s`. Then, type `cases h1 with r hr,`, 
click on enter, and write `cases h2 with s hs,`. If you look at the local context, you'll see that we've
assumed that `r` and `s`are lines in the plane Ω. 

Right after, it comes the genius idea. After reading the lemmma and trying to do a draw that represents
the situation, you should be wondering if we could create a hypothesis to state that the lines we've just
added to the local context are the same (`r = s`). Do you remember how we could add a hypothesis? Exactly, 
the `have` tactic will do it for us! Now, type `have H : r = s,`.  

Subsequently, we will have to prove two goals. First, try to look for a theorem statement that might help us 
to close the `⊢ r = s` goal. Can you see that `equal_lines_of_contain_two_points` ends with exactly the `r = s`
statement? Then, try to look if we have all the previous implications of this statement in the local context of 
this level. If so, 


-/

/- Lemma : no-side-bar
Given 4 distinct points that pass through a line, then the line also passes through two different subsets of three points.
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

