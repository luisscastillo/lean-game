import tutorial_world.level07_split --hide
open IncidencePlane --hide
open set --hide

/- Tactic : use

## Summary
The `use` tactic works on the goal that looks like `⊢ ∃ x, P x`, where the symbol **`∃`** is read as **"there exists"** and
**`P x`** can be understood as **"P is an element of x"**, which could also be written as **`P ∈ x`**.
In this case, the whole goal can be interpreted as **"there exists x such that P is an element of x"**.
Then, the `use` tactic is useful. If we know that an object `a` satisfies the  property `x`, then `use a` 
will simplify the goal into ⊢ P a.

## Example
If your goal is `⊢ ∃ n : natural_numbers, 1 + x = x + n` then `use 1` will 
turn the goal into `⊢ 1 + x = x + 1`, and the rather more unwise `use 0` will 
turn it into the impossible-to-prove `⊢ 1 + x = x + 0`.
-/

/-
# Tutorial World

## Level 8: the `use` tactic.

In further proofs, we will need to prove that there exists an object satisfying certain properties.
The goal will then look like `⊢ ∃ x, P x`, where the symbol **`∃`** is read as **"there exists"** and
**`P x`** can be understood as **"P is an element of x"**, which could also be written as **`P ∈ x`**.
In this case, the whole goal can be interpreted as **"there exists x such that P is an element of x"**.
Then, the `use` tactic is useful. If we know that an object `a` satisfies the  property `x`, then `use a` 
will simplify the goal into ⊢ P a.

Let's look at this level to understand it better! Delete the `sorry` to see the goal `⊢ ∃ (ℓ : Line Ω), P ∈ ℓ`.
What does this mean? You can read it as **"there exists a line ℓ that lies in the plane Ω, such that the point
P is an element of the line ℓ"**. [**Tip:** do a drawing if it feels very abstract to you.] Then, we have to 
find an object **?** that satisfies the property `ℓ`, so that we can type `use ?,` to simplify the goal into 
`⊢ P ∈ ?`. Now, we should take a look at our "Theorem statements" section to ask ourselves if there is any statement
that has a similar structure to the goal `⊢ P ∈ ?`. At this point, I am sure that you thought about `line_through_right`
or `line_through_left`. The statement `⊢ P ∈ line_through P Q` is very similar to that in `⊢ P ∈ ?`, isn't it?

Then, why don't we type `use line_through P Q,`. If you try that, you will see that an error appears. This is
because we don't have such point called Q in this level. We only have one point! And it's called P! What does this mean?
Do we have to create a line that goes from the point P to the point P again? Exactly! You may be wondering how is 
that possible if a line cannot close itself as if it was a circle... in the plane! However, it **is** possible. We have not
defined what is a plane yet! The computer doesn't know how a plane looks like! Because of this reason, you can type `use 
line_through P P,` and see how the goal changes into `⊢ P ∈ line_through P P`. Now, try to finish the proof by your own! It's 
only one more line of code! In case you get stuck, click on the grey box right below to look for a "Hint".
 
-/

/- Hint : Click here for a hint, in case you get stuck.
Because the goal is now `⊢ P ∈ line_through P P`, it shows the same structure as `line_through_left` and `line_through_right`
statements. Try any of both to finish the proof by using the `exact` tactic. Remember to type the variables that we are using 
before the comma! Still bewildered? Click on "View source" (located on the top right corner of the game screen) to see the solution. 
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma : no-side-bar
Given a point, there is always a line containing it.
-/
lemma line_containing_point (P : Ω) : ∃ ℓ : Line Ω, P ∈ ℓ :=
begin
  use line_through P P,
  exact line_through_left P P,


end
