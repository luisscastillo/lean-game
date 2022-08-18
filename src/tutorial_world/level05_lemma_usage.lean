import tutorial_world.incidenceplane --hide
open IncidencePlane --hide

/- Axiom :
line_through_left (P Q : Ω) : P ∈ (line_through P Q)
-/
/- Axiom :
line_through_right (P Q : Ω) : Q ∈ (line_through P Q)
-/

/-
# Tutorial World

## Level 5: The axioms of incidence.

To solve this level, we need to introduce a new section that appears on the left side of the screen, which is called
**Theorem statements**.  Click on the top left menu where it says **"Theorem statements"** and display the **"Tutorial
World"** box to discover what we are talking about. As you can see, two new statements have been added to the list. 

* line_through_left (P Q : Ω) : P ∈ (line_through P Q)

* line_through_right (P Q : Ω) : Q ∈ (line_through P Q)

**Note the name of the two statements**. Mathematicians sometimes call them "Lemma 2.1" or "Hypothesis P6" or something. But
computer scientists call them `line_through_left` and `line_through_right` because they are easier to use and remember. From now on,
all the statements that appear on this list will be remembered by the computer. In this way, we won't have to provide their proofs again.
Instead of this, we will use them straightforwardly in case they are handy for solving the following levels. 

Just after the name of the statements, two parentheses appear. Inside them, there are the exact number of variables that are needed to
put out that statements. Then, the colon **:** symbol introduces the statement as such. In this case, they are very similar to each other.
What they come to mean is that we can draw a line that passes through two distinct points (P and Q) that lie in a plane (Ω). They symbol **∈**
is read as **"is an element of"**. Then, P and Q are elements of the line that passes through the points P and Q. Seems obvious, right? Now, let's 
try to solve this level! 

Delete the `sorry` and watch the goal appear as `⊢ B ∈ line_through A B`. Presumably, the goal shows the same structure as
the statement `line_through_right (P Q : Point) : Q ∈ (line_through P Q)`. Then, we just have to write that statement in a different way! 
-- How do we change the points P and Q for the points A and B? -- Follow the same structure of the statement we need to use. Do you remember that the `exact` 
tactic solved the goal by using a hypothesis of the same structure? Then, because the computer already knows what
`line_through_right (P Q : Point) : Q ∈ (line_through P Q)` means, why don't we type `exact line_through_right A B,`? Type that and see 
how it finishes the proof! [**Don't forget to write the variables A and B. They are needed to use the statement**.]

-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma :  no-side-bar
A point lies in the line that passes through it.
-/
lemma point_on_line {A B : Ω} {r : Line Ω} :
B ∈ line_through A B :=
begin
  
  exact line_through_right A B,

end

