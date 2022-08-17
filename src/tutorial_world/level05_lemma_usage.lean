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

Just as the roof of a building cannot stand without the bricks that are glued to the floor, 
neither can theorems stand without axioms. In mathematics, we need to set down some starting points 
to build our knowledge, and this is why axioms should join the game. What are axioms? - you will be
wondering... Axioms are unprovable statements which are assumed to be true because of their self-evidence. 
They are served as a premise for further reasoning and arguments, so that we can reach new conclusions from them.

By travelling back in time to 300 B.C., we meet the great mathematician Euclid, who suggested the very 
first postulates of geometry in his well-known book **`Elements`**. Euclidean geometry can be built up from three
separate sets of axioms, each of them adding new independent notions that are needed to define the plane. These sets of axioms 
were proposed by David Hilbert (1862-1943 AD), who made remarkable improvements in the Foundations of geometry.
These three sets are called **incidence**, **betweenness** and **congruence** (we might also want to add the **Parallel Axiom**).

Inside the first set of axioms, there are up to three axioms of incidence. These are established to define
the notions of **point**, **line** and the relationship between these two concepts, which is called **incidence**. Notice 
that by "incidence" we mean whatever idea that satifies the axioms of incidence. Then, you will be wondering... are the
notions of "point" and "line" referring to whatever object of reality that satisfies the axioms of incidence? Exactly!
Before the axioms of incidence, the notions of point and line are undefined!

In fact, if we want to verify the consistency and independency of these axioms from one another, we need to create something 
called a **model**. A model consists of assigning the concepts that are mentioned in the axioms to whatever objects of reality we would like to imagine.
As long as all the `axioms of incidence` are satisfied by this model, we can then assure that this set of axioms is consistent. 
Let's introduce the axioms of incidence so that we can create a model that satisfies them!

**A.1)** For every point P and for every point Q not equal to P, there exists a unique line ℓ "passing through" (=incident with) P and Q.

**A.2)** For every line ℓ, there exist two distinct points that "pass through" (=are incident with) it.  

**A.3)** There exist three distinct points with the property that no line "passes through" (=is incident with) all three of them.

It might be useful for you to do a drawing in order to understand each of the axioms more clearly, but remember that mathematics
does not understand drawings but logical relationships to build new knowledge!

Let's make a model! For example, say that we have three distinct needles and thread. (**Note:** we must specify how many objects of each type
we have in order to be as rigorous as axioms are.) Then, we can define these three distinct needles as three distinct points and thread as the line ℓ.
Now, we have to check if this model satisfies the axioms of incidence. If you try by your own, you will realise that the three axioms are being 
satisfied at the same time and without contradicting one another. Then, the axioms of incidence are consistent! 

Now, notice that **the more axioms there exist, the more difficult it is to create a model that satisfies all of them.** For this reason, **the objective 
of axiomatic geometry is establishing as less axioms as possible to create a specific model that might be beautiful or applicable to reality.**

## The axioms of incidence in Lean.

How do we make the computer understand such complex statements? By using Type Theory, it is possible to define that concepts in Lean! However, 
some of them are such difficult for a computer to comprehend that they must be divided into more than one statement. For example, the first axiom is 
divided into four statements: 


(line_through' : Point → Point → Line)

(line_through_left' (P Q : Point) : P ∈ (line_through' P Q))

(line_through_right' (P Q : Point) : Q ∈ (line_through' P Q))

(incidence' {P Q : Point} {ℓ : Line} : P ≠ Q → P ∈ ℓ → Q ∈ ℓ → ℓ = line_through' P Q)


In this level, we need two out of that four statements. Click on the top left menu where it says **"Theorem statements"** to discover which two of 
them we are talking about. Delete the `sorry` and see that the goal is ⊢ B ∈ line_through A B. Presumably, the goal shows the same structure as
the statement `line_through_right (P Q : Point) : Q ∈ (line_through P Q)`. [Remember that the points P and Q could be needles!]. Then, we just 
have to write that statement in a different way! -- How do we change the points P and Q for A and B? -- Follow the same structure of the statement
we need to use. Do you remember that the `exact` tactic solved the goal by using a hypothesis of the same structure? Then, because the computer
already knows what `line_through_right (P Q : Point) : Q ∈ (line_through P Q)` means, why don't we type `exact line_through_right A B`? Type that and see 
how it finishes the proof! 
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



