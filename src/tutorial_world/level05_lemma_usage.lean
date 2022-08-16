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

## The axioms of incidence.

Just as the roof of a building cannot stand without the bricks that are glued to the floor, 
neither can theorems stand without axioms. In mathematics, we need to set down some starting points 
to build our knowledge, and this is why axioms should join the game. What are axioms? - you will be
wondering... Axioms are unprovable statements which are assumed to be true because of their self-evidence. 
They are served as a premise for further reasoning and arguments, so that we can reach new conclusions from them.

By travelling back in time to 300 B.C., we meet the great mathematician Euclid, who formalized the very 
first axioms of geometry in his well-known book *`The Elements`*. Euclidean geometry can be built up from three
separate blocks of axioms, each of them adding new independent notions that are needed to define the plane. 
These three blocks are called *`incidence`*, *`betweenness`* and *`congruence`* (we might also want to add the *`Parallel Axiom`*).

Inside the first block of axioms, there are up to three *`axioms of incidence`*. These are established to define
the notions of *`point`*, *`line`* and the relationship between these two concepts, which is called *`incidence`*. Notice 
that by "incidence" we mean whatever idea that satifies the *`axioms of incidence`*. Then, you will be wondering... are the
notions of "point" and "line" referring to whatever object of reality that satisfies the *`axioms of incidence`*? Exactly! 

In fact, if we want to verify the consistency and independency of these axioms from one another, we need to create something 
called a *`model`*. A model consists of assigning the concepts of point and line to whatever object of reality we would like to imagine.
As long as all the *`axioms of incidence`* are satisfied by this model, we can then ensure that this system of axioms is consistent. 
Let's introduce the axioms of incidence so that we can create a model that satisfies them!

*A.1)* For every point P and for every point Q not equal to P, there exists a unique line ℓ "passing through" (=incident with) P and Q.

*A.2)* For every line ℓ, there exist two distinct points that "pass through" (=are incident with) it.  

*A.3)* There exist three distinct points with the property that no line "passes through" (=is incident with) all three of them.

It might be useful for you to do a drawing in order to understand each of the axioms more clearly, but remember that mathematics
does not understand drawings but logical relationships to build new knowledge!

Let's make a model! For example, say that we have three distinct needles and thread. (Note: we must specify how many objects of each type
we have in order to be as rigorous as axioms are.) Then, we can define these three distinct needles as three distinct points and thread as the line ℓ.
Now, we have to check if this model satisfies the axioms of incidence. If you try by your own, you will realise that the three axioms are being 
satisfied at the same time and without contradicting one another. Then, the axioms of incidence are consistent! 

Now, notice that the more axioms there exist, the more difficult it is to create a model that satisfies all of them. For this reason, the objective 
of axiomatic geometry is establishing as less axioms as possible to create a specific model that might be beautiful or applicable to reality.

## The axioms of incidence in Lean.

How do we make the computer understand such complex statements?

-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma :  no-side-bar
A point lies in the line through it.
-/
lemma point_on_line {A B : Ω} {r : Line Ω} :
B ∈ line_through A B :=
begin
  
  exact line_through_right A B,

end



