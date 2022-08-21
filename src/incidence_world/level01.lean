import tutorial_world.level18_by_contra --hide
open IncidencePlane --hide

/- Axiom :
existence (Ω : Type) : ∃ P Q R : Ω, P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧ R ∉ (line_through P Q)
-/

/-
# Incidence World

## Level 1: The axioms of incidence.

Just as the roof of a building cannot stand without the bricks that are glued to the floor, 
neither can theorems stand without axioms. In mathematics, we need to set down some starting points 
to build our knowledge, and this is why axioms should join the game. What are axioms? - you will be
wondering... Axioms are unprovable statements which are assumed to be true because of their self-evidence. 
They are served as a premise for further reasoning and arguments, so that we can reach new conclusions from them.

By travelling back in time to 300 B.C., we meet the great mathematician Euclid, who suggested the very 
first postulates of geometry in his well-known book **`Elements`**. Euclidean geometry can be built up from three
separate sets of axioms, each of them adding new independent notions that are needed to define the plane. These sets of axioms 
were proposed by David Hilbert (1862-1943 AD), who made remarkable improvements in the foundations of geometry.
These three sets are called **incidence**, **betweenness** and **congruence** (we might also want to add the **Parallel Axiom**).

When it comes to the first set of axioms, there are up to three axioms of incidence. These are established to define
the primitive notions of **point**, **line** and the relationship between these two concepts, which is called **incidence**. Notice 
that by "incidence" we mean whatever idea that satifies the axioms of incidence. Then, you will be wondering... are the
notions of "point" and "line" referring to whatever object of reality that satisfies the axioms of incidence? Exactly!
Before the axioms of incidence, these notions are **undefined**!

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

Now, notice that **the more axioms there exist, the more difficult it is to create a model that satisfies all of them.** For this reason, 
**the objective of axiomatic geometry is establishing as less axioms as possible to create a specific model that might be beautiful or applicable to reality.**

## The axioms of incidence in Lean.

How do we make the computer understand such complex statements? By using Type Theory, it is possible to define these concepts in Lean! However, 
some of them are such difficult for a computer to comprehend that they must be divided into more than one statement. For example, the first axiom is 
divided into four statements: 

line_through (P Q : Ω) : Line Ω := line_through' P Q

line_through_left (P Q : Ω) : P ∈ (line_through P Q)

line_through_right (P Q : Ω) : Q ∈ (line_through P Q)

incidence {P Q : Ω} {ℓ : Line Ω} : P ≠ Q → P ∈ ℓ → Q ∈ ℓ → ℓ = line_through P Q

Here it comes the second axiom of incidence in Lean: 

line_contains_two_points (ℓ : Line Ω) : ∃ P Q : Ω, P ≠ Q ∧ ℓ = line_through P Q

And, to finish with, the third one appears right below: 

existence (Ω : Type) : ∃ P Q R : Ω, P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧ R ∉ (line_through P Q)

With that being said, let's try to solve the first level of this world together! 

## Let's solve this level together!

Now that we have learned the basic Lean tactics, we are ready to prove our first theorem! 

The goal of this world is to prove the existence of triangles, but we will start showing that there is no line 
that covers the whole plane. That is to say, every line misses at least one point.

To solve this level, we will need to use the third axiom of incidence. For this reason, the theorem statement 
called `existence` has been added to the list of our theorem statements (located at the left-hand side of the game screen).
[**Remember:** Despite being in the Incidence World, we can freely use the theorem statements from the Tutorial World.]

## Step 1: Thinking of a mathematical proof!

To begin with, we are going to understand why we need to start our proof by using the third axiom of incidence. Read the lemma 
of this level and do a drawing of the situation. Can you see that there is a point which is not in the line you have drawed? Now, go above and 
read the first two axioms of incidence. Then, come back here. Have you noticed it? All the points which are considered in the first two axioms 
pass through a line! Meanwhile, if we want to prove our lemma, we need to generate a point which is not in a line! Now, go above and read the 
third axiom of incidence. Because this is the only axiom that considers a point which is not in a line, we must start by using it!

Once we've discovered how to start our proof, let's now define the objects that we are going to use! First, we need three distinct points which 
will be called A, B and C. Then, we need a plane Ω that contains all of them! Now, you may be wondering if we have to define a line as well...
The answer is that we will have to define more than one line in fact, but we won't do this at the beginning of the proof because it's not necessary yet. 
However, you might be asking... why can we not define a line that passes through two of the three points that we have defined and say that the line misses 
one of the points? The answer is simple: that is not what we want. If you read the lemma again, you will see that it considers **every** possible line of the plane. 
Then, if we define a line, we are just proving one case out of all the lines that could exist in a plane!

Because of this reason, **we must divide our proof into different cases**. That is, into different possible lines. Does this mean that we have to consider as many
cases as lines exist in a plane? Absolutely not! If that was the case, we would need infinite lifes to finish that proof! What we need to do, instead, is to
**provide as less cases as possible to prove that the lemma is true**. Then, **how do we know the minimum number of cases that are needed to prove this lemma?** 
The answer to this question is **by knowing the minimum number of dimensions that are needed to satisfy the lemma**. If you try to prove this lemma in non-dimensional
or one-dimensional spaces, you will see that it is not possible. However, in two-dimensional spaces (that is, the plane) it **is** possible to prove it. And because
the minimum number of points to build the plane is three, then we can prove this lemma just by generating three points. 

Now that we have divided the proof into three cases, it's time to talk about each of them. The strategy is to define a unique line for each of the cases so that
exactly one point misses that line. To define the lines, we will make use of the first axiom of incidence, which is the only one that makes it possible when we've
already generated two or more points. Because these cases don't have to follow a specific order, we will just choose an arbitrary order to step through them. In the
first case, we will define a line through the points A and B so that the line misses the point C. In the second one, we will define a line through the points A and C
so that the line misses the point B. In the third one, we will define a line through the points B and C so that the line misses the point A. 

To finish with, draw the situation of these three cases separately. Then, make sure that all of them satisfy the three axioms of incidence and answer the lemma of
this level at the same time. Read this section as many times as necessary to understand it so that you can enjoy the following steps to the maximum!

## Step 2: Writing a mathematical proof in paper!

Before typing any tactic in Lean, writing the mathematical proof in paper first is a synonym of success! In this way, you will have a clear and structured strategy to
face the level you are trying to complete! Now, read the mathematical proof in paper for this lemma and try to grasp every bit of it!

**Claim:** Every line misses at least one point.

**Proof:** 

By the third axiom of incidence, let A, B and C be three non-collinear points that lie on the plane Ω. 

Now, we proceed with the proof by cases.

**Case 1:** By the first axiom of incidence, let ℓ be the line that is incident with the points A and B. Because of the third axiom of incidence, the line ℓ 
in not incident with the point C.

**Case 2:** By the first axiom of incidence, let ℓ be the line that is incident with the points A and C. Because of the third axiom of incidence, the line ℓ 
in not incident with the point B.

**Case 3:** By the first axiom of incidence, let ℓ be the line that is incident with the points B and C. Because of the third axiom of incidence, the line ℓ 
in not incident with the point A.

Hence, we have shown that every line misses at least one point.

## Step 3: Writing a mathematical proof in Lean!

-/

/- Hint : Click here for a hint, in case you get stuck.
This is really a proof `by_cases`, and you will need to come up
with some candidate points...
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma :
Every line misses at least one point.
-/
lemma exists_point_not_in_line (ℓ : Line Ω) : ∃ (P : Ω), P ∉ ℓ :=
begin
  rcases existence Ω with ⟨A, B, C, ⟨hAB, hAC, hBC, h⟩⟩,
  by_cases hA : A ∈ ℓ,
  {
    by_cases hB : B ∈ ℓ,
    {
      use C,
      have ltA := line_through_left A B,
      have ltB := line_through_right A B,
      rw (incidence hAB hA hB),
      exact h,
    },
    {
      use B,
    }
  },
  {
    use A,
  }
  
end
