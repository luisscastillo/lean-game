import incidence_world.level06 --hide
open IncidencePlane --hide

/-
# Betweenness World

## Level 1: The axioms of order

Also called the axioms of betweenness, the axioms of order were formalized by David Hilbert (1862-1943 AD) on the occasion of studying the Euclid's `Elements`.
When it comes to them, there are up to four axioms of order. Their learning involves the definition of **segment**, **betweenness**, **line separation** and
**plane separation**, among others. In written mathematics, the notion of **betweenness** is represented by the **`*`** symbol. Now, take a look to the axioms of order.

**B.1)** If A ∗ B ∗ C, then A, B, C are three distinct points all lying on the same line, and C ∗ B ∗ A.

**B.2)** Given two distinct collinear points A and B, there is a third point C such that A * B * C.

**B.3)** Given 3 distinct collinear points A B C, exactly one of them is between the other two. 

**B.4)** **Pasch Axiom:**
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
lemma not_between_of_between : (A * B * C) → ¬ (B * A * C) :=
begin

  intro h,
  have h' := between_of_collinear (collinear_of_between h),
  unfold xor3 at h',
  tauto,
  
end
