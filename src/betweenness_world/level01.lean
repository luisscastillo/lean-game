import incidence_world.level06 --hide
open IncidencePlane --hide

/-
# Betweenness World

## Level 1: The axioms of order

Also called the axioms of betweenness, the axioms of order were formalized by David Hilbert (1862-1943 AD) on the occasion of studying the Euclid's `Elements`.
When it comes to them, there are up to four axioms of order. Their learning involves the definition of **segment**, **betweenness**, **line separation** and
**plane separation**, among others. In mathematics, the idea of **betweenness** or "being in the middle of two objects" is represented by the **`*`** symbol.
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
