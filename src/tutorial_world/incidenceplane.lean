import tactic
import data.real.basic
import data.set.function

noncomputable theory
open_locale classical
open set function

@[protect_proj]
class subset (A : Type*) (B : out_param $ Type*) :=
(mem : B → A → Prop)

namespace subset
-- The following allows us to use the symbol `∈`
instance {A : Type*} {B : Type*} [subset A B] : has_mem B A := ⟨subset.mem⟩

-- This says that two "subset"s are equivalent (written `≈`, type with \approx) when
-- they have the same points.
instance {A : Type*} {B : Type*} [subset A B] : has_equiv A := ⟨λ X Y, ∀ t, t ∈ X ↔ t ∈ Y⟩
@[simp] lemma equiv_iff {A : Type*} {B : Type*} [subset A B] (X Y : A) : X ≈ Y ↔ ∀ t, t ∈ X ↔ t ∈ Y := iff.rfl

-- A "subset" can always be considered as an actual subset, in Lean this is `set B`
instance {A : Type*} {B : Type*} [subset A B] : has_coe_t A (set B) := ⟨λ x p, p ∈ x⟩

@[simp] lemma mem_pts  {A : Type*} {B : Type*} [subset A B] (a : A) (P : B) : P ∈ (a : set B) ↔ P ∈ a
:= iff.rfl

end subset

@[simp] def pts {A : Type*} {B : Type*} [subset A B] : A → set B := λ a, {x : B | x ∈ a}


notation p `xor` q := (p ∧ ¬ q) ∨ (q ∧ ¬ p)
def xor3 (p q r : Prop) : Prop := (p ∧ ¬ q ∧ ¬ r) ∨ (¬ p ∧ q ∧ ¬ r) ∨ (¬ p ∧ ¬ q ∧ r)

/--
We define an incidence plane as having the undefined terms `Point` and `Line`,
a function `distance` that takes every two points to a real number, and a predicate
`belongs` that relates points and lines.

There are essentially two axioms: existence of two distinct points, and the incidence postulate.
-/
class IncidencePlane (Point : Type*) :=
	(Line : Type*)

	-- Belongs is an undefined concept
  (belongs : Point → Line → Prop)
	(infix `∈`:100 := belongs)

	-- I1 postulate is divided into 4 statements
	(line_through' : Point → Point → Line)
	(line_through_left' (P Q : Point) : P ∈ (line_through' P Q))
	(line_through_right' (P Q : Point) : Q ∈ (line_through' P Q))
	(incidence' {P Q : Point} {ℓ : Line} : P ≠ Q → P ∈ ℓ → Q ∈ ℓ → ℓ = line_through' P Q)

	-- I2 postulate
	(line_contains_two_points' (ℓ : Line) : ∃ P Q : Point, P ≠ Q ∧ ℓ = line_through' P Q)

	-- I3 postulate (existence postulate)
	(existence' : ∃ P Q R : Point, P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧ ¬ R ∈ (line_through' P Q))

	-- Betweenness is an undefined concept
	(between : Point → Point → Point → Prop)
	(notation A `*` B `*` C := between A B C)

	/- Betweenness is symmetric -/
	(between_symmetric' {A B C : Point} : (A * B * C) → (C * B * A))
	/- If A * B * C then the three points are distinct and collinear. -/
	(different_of_between' {A B C : Point} : (A * B * C) → (A ≠ B ∧ A ≠ C ∧ B ≠ C))
	(collinear_of_between' {A B C : Point} : (A * B * C) → ∃ ℓ, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ)

	/- Given two distinct points A, B, there is a third point C such that A * B * C.-/
	(point_on_ray' {A B : Point} (h: A ≠ B) : ∃ C, A * B * C)

	/- Given 3 distinct collinear points A B C, exactly one of them is between the other two.-/
	(between_of_collinear' {A B C : Point} (h: ∃ℓ, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ) : xor3 (A * B * C) ( B * A * C ) (A * C * B))

	/- Pasch -/
	(pasch' {A B C D : Point} {ℓ : Line}
		(hnc: ¬ C ∈ line_through' A B)
		(hnAl: ¬ (A ∈ ℓ)) (hnBl: ¬ B ∈ ℓ) (hnCl: ¬ C ∈ ℓ)
		(hDl: D ∈ ℓ) (hADB: A * D * B) : (∃ E ,  E ∈ ℓ ∧ (A * E * C)) xor (∃ E, E ∈ ℓ ∧ (B * E * C)))

namespace IncidencePlane
variables {Ω Point : Type*} [IncidencePlane Ω] [IncidencePlane Point]

-- From here on, we can use the symbol `∈` for Lines
instance : subset (Line Ω) Ω := {mem := belongs}

notation A `*` B `*` C := IncidencePlane.between A B C


-- Define again everything

-- A1
def line_through (P Q : Ω) : Line Ω := line_through' P Q
@[simp] lemma line_through_left (P Q : Ω) : P ∈ (line_through P Q) := line_through_left' P Q
@[simp] lemma line_through_right (P Q : Ω) : Q ∈ (line_through P Q) := line_through_right' P Q
lemma incidence {P Q : Ω} {ℓ : Line Ω} : P ≠ Q → P ∈ ℓ → Q ∈ ℓ → ℓ = line_through P Q
:= incidence'

-- A2
lemma line_contains_two_points (ℓ : Line Ω) : ∃ P Q : Ω, P ≠ Q ∧ ℓ = line_through P Q
:= line_contains_two_points' ℓ

-- A3
lemma existence (Ω : Type*) [IncidencePlane Ω] : ∃ P Q R : Ω, P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧
R ∉ (line_through P Q) := existence'



lemma between_symmetric {A B C : Ω} : (A * B * C) → (C * B * A)  := between_symmetric'
lemma different_of_between {A B C : Ω} : (A * B * C) → (A ≠ B ∧ A ≠ C ∧ B ≠ C) := different_of_between'
lemma collinear_of_between {A B C : Ω} : (A * B * C) → ∃ ℓ : Line Ω, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ := collinear_of_between'
lemma point_on_ray {A B : Ω} (h: A ≠ B) : ∃ (C : Ω), A * B * C := point_on_ray' h
lemma between_of_collinear {A B C : Ω} (h: ∃(ℓ : Line Ω), A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ) : xor3 (A * B * C) ( B * A * C ) (A * C * B)
:= between_of_collinear' h
lemma pasch {A B C D : Ω} {ℓ : Line Ω} (hnc: ¬ C ∈ line_through A B)
(hnAl: ¬ (A ∈ ℓ)) (hnBl: ¬ B ∈ ℓ) (hnCl: ¬ C ∈ ℓ) (hDl: D ∈ ℓ) (hADB: A * D * B) :
(∃ E ,  E ∈ ℓ ∧ (A * E * C)) xor (∃ E, E ∈ ℓ ∧ (B * E * C)) := pasch' hnc hnAl hnBl hnCl hDl hADB

-- Define collinearity of a set of points to mean that they all lie on some line
def collinear (S : set Ω) : Prop := ∃ (ℓ : Line Ω), ∀ {P : Ω}, P ∈ S → P ∈ ℓ

/--
Two lines intersect if they share a point
-/
def intersect (r s : Line Ω) : Prop := ∃ A, A ∈ r ∧ A ∈ s

/--
Two lines are parallel if they dont intersect (so a line is never parallel to itself)
-/
def parallel (r s : Line Ω) : Prop := ¬ intersect r s

-- Next we introduce the notion of a Segment.


/--
A segment is the giving two points, A and B.
We will use the notation A⬝B to denote the segment denoted by A and B. The segment A⬝B consists
of all the points X such that A * X * B.
-/
structure Segment (Ω : Type*) := 
(A : Ω) (B : Ω)

infix `⬝`:100 := Segment.mk

namespace Segment

-- Declare when P ∈ A⬝B
instance : subset (Segment Ω) Ω := { mem := λ P S, P = S.A ∨ P = S.B ∨ S.A * P * S.B }
@[simp] lemma mem_pts (S : Segment Ω) (P : Ω) : P ∈ S ↔ P = S.A ∨ P = S.B ∨ (S.A * P * S.B) := iff.rfl

end Segment

end IncidencePlane