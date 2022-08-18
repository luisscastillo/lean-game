import tutorial_world.level06_intro --hide
open IncidencePlane --hide

/- Tactic : split

## Summary:

If the goal is `P ∧ Q` or `P ↔ Q` then `split` will break it into two goals.

## Details

If `P Q : Prop` and the goal is `⊢ P ∧ Q`, then `split` will change it into
two goals, namely `⊢ P` and `⊢ Q`. 

If `P Q : Prop` and the goal is `⊢ P ↔ Q`, then `split` will change it into
two goals, namely `⊢ P → Q` and `⊢ Q → P`.  

## Example:

If your local context (the top right window) looks like this
```
X : Type
A B : set X
x : X
⊢ x ∈ A ↔ x ∈ B
```

then after

`split,`

it will look like this:

```
2 goals
X : Type
A B : set X
x : X
⊢ x ∈ A → x ∈ B


X : Type
A B : set X
x : X
⊢ x ∈ B → x ∈ A
```
-/

/-
# Tutorial World

## Level 7: The `split` tactic.

In this level we will learn the `split` tactic. It breaks a goal of the type `P ∧ Q` into two goals (proving `P`, and then proving `Q`),
and also breaks goals of the form `P ↔ Q` into proving each of the implications separately. That is to say, it asks us to prove `P → Q` first, and 
then `Q → P`. In mathematics and logic, the **∧** symbol is read as **and**. For example, `IT RAINS ∧ I AM IN THE STREET → I OPEN THE UMBRELLA`. 
Analogously, the **`↔`** symbol refers to a **double implication**, or an **if and only if** statement. In written mathematics, you could also
find the **`↔`** symbol written as **iff**. 

Because you are supposed to be making process, try to solve this level by your own. You can solve it in three lines of code. 
After deleting `sorry` and typying `split,`, you will see that this level is remarkably similar to Level 5. Feel free to go back to it! 
[**Remember:** Whenever there are two goals to solve in Lean, you will always have to solve the above goal first, and then the one below.]
-/

/- Hint : Click here for a hint, in case you get stuck.
Delete `sorry` and type `split,` (don't forget the comma!). Directly after, go to the "Theorem statements" box (located on the 
top left of the game screen) and try to find a lemma which could be suitable to solve this level. Still bewildered? Click on "View source"
(located on the top right corner of the game screen) to see the solution. 

-/

variables {Ω : Type} [IncidencePlane Ω] --hide


/- Lemma : no-side-bar
If two lines contain two distinct points, then they are the same line.
-/
lemma line_through_contains_points (P Q : Ω) : P ∈ (line_through P Q) ∧ Q ∈ (line_through P Q)
:=
begin
  split,
  exact line_through_left P Q,
  exact line_through_right P Q,
end

