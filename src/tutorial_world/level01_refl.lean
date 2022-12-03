/- Tactic : refl

## Summary

`refl` is a tactic which proves goals of the form `A = A`.

## Details

The `refl` tactic will close any goal of the form `A = B`
where `A` and `B` are *exactly the same thing*.

### Example:
If it looks like this in the top right hand box:
```
A : Point
⊢ A = A
```

then

`refl,`

will close the goal and solve the level. Don't forget the comma.

-/

/-
# Tutorial World

## The setup

Welcome to the Tutorial World! In this world, you're going to prove some geometric facts by using **`tactics`**. 
These `tactics` are just instructions that make progress in a mathematical proof.
During your proofs, your "goal" (i.e. what you're
supposed to be proving) will be displayed in front of a `⊢` symbol on the top
right hand box, so you will need to use `tactics` to close that goals. Once you close all the goals, the top
right hand box will report "Proof complete!", so that you 
can move on to the next level in the world you're in. 

## The language

The vast majority of mathematical fields are built up from **Set theory**, which is a branch of mathematical logic
that studies sets. In set theory, everything is a set. Even a point can be thought as a set. These sets can contain
elements, which are mathematical objects of any kind: numbers, points, lines, or even other sets. The set with no element 
is the empty set. The problem with set theory, however, is that it does not consider mathematical proofs as sets or elements.
As a consequence, it makes the translation of mathematical propositions into programming languages more difficult.

To avoid this problem, the majority of proof assistants, such as Lean or Coq, use **Type Theory**.
In Type theory, there are `terms` and `types`. A term and its type are written together as `term` : `type`, 
where the symbol : can be thought as "is an element of" (this is an analogy with set theory). 
Then, if we find the expression Ω : Type , we should understand that Ω is a term of the type "Type". 
Analogously, A : Ω  will translate into "A is a term of the type Ω", which makes us think that terms can also be types.
In this case, because we are talking about geometry, Ω must be interpreted as a plane, where A is a point that lies on 
that plane. In addition to all this, there exists `Prop`, which refers to propositions. Each proposition (when interpreted as a type) 
is either empty or has exactly one `term`. In this way, it can be used to introduce mathematical proofs. If we found h : A = B, 
that should be read as "h is a proof of the fact that `A = B`". In Lean, the computer does not care about the content of a proof, 
but if a proposition is either proved or not. This fact is known as **proof irrelevance**, and makes reasoning about dependent types easier
for computers. If you want to learn more about this, we encourage you to look for the **Curry–Howard correspondence** and **Homotopy Type Theory**. 

## Level 1: the `refl` tactic.

Once we've mastered the language...Let's learn some tactics! Let's start with the `refl` tactic. `refl` 
stands for "reflexivity", which is a fancy way of saying that it will prove any goal of the form `A = A`.
It doesn't matter how complicated `A` is, all that matters is that the left hand side is *exactly equal* 
to the right hand side. 

Each level in this game involves proving a theorem or a lemma (a lemma is just a baby theorem).
At the bottom of the text in this box, there's a lemma, which says that if $A$ is a point, then $A$ = $A$. 
Locate this lemma (if you can't see the lemma and these instructions at the same time, make this box wider
by dragging the sides). Let's supply the proof. Click on the word `sorry` and then delete it.
When the system finishes being busy, you'll be able to see your goal in the box on the top right. 
[If your system never finishes being busy, then your computer is not running the javascript 
Lean which powers everything behind the scenes. Try Chrome? Try not using private browsing?] 

This first level shows a pretty easy goal to prove -- you can just prove it with the `refl` tactic.
Where it used to say `sorry`, write `refl,`
**and don't forget the comma**. Then **hit enter** to go onto the next line.
If all is well, Lean should tell you "Proof complete!" in the top right box, and there
should be no errors in the bottom right box. You just did the first
level of the tutorial! And you also learnt how to avoid by *far* the most
common mistake that beginner users make -- **every line must end with a comma**. 
At the end, the comma is important because it tells Lean you are done with one step of your proof!

For each level, the idea is to get Lean into this state: with the top right
box saying "Proof complete!" and the bottom right box empty (i.e. with no errors in).
If you want to be reminded about the `refl` tactic, you can click on the "Tactics" drop
down menu on the left. Resize the window if it's too small. 
Now click on "Next Level" in the top right of your browser to go onto the second level of
Tutorial World, where we'll learn about the `rw` tactic.
-/

variables {Ω : Type} -- hide

/- Lemma : no-side-bar
If A is a point, then A = A.
-/
lemma refl_example (A : Ω) : A = A :=
begin
  refl,
end
