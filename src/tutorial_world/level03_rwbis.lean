/-
# Tutorial World 

## The rewrite (`rw`) tactic (II).

In the previous level, we learned that `rw h` changes A's into B's when the goal contains one or more A's 
and we have the hypothesis `h : A = B` in the local context. You may be wondering if the opposite case is 
also possible. That is to say: could we change B's into A's when the goal contains one or more B's and we have 
the hypothesis `h : A = B` in the local context?

So the answer is... Yes! The hypotheses in this level are a bit different than before, 
so you should use *`rw ←`* instead. To do so, you can type the little left-arrow by typing *\l* 
and then a space, so the system will change it automatically.

## Did you know?

On the top right corner of the screen, there is a box named *"View source"* for each level. If you 
click on it, you will see one possible solution to this level. Again, try to use this tool wisely! 

-/

/- Hint : Click here for a hint, in case you get stuck.
You may want to use *`rw ←`* first. Use it only with one of the hypotheses. Then, think if it's necessary to use it again
or you just can finish the proof by using `rw`without `←`.
-/
variables {Ω : Type} -- hide

/- Lemma : no-side-bar
If A, B and C are points with B = A and B = C, then A = C.
-/
lemma example_exact (A B C: Ω) (h1 : B = A) (h2 : B = C) : A = C :=
begin
  rw ← h1,
  rw h2,

  
end

