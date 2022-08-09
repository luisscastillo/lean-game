/-
Let's practice a little bit more with the `rw` tactic. The hypotheses in this level are
a bit different than before, so you should use `rw ←` instead. You can
type the little arrow by typing \l, and the system will change it automatically.
-/


variables {Ω : Type} -- hide

/- Lemma : no-side-bar
If A, B and C are points with B = C and B = C, then A = C.
-/
lemma example_exact (A B C: Ω) (h1 : B = A) (h2 : B = C) : A = C :=
begin
  rw ←h1,
  rw h2,

  
end

