---- MODULE RecursiveInvariant ----
EXTENDS Integers

(*
A small demo of recursive operator definitions and their use in invariants.
We define a Fibonacci-like recursive operator Seq over a finite domain D,
build the corresponding set of produced values, and specify a trivial
stuttering system whose single state variable x is initialized to one of
those values and never changes. The invariant asserts that x is always a
value produced by Seq over D.
*)

(*
Finite domain for the recursive operator's argument.
*)
N == 6
D == 0..N

(*
Recursive sequence: Fibonacci with base cases Seq(0)=1, Seq(1)=1.
Only intended to be used with n \in D.
*)
RECURSIVE Seq(_)
Seq(n) ==
  IF n = 0 THEN 1
  ELSE IF n = 1 THEN 1
  ELSE Seq(n - 1) + Seq(n - 2)

(*
Set of values produced by Seq over the finite domain D.
*)
ValueSet == { Seq(n) : n \in D }

VARIABLES x

vars == << x >>

Init == x \in ValueSet

(*
Stuttering-tolerant next-state relation (no state change).
*)
Next == x' = x

Spec == Init /\ [][Next]_vars

(*
Correctness property: the state variable always equals some value
produced by the recursive function.
*)
Inv == \E n \in D : x = Seq(n)

THEOREM Spec => []Inv
PROOF OMITTED

====