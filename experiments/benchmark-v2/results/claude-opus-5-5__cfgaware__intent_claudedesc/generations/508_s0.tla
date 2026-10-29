---- MODULE SquareAssert ----
EXTENDS Integers, TLC

(* --algorithm SquareAssert
variables x \in 1..10;
begin
  A:
    assert x * x <= 100;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES x, pc

vars == << x, pc >>

Init == /\ x \in 1..10
        /\ pc = "A"

A == /\ pc = "A"
     /\ Assert(x * x <= 100, "Failure of assertion at line 7, column 5.")
     /\ pc' = "Done"
     /\ x' = x

Terminating == pc = "Done" /\ UNCHANGED vars

Next == A \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

TypeOK == /\ x \in 1..10
          /\ pc \in {"A", "Done"}

SquareBound == x * x <= 100
====