---------------------------- MODULE SquareAssert ----------------------------
EXTENDS Integers, TLC

(* --algorithm SquareAssert
variables x \in 1..10;
begin
  A: assert x ^ 2 <= 100;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES x, pc

vars == << x, pc >>

Init == /\ x \in 1..10
        /\ pc = "A"

A == /\ pc = "A"
     /\ Assert(x ^ 2 <= 100,
               "Failure of assertion at line 6, column 6.")
     /\ pc' = "Done"
     /\ x' = x

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

TypeOK == /\ x \in 1..10
          /\ pc \in {"A", "Done"}

SquareBound == x ^ 2 <= 100

=============================================================================