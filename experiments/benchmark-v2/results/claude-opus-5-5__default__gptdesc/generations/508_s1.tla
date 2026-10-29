---- MODULE SquareAssert ----
EXTENDS Integers, TLC

(* --algorithm SquareAssert
variable x \in 1..10;
begin
  A:
    assert x ^ 2 <= 100;
end algorithm; *)

VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x \in 1..10
        /\ pc = "A"

A == /\ pc = "A"
     /\ Assert(x ^ 2 <= 100, 
               "Failure of assertion at line 6, column 5.")
     /\ pc' = "Done"
     /\ x' = x

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

====