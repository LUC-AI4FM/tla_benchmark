---- MODULE Euclid ----
EXTENDS Integers, TLC

(* --algorithm Euclid
variables x \in 1..10;
begin
  a: assert x ^ 2 <= 100;
end algorithm; *)

VARIABLES x, pc

vars == << x, pc >>

Init == /\ x \in 1..10
        /\ pc = "a"

a == /\ pc = "a"
     /\ Assert(x ^ 2 <= 100,
               "Failure of assertion at line 5, column 6.")
     /\ pc' = "Done"
     /\ x' = x

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

TypeOK == /\ x \in 1..10
          /\ pc \in {"a", "Done"}

AssertionHolds == x ^ 2 <= 100

====