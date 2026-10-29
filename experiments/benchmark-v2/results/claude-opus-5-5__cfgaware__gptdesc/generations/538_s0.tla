---- MODULE Squares ----
EXTENDS Naturals

CONSTANT NSet

ASSUME NSet \subseteq Nat

(* --algorithm Squares
variables n \in NSet, x = 0, i = 0;
begin
a: while i < n do
b:   i := i + 1;
     x := x + 2*i - 1;
   end while;
end algorithm *)

VARIABLES n, x, i, pc

vars == << n, x, i, pc >>

Init == /\ n \in NSet
        /\ x = 0
        /\ i = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF i < n
           THEN /\ pc' = "b"
           ELSE /\ pc' = "Done"
     /\ UNCHANGED << n, x, i >>

b == /\ pc = "b"
     /\ i' = i + 1
     /\ x' = x + 2*i' - 1
     /\ pc' = "a"
     /\ n' = n

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

====