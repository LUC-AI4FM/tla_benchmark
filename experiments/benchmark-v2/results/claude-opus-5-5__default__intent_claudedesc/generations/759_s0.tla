------------------------------ MODULE DieHarder ------------------------------
EXTENDS Naturals

Min(m, n) == IF m < n THEN m ELSE n

CONSTANTS Jug, Capacity, Goal

ASSUME /\ Capacity \in [Jug -> {n \in Nat : n > 0}]
       /\ Goal \in Nat

VARIABLE contents

vars == << contents >>

TypeOK == contents \in [Jug -> Nat]

CapacityOK == \A j \in Jug : contents[j] <= Capacity[j]

Init == contents = [j \in Jug |-> 0]

FillJug(j)  == contents' = [contents EXCEPT ![j] = Capacity[j]]

EmptyJug(j) == contents' = [contents EXCEPT ![j] = 0]

JugToJug(j, k) ==
  LET amountPoured == Min(contents[j], Capacity[k] - contents[k])
  IN  contents' = [contents EXCEPT ![j] = @ - amountPoured,
                                   ![k] = @ + amountPoured]

Next == \E j \in Jug : \/ FillJug(j)
                       \/ EmptyJug(j)
                       \/ \E k \in Jug \ {j} : JugToJug(j, k)

Spec == Init /\ [][Next]_vars

(* Checking this invariant with TLC yields a counterexample trace that
   solves the puzzle, if a solution exists. *)
NotSolved == \A j \in Jug : contents[j] # Goal

(* The goal state is reachable (checked as a counterexample to NotSolved). *)
GoalReachable == \E j \in Jug : contents[j] = Goal
=============================================================================