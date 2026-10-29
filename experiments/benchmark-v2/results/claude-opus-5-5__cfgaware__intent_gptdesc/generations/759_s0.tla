---- MODULE DieHarder ----
EXTENDS Naturals

Jug == {"j1", "j2"}

Capacity == [j \in Jug |-> IF j = "j1" THEN 3 ELSE 5]

Goal == 4

ASSUME /\ \A j \in Jug : Capacity[j] \in Nat \ {0}
       /\ Goal \in Nat

Min(m, n) == IF m < n THEN m ELSE n

VARIABLE contents

vars == <<contents>>

TypeOK == contents \in [Jug -> Nat] /\ \A j \in Jug : contents[j] <= Capacity[j]

Init == contents = [j \in Jug |-> 0]

FillJug(j) == contents' = [contents EXCEPT ![j] = Capacity[j]]

EmptyJug(j) == contents' = [contents EXCEPT ![j] = 0]

JugToJug(j, k) ==
    LET amountPoured == Min(contents[j], Capacity[k] - contents[k])
    IN  contents' = [contents EXCEPT ![j] = @ - amountPoured,
                                     ![k] = @ + amountPoured]

Next == \E j \in Jug : \/ FillJug(j)
                       \/ EmptyJug(j)
                       \/ \E k \in Jug \ {j} : JugToJug(j, k)

Spec == Init /\ [][Next]_vars

\* Violated exactly when a state with some jug holding Goal is reachable;
\* the counterexample trace (shortest under BFS) is a solution sequence.
NotSolved == \A j \in Jug : contents[j] # Goal

Solved == \E j \in Jug : contents[j] = Goal

THEOREM Spec => []TypeOK
====