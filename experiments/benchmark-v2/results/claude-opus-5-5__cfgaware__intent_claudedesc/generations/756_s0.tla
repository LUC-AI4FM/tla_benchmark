---------------------------- MODULE DieHarder ----------------------------
EXTENDS Naturals

CONSTANTS Jug, Capacity, Goal

ASSUME Capacity \in [Jug -> {n \in Nat : n > 0}]
ASSUME Goal \in Nat

VARIABLE contents

vars == <<contents>>

\* Concrete values for model checking (classic Die Hard instance)
JugVal == {"j1", "j2"}
CapacityVal == [j \in JugVal |-> IF j = "j1" THEN 3 ELSE 5]

Min(m, n) == IF m < n THEN m ELSE n

TypeOK == contents \in [Jug -> Nat]

CapacityOK == \A j \in Jug : contents[j] >= 0 /\ contents[j] <= Capacity[j]

Init == contents = [j \in Jug |-> 0]

FillJug(j) ==
    contents' = [contents EXCEPT ![j] = Capacity[j]]

EmptyJug(j) ==
    contents' = [contents EXCEPT ![j] = 0]

JugToJug(j, k) ==
    LET amountPoured == Min(contents[j], Capacity[k] - contents[k])
    IN  contents' = [contents EXCEPT ![j] = @ - amountPoured,
                                     ![k] = @ + amountPoured]

Next == \E j \in Jug :
          \/ FillJug(j)
          \/ EmptyJug(j)
          \/ \E k \in Jug \ {j} : JugToJug(j, k)

Spec == Init /\ [][Next]_vars

\* Violation of this invariant yields a trace reaching the goal
NotSolved == \A j \in Jug : contents[j] # Goal

=============================================================================