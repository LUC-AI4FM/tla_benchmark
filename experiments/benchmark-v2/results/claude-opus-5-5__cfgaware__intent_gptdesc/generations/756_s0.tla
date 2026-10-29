------------------------------- MODULE DieHarder -------------------------------
EXTENDS Naturals

CONSTANTS Jug, Capacity, Goal

ASSUME Capacity \in [Jug -> Nat]
ASSUME Goal \in Nat

JugVal == {"j1", "j2"}

CapacityVal == [j \in JugVal |-> IF j = "j1" THEN 5 ELSE 3]

Min(m, n) == IF m < n THEN m ELSE n

VARIABLE contents

vars == <<contents>>

TypeOK == /\ contents \in [Jug -> Nat]
          /\ \A j \in Jug : contents[j] <= Capacity[j]

Total(f) ==
  LET S[s \in SUBSET Jug] ==
        IF s = {} THEN 0
        ELSE LET j == CHOOSE x \in s : TRUE
             IN f[j] + S[s \ {j}]
  IN S[Jug]

Init == contents = [j \in Jug |-> 0]

FillJug(j) ==
  contents' = [contents EXCEPT ![j] = Capacity[j]]

EmptyJug(j) ==
  contents' = [contents EXCEPT ![j] = 0]

JugToJug(j, k) ==
  LET amount == Min(contents[j], Capacity[k] - contents[k])
  IN contents' = [contents EXCEPT ![j] = @ - amount,
                                  ![k] = @ + amount]

Pour ==
  \E j, k \in Jug : j # k /\ JugToJug(j, k)

Next ==
  \E j \in Jug : \/ FillJug(j)
                 \/ EmptyJug(j)
                 \/ \E k \in Jug \ {j} : JugToJug(j, k)

Spec == Init /\ [][Next]_vars

Safety == \A j \in Jug : contents[j] >= 0 /\ contents[j] <= Capacity[j]

ConservationOnPour ==
  [][Pour => Total(contents') = Total(contents)]_vars

Solved == \E j \in Jug : contents[j] = Goal

NotSolved == ~Solved

SolutionReachable == <>Solved

FairSpec == Spec /\ WF_vars(Next)

=============================================================================