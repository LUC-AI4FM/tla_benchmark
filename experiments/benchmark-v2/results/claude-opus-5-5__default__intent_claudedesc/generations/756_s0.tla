---------------------------- MODULE DieHarder ----------------------------
EXTENDS Naturals

CONSTANTS Jug, Capacity, Goal

ASSUME /\ Capacity \in [Jug -> Nat \ {0}]
       /\ Goal \in Nat

VARIABLE contents

vars == << contents >>

Min(m, n) == IF m < n THEN m ELSE n

TypeOK == contents \in [Jug -> Nat]

CapacityOK == \A j \in Jug : 0 <= contents[j] /\ contents[j] <= Capacity[j]

Init == contents = [j \in Jug |-> 0]

FillJug(j) ==
    contents' = [contents EXCEPT ![j] = Capacity[j]]

EmptyJug(j) ==
    contents' = [contents EXCEPT ![j] = 0]

JugToJug(j, k) ==
    LET amountPoured == Min(contents[j], Capacity[k] - contents[k])
    IN  contents' = [contents EXCEPT ![j] = @ - amountPoured,
                                     ![k] = @ + amountPoured]

Next ==
    \E j \in Jug :
        \/ FillJug(j)
        \/ EmptyJug(j)
        \/ \E k \in Jug \ {j} : JugToJug(j, k)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Water conservation for pour operations: total of the two jugs unchanged *)
PourConservesWater ==
    [][\A j \in Jug : \A k \in Jug \ {j} :
          JugToJug(j, k) => (contents'[j] + contents'[k] = contents[j] + contents[k])
      ]_vars

(* Goal predicate: some jug contains exactly Goal units of water *)
Solved == \E j \in Jug : contents[j] = Goal

(* Check this invariant with TLC: a violation yields a trace that solves
   the puzzle; if it holds, no sequence of actions achieves the goal. *)
NotSolved == ~Solved

(* Possibility of reaching the goal (expressed as a temporal property whose
   violation demonstrates unreachability under the given fairness). *)
FairSpec == Spec /\ WF_vars(Next)

=============================================================================