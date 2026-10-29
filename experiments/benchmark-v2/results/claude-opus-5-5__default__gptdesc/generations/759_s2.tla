------------------------------- MODULE DieHarder -------------------------------
(***************************************************************************)
(* Generalized Die Hard water-jug problem.  We are given an arbitrary set  *)
(* of jugs, each with a positive integer capacity, and a target amount     *)
(* of water Goal.  Jugs may be filled from a faucet, emptied onto the      *)
(* ground, or poured into one another until either the source jug is       *)
(* empty or the destination jug is full.                                   *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS Jug,        \* The set of jugs.
          Capacity,   \* A function assigning each jug its capacity.
          Goal        \* The target quantity of water.

ASSUME /\ Capacity \in [Jug -> {n \in Nat : n > 0}]
       /\ Goal \in Nat

Min(m, n) == IF m < n THEN m ELSE n

VARIABLE contents   \* contents[j] is the amount of water in jug j.

TypeOK == contents \in [Jug -> Nat]

Init == contents = [j \in Jug |-> 0]

(***************************************************************************)
(* Fill jug j to its capacity.                                             *)
(***************************************************************************)
FillJug(j) == contents' = [contents EXCEPT ![j] = Capacity[j]]

(***************************************************************************)
(* Empty jug j completely.                                                 *)
(***************************************************************************)
EmptyJug(j) == contents' = [contents EXCEPT ![j] = 0]

(***************************************************************************)
(* Pour as much water as possible from jug j into jug k.                   *)
(***************************************************************************)
JugToJug(j, k) ==
  LET amountPoured == Min(contents[j], Capacity[k] - contents[k])
  IN  contents' = [contents EXCEPT ![j] = @ - amountPoured,
                                   ![k] = @ + amountPoured]

Next == \E j \in Jug : \/ FillJug(j)
                       \/ EmptyJug(j)
                       \/ \E k \in Jug \ {j} : JugToJug(j, k)

Spec == Init /\ [][Next]_contents

(***************************************************************************)
(* NotSolved asserts that no jug contains exactly Goal gallons.  Having    *)
(* TLC check NotSolved as an invariant causes it to report a violation     *)
(* when it reaches a state in which some jug holds Goal; the error trace   *)
(* it produces is then a solution to the problem.                          *)
(***************************************************************************)
NotSolved == \A j \in Jug : contents[j] # Goal

THEOREM Spec => [](TypeOK /\ NotSolved)
=============================================================================