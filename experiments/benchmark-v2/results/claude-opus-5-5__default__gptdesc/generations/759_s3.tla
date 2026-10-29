---------------------------- MODULE DieHarder ----------------------------
(***************************************************************************)
(* Generalized Die Hard water-jug problem.  There is an arbitrary set of   *)
(* jugs, each with a positive integer capacity, and a target amount of     *)
(* water Goal.  A jug may be filled, emptied, or poured into another jug.  *)
(* Pouring stops when the source jug is empty or the destination jug is    *)
(* full.                                                                   *)
(***************************************************************************)
EXTENDS Naturals

Min(m, n) == IF m < n THEN m ELSE n

CONSTANTS Jug,       \* The set of jugs.
          Capacity,  \* A function: Capacity[j] is the capacity of jug j.
          Goal       \* The amount of water we want some jug to hold.

ASSUME /\ Capacity \in [Jug -> {n \in Nat : n > 0}]
       /\ Goal \in Nat

VARIABLE contents    \* contents[j] is the amount of water in jug j.

TypeOK == contents \in [Jug -> Nat]

Init == contents = [j \in Jug |-> 0]

FillJug(j)  == contents' = [contents EXCEPT ![j] = Capacity[j]]

EmptyJug(j) == contents' = [contents EXCEPT ![j] = 0]

JugToJug(j, k) ==
  LET amountPoured == Min(contents[j], Capacity[k] - contents[k])
  IN  contents' = [contents EXCEPT ![j] = @ - amountPoured,
                                   ![k] = @ + amountPoured]

Next ==  \E j \in Jug : \/ FillJug(j)
                        \/ EmptyJug(j)
                        \/ \E k \in Jug \ {j} : JugToJug(j, k)

Spec == Init /\ [][Next]_contents

(***************************************************************************)
(* NotSolved asserts that no jug contains Goal gallons.  Having TLC check  *)
(* NotSolved as an invariant makes it search for a counterexample; the     *)
(* resulting error trace is a solution to the puzzle.                      *)
(***************************************************************************)
NotSolved == \A j \in Jug : contents[j] # Goal
=============================================================================