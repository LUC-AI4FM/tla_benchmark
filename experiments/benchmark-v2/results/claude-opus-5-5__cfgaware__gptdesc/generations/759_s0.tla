------------------------------ MODULE DieHarder ------------------------------
(***************************************************************************)
(* The generalized Die Hard water-jug problem.  We are given an arbitrary  *)
(* set Jug of jugs, a function Capacity assigning each jug a positive      *)
(* integer capacity, and a natural-number target amount Goal.  The system  *)
(* state is the variable contents, which maps each jug to the amount of    *)
(* water it currently holds.  A step fills a jug, empties a jug, or pours  *)
(* as much water as possible from one jug into another.                    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS Jug, Capacity, Goal

ASSUME /\ Capacity \in [Jug -> {n \in Nat : n > 0}]
       /\ Goal \in Nat

Min(m, n) == IF m < n THEN m ELSE n

VARIABLE contents

TypeOK == contents \in [Jug -> Nat]

Init == contents = [j \in Jug |-> 0]

FillJug(j) == contents' = [contents EXCEPT ![j] = Capacity[j]]

EmptyJug(j) == contents' = [contents EXCEPT ![j] = 0]

(***************************************************************************)
(* Pour from jug j into jug k.  The amount poured is the smaller of the    *)
(* amount in j and the free space remaining in k.                          *)
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
(* NotSolved asserts that no jug contains exactly Goal gallons.  Asking    *)
(* TLC to check NotSolved as an invariant makes it search for a state      *)
(* violating it; the resulting error trace is a solution to the puzzle.   *)
(***************************************************************************)
NotSolved == \A j \in Jug : contents[j] # Goal
=============================================================================