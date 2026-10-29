---------------------------- MODULE DieHarder ----------------------------
(***************************************************************************)
(* Generalized Die Hard water-jug problem.  We are given an arbitrary set  *)
(* of jugs, each with a positive integer capacity, and a target amount of *)
(* water Goal.  The goal is to obtain exactly Goal gallons in some jug.    *)
(*                                                                         *)
(* To find a solution, have TLC check the invariant NotSolved.  If the     *)
(* problem is solvable, TLC will report that NotSolved is violated and     *)
(* the error trace it produces is a sequence of steps that solves the      *)
(* problem.                                                                *)
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
(* Pour from jug j into jug k as much water as possible: either until j    *)
(* is empty or until k is full.                                            *)
(***************************************************************************)
JugToJug(j, k) ==
    LET amountPoured == Min(contents[j], Capacity[k] - contents[k])
    IN  contents' = [contents EXCEPT ![j] = @ - amountPoured,
                                     ![k] = @ + amountPoured]

Next == \E j \in Jug :
          \/ FillJug(j)
          \/ EmptyJug(j)
          \/ \E k \in Jug \ {j} : JugToJug(j, k)

Spec == Init /\ [][Next]_contents

(***************************************************************************)
(* NotSolved asserts that no jug contains Goal gallons.  A counterexample  *)
(* to this invariant found by TLC is a solution to the problem.            *)
(***************************************************************************)
NotSolved == \A j \in Jug : contents[j] # Goal

THEOREM Spec => []TypeOK
=============================================================================