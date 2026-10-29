---------------------------- MODULE DieHarder ----------------------------
(***************************************************************************)
(* Generalized Die Hard water-jug problem.  We are given a set Jug of     *)
(* jugs, a function Capacity assigning each jug a positive integer        *)
(* capacity, and a target amount Goal.  The single state variable         *)
(* contents maps each jug to the amount of water it currently holds.      *)
(*                                                                         *)
(* To find a solution, have TLC check the invariant NotSolved.  Any       *)
(* violation of NotSolved is a behavior that reaches a state in which     *)
(* some jug contains exactly Goal gallons, and the error trace TLC        *)
(* produces is therefore a solution to the puzzle.                         *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS Jug, Capacity, Goal

ASSUME /\ Capacity \in [Jug -> {n \in Nat : n > 0}]
       /\ Goal \in Nat

VARIABLE contents

Min(m, n) == IF m < n THEN m ELSE n

TypeOK == contents \in [Jug -> Nat]

Init == contents = [j \in Jug |-> 0]

(* Fill jug j to its capacity. *)
FillJug(j) == contents' = [contents EXCEPT ![j] = Capacity[j]]

(* Empty jug j completely. *)
EmptyJug(j) == contents' = [contents EXCEPT ![j] = 0]

(* Pour as much water as possible from jug j into jug k: either j       *)
(* becomes empty or k becomes full, whichever happens first.             *)
JugToJug(j, k) ==
  LET amountPoured == Min(contents[j], Capacity[k] - contents[k])
  IN  contents' = [contents EXCEPT ![j] = @ - amountPoured,
                                   ![k] = @ + amountPoured]

Next == \E j \in Jug : \/ FillJug(j)
                       \/ EmptyJug(j)
                       \/ \E k \in Jug \ {j} : JugToJug(j, k)

Spec == Init /\ [][Next]_contents

(***************************************************************************)
(* NotSolved asserts that no jug contains exactly Goal gallons.  A        *)
(* counterexample found by TLC is a sequence of steps that solves the     *)
(* puzzle.                                                                 *)
(***************************************************************************)
NotSolved == \A j \in Jug : contents[j] # Goal

=============================================================================