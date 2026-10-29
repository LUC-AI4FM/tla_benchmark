---------------------------- MODULE DieHarder ----------------------------
(***************************************************************************)
(* The generalized Die Hard water-jug problem.  We have an arbitrary set   *)
(* of jugs, each with a positive integer capacity.  Each step fills a jug, *)
(* empties a jug, or pours as much water as possible from one jug into     *)
(* another.  The goal is to get some jug to hold exactly Goal gallons.     *)
(***************************************************************************)
EXTENDS Naturals

(***************************************************************************)
(* Min(m, n) is the smaller of the two numbers m and n.                    *)
(***************************************************************************)
Min(m, n) == IF m < n THEN m ELSE n

CONSTANTS Jug,       \* The set of all jugs.
          Capacity,  \* A function: Capacity[j] is the capacity of jug j.
          Goal       \* The amount of water we want some jug to contain.

(***************************************************************************)
(* We assume that every capacity is a positive integer and that Goal is a  *)
(* natural number.                                                         *)
(***************************************************************************)
ASSUME /\ Capacity \in [Jug -> {n \in Nat : n > 0}]
       /\ Goal \in Nat

VARIABLE contents   \* contents[j] is the amount of water now in jug j.

(***************************************************************************)
(* The type-correctness invariant.                                         *)
(***************************************************************************)
TypeOK == contents \in [Jug -> Nat]

(***************************************************************************)
(* Initially, every jug is empty.                                          *)
(***************************************************************************)
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
(* Pour as much water as possible from jug j into jug k.  The amount       *)
(* poured is limited by the water in j and the free space left in k.       *)
(***************************************************************************)
JugToJug(j, k) ==
  LET amountPoured == Min(contents[j], Capacity[k] - contents[k])
  IN  contents' = [contents EXCEPT ![j] = @ - amountPoured,
                                   ![k] = @ + amountPoured]

(***************************************************************************)
(* The next-state relation.                                                *)
(***************************************************************************)
Next ==  \E j \in Jug : \/ FillJug(j)
                        \/ EmptyJug(j)
                        \/ \E k \in Jug \ {j} : JugToJug(j, k)

(***************************************************************************)
(* The complete (stuttering-inclusive) specification.                      *)
(***************************************************************************)
Spec == Init /\ [][Next]_contents

(***************************************************************************)
(* NotSolved asserts that no jug currently contains exactly Goal gallons.  *)
(* To find a solution to the puzzle, have TLC check NotSolved as an        *)
(* invariant.  If the puzzle has a solution, TLC will report that the      *)
(* invariant is violated and the error trace it prints is a sequence of    *)
(* steps that solves the problem.                                          *)
(***************************************************************************)
NotSolved == \A j \in Jug : contents[j] # Goal

THEOREM Spec => [](TypeOK)
=============================================================================