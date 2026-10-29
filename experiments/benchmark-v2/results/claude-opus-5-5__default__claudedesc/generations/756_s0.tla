------------------------------ MODULE MC_DieHarder ------------------------------
(***************************************************************************)
(* Apalache-compatible typed wrapper for the "Die Hard" water jug puzzle.   *)
(* The DieHarder behavior (fill, empty, pour jug-to-jug) is reproduced      *)
(* here so that this module is self-contained and parses on its own.        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    \* @type: Set(Str);
    Jug,
    \* @type: Str -> Int;
    Capacity,
    \* @type: Int;
    Goal

VARIABLES
    \* @type: Str -> Int;
    contents

(***************************************************************************)
(* Concrete values used for model checking: the Die Hard with a Vengeance  *)
(* configuration, with a 3-gallon and a 5-gallon jug and a goal of 4.      *)
(***************************************************************************)
\* @type: Set(Str);
MCJug == {"small", "big"}

\* @type: Str -> Int;
MCCapacity == [j \in MCJug |-> IF j = "small" THEN 3 ELSE 5]

\* @type: Int;
MCGoal == 4

ASSUME /\ Capacity \in [Jug -> Nat \ {0}]
       /\ Goal \in Nat

(***************************************************************************)
(* DieHarder specification.                                                *)
(***************************************************************************)
\* @type: (Int, Int) => Int;
Min(m, n) == IF m < n THEN m ELSE n

TypeOK ==
    /\ contents \in [Jug -> Nat]
    /\ \A j \in Jug : contents[j] <= Capacity[j]

Init == contents = [j \in Jug |-> 0]

\* @type: Str => Bool;
FillJug(j) ==
    contents' = [contents EXCEPT ![j] = Capacity[j]]

\* @type: Str => Bool;
EmptyJug(j) ==
    contents' = [contents EXCEPT ![j] = 0]

\* @type: (Str, Str) => Bool;
JugToJug(j, k) ==
    LET amountPoured == Min(contents[j], Capacity[k] - contents[k])
    IN  contents' = [contents EXCEPT ![j] = @ - amountPoured,
                                     ![k] = @ + amountPoured]

Next ==
    \E j \in Jug :
        \/ FillJug(j)
        \/ EmptyJug(j)
        \/ \E k \in Jug \ {j} : JugToJug(j, k)

Spec == Init /\ [][Next]_contents

(***************************************************************************)
(* Invariant whose violation exhibits a solution to the puzzle.            *)
(***************************************************************************)
NotSolved == \A j \in Jug : contents[j] # Goal

THEOREM Spec => []TypeOK
=============================================================================