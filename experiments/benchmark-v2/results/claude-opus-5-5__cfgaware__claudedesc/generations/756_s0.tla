---------------------------- MODULE ApaDieHarder ----------------------------
(***************************************************************************)
(* Apalache-typed wrapper for the "Die Hard" water jug puzzle.             *)
(* The DieHarder definitions are included inline so that this module is    *)
(* self-contained and parses on its own.                                   *)
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
(* Concrete values for model checking                                      *)
(***************************************************************************)
\* @type: Set(Str);
JugVal == {"small", "big"}

\* @type: Str -> Int;
CapacityVal == [j \in JugVal |-> IF j = "small" THEN 3 ELSE 5]

(***************************************************************************)
(* DieHarder specification                                                 *)
(***************************************************************************)
Min(m, n) == IF m < n THEN m ELSE n

TypeOK == contents \in [Jug -> Nat]
          /\ \A j \in Jug : contents[j] <= Capacity[j]

Init == contents = [j \in Jug |-> 0]

FillJug(j) == contents' = [contents EXCEPT ![j] = Capacity[j]]

EmptyJug(j) == contents' = [contents EXCEPT ![j] = 0]

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

NotSolved == \A j \in Jug : contents[j] /= Goal

=============================================================================