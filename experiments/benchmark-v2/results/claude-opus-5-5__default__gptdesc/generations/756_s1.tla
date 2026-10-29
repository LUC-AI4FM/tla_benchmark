---------------------------- MODULE APDieHarder ----------------------------
(***************************************************************************)
(* Apalache-specific wrapper for the DieHarder specification.             *)
(* Provides type annotations for the constants and variable, instantiates *)
(* DieHarder, and gives concrete constant values JugVal and CapacityVal   *)
(* to be used with APDieHarder.cfg.                                       *)
(***************************************************************************)

    ------------------------------ MODULE DieHarder ------------------------------
    EXTENDS Naturals

    CONSTANTS
        \* @type: Set(Str);
        Jug,
        \* @type: Str -> Int;
        Capacity,
        \* @type: Int;
        Goal

    ASSUME /\ Capacity \in [Jug -> {n \in Nat : n > 0}]
           /\ Goal \in Nat

    \* @type: (Int, Int) => Int;
    Min(m, n) == IF m < n THEN m ELSE n

    VARIABLES
        \* @type: Str -> Int;
        contents

    TypeOK == contents \in [Jug -> Nat]

    Init == contents = [j \in Jug |-> 0]

    FillJug(j)  == contents' = [contents EXCEPT ![j] = Capacity[j]]

    EmptyJug(j) == contents' = [contents EXCEPT ![j] = 0]

    JugToJug(j, k) ==
        LET amountPoured == Min(contents[j], Capacity[k] - contents[k])
        IN  contents' = [contents EXCEPT ![j] = @ - amountPoured,
                                         ![k] = @ + amountPoured]

    Next == \E j \in Jug :
               \/ FillJug(j)
               \/ EmptyJug(j)
               \/ \E k \in Jug \ {j} : JugToJug(j, k)

    Spec == Init /\ [][Next]_contents

    \* Invariant whose violation exhibits a solution to the puzzle
    NotSolved == \A j \in Jug : contents[j] # Goal
    =============================================================================