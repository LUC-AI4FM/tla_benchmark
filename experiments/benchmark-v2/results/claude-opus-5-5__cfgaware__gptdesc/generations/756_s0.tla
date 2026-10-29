---------------------------- MODULE APDieHarder ----------------------------
(***************************************************************************)
(* Apalache-specific type annotations and concrete constant values for an  *)
(* instance of the DieHarder specification.  The DieHarder definitions are *)
(* included here directly so that this module parses on its own.           *)
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
(* Concrete values for use with APDieHarder.cfg                            *)
(***************************************************************************)
JugVal == {"j1", "j2"}

CapacityVal == [j \in JugVal |-> IF j = "j1" THEN 3 ELSE 5]

(***************************************************************************)
(* DieHarder definitions (equivalent to INSTANCE DieHarder)                *)
(***************************************************************************)
Min(m, n) == IF m < n THEN m ELSE n

ASSUME /\ Capacity \in [Jug -> {n \in Nat : n > 0}]
       /\ Goal \in Nat

TypeOK == contents \in [Jug -> Nat]

Init == contents = [j \in Jug |-> 0]

FillJug(j)  == contents' = [contents EXCEPT ![j] = Capacity[j]]

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

NotSolved == \A j \in Jug : contents[j] # Goal

=============================================================================