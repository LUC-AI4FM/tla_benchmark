---------------------------- MODULE MCClientTable ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS c1, c2

ASSUME c1 # c2

Clients == {c1, c2}

PrimaryKeys == {1, 2}

ClientPrimaryKey == (c1 :> 1) @@ (c2 :> 2)

VARIABLES table

vars == << table >>

TypeOK ==
    /\ ClientPrimaryKey \in [Clients -> PrimaryKeys]
    /\ table \in [PrimaryKeys -> {0}]

UniquePrimaryKeys ==
    \A x, y \in Clients : (x # y) => (ClientPrimaryKey[x] # ClientPrimaryKey[y])

KeysCovered ==
    {ClientPrimaryKey[c] : c \in Clients} = PrimaryKeys

Init ==
    table = [k \in PrimaryKeys |-> 0]

Next ==
    UNCHANGED vars

Spec == Init /\ [][Next]_vars

=============================================================================