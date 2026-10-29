---- MODULE ClientTable ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS c1, c2

ASSUME c1 # c2

Clients == {c1, c2}

PrimaryKeys == {1, 2}

ClientPrimaryKey == (c1 :> 1) @@ (c2 :> 2)

ASSUME ClientPrimaryKey \in [Clients -> PrimaryKeys]

ASSUME \A a, b \in Clients : a # b => ClientPrimaryKey[a] # ClientPrimaryKey[b]

VARIABLES table

vars == << table >>

Init == table = [k \in PrimaryKeys |-> 0]

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

TypeOK == table \in [PrimaryKeys -> Nat]

ClientKeyUnique ==
    \A a, b \in Clients : a # b => ClientPrimaryKey[a] # ClientPrimaryKey[b]

ClientKeyValid ==
    \A c \in Clients : ClientPrimaryKey[c] \in DOMAIN table

====