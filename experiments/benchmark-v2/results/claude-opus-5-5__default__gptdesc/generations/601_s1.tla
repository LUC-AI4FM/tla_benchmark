---------------------------- MODULE MCTwoClients ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS c1, c2

ASSUME c1 # c2

Clients == {c1, c2}

PrimaryKeys == {1, 2}

ClientPrimaryKey == [c \in Clients |-> IF c = c1 THEN 1 ELSE 2]

VARIABLES table

vars == << table >>

TypeOK ==
    /\ table \in [PrimaryKeys -> {"empty"}]
    /\ ClientPrimaryKey \in [Clients -> PrimaryKeys]

ClientKeysUnique ==
    \A a, b \in Clients : (a # b) => (ClientPrimaryKey[a] # ClientPrimaryKey[b])

ClientKeysCoverTable ==
    {ClientPrimaryKey[c] : c \in Clients} = PrimaryKeys

Init == table = [k \in PrimaryKeys |-> "empty"]

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

=============================================================================