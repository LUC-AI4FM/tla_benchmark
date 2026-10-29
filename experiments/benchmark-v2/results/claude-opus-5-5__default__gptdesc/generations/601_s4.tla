---------------------------- MODULE MC ----------------------------
EXTENDS Naturals, TLC

CONSTANTS c1, c2

ASSUME c1 /= c2

Clients == {c1, c2}

PrimaryKeys == {1, 2}

ClientPrimaryKey == (c1 :> 1) @@ (c2 :> 2)

VARIABLE table

vars == << table >>

Init == table = [k \in PrimaryKeys |-> 0]

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

TypeOK == table \in [PrimaryKeys -> Nat]

ClientPrimaryKeyOK ==
    /\ DOMAIN ClientPrimaryKey = Clients
    /\ \A c \in Clients : ClientPrimaryKey[c] \in PrimaryKeys

ClientPrimaryKeyUnique ==
    \A a, b \in Clients : (a /= b) => (ClientPrimaryKey[a] /= ClientPrimaryKey[b])

=============================================================================