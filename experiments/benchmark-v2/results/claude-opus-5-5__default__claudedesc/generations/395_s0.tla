---------------------------- MODULE FingerprintTest ----------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

S == {1}
T == {2, 3, 4}

Rec == [a : T, b : T]

TypeOK ==
    /\ x \in [S -> [S -> SUBSET T]]
    /\ y \in [S -> [S -> SUBSET Rec]]

Init ==
    /\ x \in [S -> [S -> SUBSET T]]
    /\ y \in [S -> [S -> SUBSET Rec]]
    /\ PrintT("Distinct states should equal distinct initial states")

\* Stutter: no change at all
Stutter ==
    UNCHANGED <<x, y>>

\* Reassign x using a set with duplicate elements; normalizes to {2, 3}
ReassignX ==
    /\ x' = [i \in S |-> [j \in S |-> {2, 3, 2, 3, 3}]]
    /\ UNCHANGED y

\* Reassign y using records with duplicate values and reordered fields
ReassignY ==
    /\ y' = [i \in S |-> [j \in S |->
                {[a |-> 2, b |-> 3], [b |-> 3, a |-> 2], [a |-> 2, b |-> 3],
                 [a |-> 4, b |-> 4], [b |-> 4, a |-> 4]}]]
    /\ UNCHANGED x

\* Update specific elements of y to singleton sets of particular records
UpdateY1 ==
    /\ y' = [y EXCEPT ![1][1] = {[a |-> 3, b |-> 4]}]
    /\ UNCHANGED x

UpdateY2 ==
    /\ y' = [y EXCEPT ![1] = [j \in S |-> {[b |-> 2, a |-> 4]}]]
    /\ UNCHANGED x

Next ==
    \/ Stutter
    \/ ReassignX
    \/ ReassignY
    \/ UpdateY1
    \/ UpdateY2

Spec == Init /\ [][Next]_vars

\* Two syntactically different, semantically identical expressions must be equal
Expr1 ==
    [i \in S |-> [j \in S |->
        {{2, 2, 3}, {3, 2}, {4, 4, 4}} \cup
        {[a |-> 2, b |-> 3], [b |-> 3, a |-> 2], [a |-> 2, b |-> 3]}]]

Expr2 ==
    [i \in S |-> [j \in S |->
        {{2, 3}, {4}} \cup {[b |-> 3, a |-> 2]}]]

Inv ==
    /\ Assert(Expr1 = Expr2, "Fingerprint failure: equivalent expressions differ")
    /\ Assert({1, 1, 2} = {2, 1}, "Fingerprint failure: duplicate set elements")
    /\ Assert([a |-> 1, b |-> 2] = [b |-> 2, a |-> 1],
              "Fingerprint failure: record field order")

=============================================================================