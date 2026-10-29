---- MODULE FingerprintNested ----
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

D == {1}

Vals == {1, 2}

RecSet == [a : {1}, b : {1, 2}]

TypeX == [D -> [D -> SUBSET Vals]]

TypeY == [D -> [D -> SUBSET RecSet]]

\* Structurally equivalent type expressions, written differently
TypeX2 == [{1} -> [{1} -> SUBSET {2, 1}]]

TypeY2 == [{1} -> [{1} -> SUBSET [b : {2, 1}, a : {1}]]]

TypeOK ==
    /\ x \in TypeX
    /\ y \in TypeY

Init ==
    /\ x = [i \in D |-> [j \in D |-> {}]]
    /\ y = [i \in D |-> [j \in D |-> {}]]

Inv ==
    /\ Assert(TypeX = TypeX2, "Type expressions for x differ")
    /\ Assert(TypeY = TypeY2, "Type expressions for y differ")
    /\ TypeOK

Stutter == UNCHANGED vars

SetX1 ==
    /\ x' = [x EXCEPT ![1][1] = {1}]
    /\ UNCHANGED y

SetX2 ==
    /\ x' = [x EXCEPT ![1] = [j \in D |-> {1, 2}]]
    /\ UNCHANGED y

AddX ==
    /\ \E v \in Vals : x' = [x EXCEPT ![1][1] = @ \cup {v}]
    /\ UNCHANGED y

ChooseX ==
    /\ x' \in TypeX
    /\ UNCHANGED y

SetY1 ==
    /\ y' = [y EXCEPT ![1][1] = {[a |-> 1, b |-> 2]}]
    /\ UNCHANGED x

SetY2 ==
    /\ y' = [y EXCEPT ![1][1] = @ \cup {[b |-> 1, a |-> 1]}]
    /\ UNCHANGED x

ChooseY ==
    /\ y' \in TypeY
    /\ UNCHANGED x

ResetY ==
    /\ y' = [i \in D |-> [j \in D |-> {}]]
    /\ UNCHANGED x

Next ==
    \/ Stutter
    \/ SetX1
    \/ SetX2
    \/ AddX
    \/ ChooseX
    \/ SetY1
    \/ SetY2
    \/ ChooseY
    \/ ResetY

Spec == Init /\ [][Next]_vars

THEOREM Spec => []Inv
====