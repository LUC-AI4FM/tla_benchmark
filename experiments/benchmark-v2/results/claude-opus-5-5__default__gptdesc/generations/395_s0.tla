---------------------------- MODULE NestedValueFingerprint ----------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

S == {1}

D == {1, 2}

V == {1, 2}

Rec == [a : V, b : V]

XType == [S -> [D -> SUBSET V]]

YType == [S -> [S -> SUBSET Rec]]

XTypeAlt == [{1} -> [{2, 1} -> SUBSET {2, 1}]]

YTypeAlt == [{1} -> [{1} -> SUBSET [b : {2, 1}, a : {2, 1}]]]

TypeOK ==
    /\ x \in XType
    /\ y \in YType

Init ==
    /\ x = [i \in S |-> [j \in D |-> {}]]
    /\ y = [i \in S |-> [j \in S |-> {}]]

Inv ==
    /\ TypeOK
    /\ IF XType = XTypeAlt /\ YType = YTypeAlt
          THEN TRUE
          ELSE Assert(FALSE, "Structurally equivalent type expressions differ")

SetX1 ==
    /\ \E v \in SUBSET V : x' = [x EXCEPT ![1][1] = v]
    /\ UNCHANGED y

SetX2 ==
    /\ \E v \in SUBSET V : x' = [x EXCEPT ![1][2] = v]
    /\ UNCHANGED y

ResetX ==
    /\ x' = [i \in S |-> [j \in D |-> V]]
    /\ UNCHANGED y

SetY ==
    /\ \E r \in SUBSET Rec : y' = [y EXCEPT ![1][1] = r]
    /\ UNCHANGED x

AddY ==
    /\ \E r \in Rec : y' = [y EXCEPT ![1][1] = @ \cup {r}]
    /\ UNCHANGED x

ResetY ==
    /\ y' = [i \in S |-> [j \in S |-> {[a |-> 1, b |-> 2]}]]
    /\ UNCHANGED x

Next ==
    \/ UNCHANGED vars
    \/ SetX1
    \/ SetX2
    \/ ResetX
    \/ SetY
    \/ AddY
    \/ ResetY

Spec == Init /\ [][Next]_vars

THEOREM Spec => []Inv
=======================================================================================