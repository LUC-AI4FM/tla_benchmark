---------------------------- MODULE FingerprintNested ----------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Dom == {1}
Vals == {1, 2}

Rec == [a : Vals, b : Vals]

XType == [Dom -> [Vals -> SUBSET Vals]]
XTypeAlt == [{1} -> [{2, 1} -> SUBSET {2, 1}]]

YType == [Dom -> [Dom -> SUBSET Rec]]
YTypeAlt == [{1} -> [{1} -> SUBSET [b : {2, 1}, a : {2, 1}]]]

Init ==
    /\ x = [i \in Dom |-> [j \in Vals |-> {}]]
    /\ y = [i \in Dom |-> [j \in Dom |-> {}]]

TypeOK ==
    /\ x \in XType
    /\ y \in YType

Inv ==
    /\ Assert(XType = XTypeAlt, "Structurally equivalent x types differ")
    /\ Assert(YType = YTypeAlt, "Structurally equivalent y types differ")
    /\ TypeOK

Next ==
    \/ UNCHANGED vars
    \/ /\ x' = [x EXCEPT ![1][1] = {1}]
       /\ UNCHANGED y
    \/ /\ x' = [x EXCEPT ![1][2] = @ \cup {2}]
       /\ UNCHANGED y
    \/ /\ x' = [i \in Dom |-> [j \in Vals |-> x[i][j] \cup {j}]]
       /\ UNCHANGED y
    \/ /\ x' = [x EXCEPT ![1] = [j \in Vals |-> {}]]
       /\ UNCHANGED y
    \/ /\ y' = [y EXCEPT ![1][1] = {[a |-> 1, b |-> 2]}]
       /\ UNCHANGED x
    \/ /\ y' = [y EXCEPT ![1][1] = @ \cup {[b |-> 1, a |-> 2]}]
       /\ UNCHANGED x
    \/ /\ y' = [i \in Dom |-> [j \in Dom |-> {}]]
       /\ UNCHANGED x

Spec == Init /\ [][Next]_vars

THEOREM Spec => []Inv
=============================================================================