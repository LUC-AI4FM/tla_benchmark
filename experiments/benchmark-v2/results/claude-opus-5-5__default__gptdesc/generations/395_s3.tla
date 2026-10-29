---------------------------- MODULE FingerprintNested ----------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Dom == {1}

Vals == {1, 2}

Rec == [a : Vals, b : Vals]

XType == [Dom -> [Dom -> SUBSET Vals]]

YType == [Dom -> [Dom -> SUBSET Rec]]

\* Structurally equivalent type expressions, written differently
XType2 == [{1} -> [{1} -> SUBSET {2, 1}]]

YType2 == [{1} -> [{1} -> SUBSET [b : {2, 1}, a : {1, 2}]]]

TypeOK == /\ x \in XType
          /\ y \in YType

Init == /\ x = [i \in Dom |-> [j \in Dom |-> {}]]
        /\ y = [i \in Dom |-> [j \in Dom |-> {}]]

Inv == /\ TypeOK
       /\ IF XType = XType2
             THEN TRUE
             ELSE Assert(FALSE, "XType and XType2 differ")
       /\ IF YType = YType2
             THEN TRUE
             ELSE Assert(FALSE, "YType and YType2 differ")

SetX1 == /\ x' = [x EXCEPT ![1][1] = {1}]
         /\ UNCHANGED y

SetX2 == /\ x' = [x EXCEPT ![1][1] = @ \cup {2}]
         /\ UNCHANGED y

ResetX == /\ x' = [i \in Dom |-> [j \in Dom |-> {}]]
          /\ UNCHANGED y

AddY == /\ \E r \in Rec :
             y' = [y EXCEPT ![1][1] = @ \cup {r}]
        /\ UNCHANGED x

SetY == /\ y' = [y EXCEPT ![1] = [j \in Dom |-> {[a |-> 1, b |-> 2]}]]
        /\ UNCHANGED x

ResetY == /\ y' = [i \in Dom |-> [j \in Dom |-> {}]]
          /\ UNCHANGED x

Next == \/ UNCHANGED vars
        \/ SetX1
        \/ SetX2
        \/ ResetX
        \/ AddY
        \/ SetY
        \/ ResetY

Spec == Init /\ [][Next]_vars

THEOREM Spec => []Inv
==================================================================================