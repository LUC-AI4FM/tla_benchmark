---------------------------- MODULE NestedFingerprint ----------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

S == {1, 2}

RecSet == [a : S, b : S]

TypeX == [{1} -> [S -> SUBSET S]]

TypeY == [{1} -> SUBSET RecSet]

T1 == [{1} -> [{"a", "b"} -> SUBSET S]]
T2 == [{1} -> [a : SUBSET S, b : SUBSET S]]

Init ==
    /\ x = [i \in {1} |-> [j \in S |-> {}]]
    /\ y = [i \in {1} |-> {}]

Inv ==
    /\ x \in TypeX
    /\ y \in TypeY
    /\ IF T1 = T2
          THEN TRUE
          ELSE Assert(FALSE, "Structurally equivalent type expressions differ")

Next ==
    \/ UNCHANGED vars
    \/ /\ x' = [x EXCEPT ![1][1] = {1}]
       /\ UNCHANGED y
    \/ /\ x' = [x EXCEPT ![1][2] = @ \cup {2}]
       /\ UNCHANGED y
    \/ /\ x' = [x EXCEPT ![1] = [j \in S |-> S]]
       /\ UNCHANGED y
    \/ /\ x' = [i \in {1} |-> [j \in S |-> {j}]]
       /\ UNCHANGED y
    \/ /\ y' = [y EXCEPT ![1] = @ \cup {[a |-> 1, b |-> 2]}]
       /\ UNCHANGED x
    \/ /\ y' = [y EXCEPT ![1] = {[b |-> 1, a |-> 1]}]
       /\ UNCHANGED x
    \/ /\ y' = [i \in {1} |-> {}]
       /\ UNCHANGED x

Spec == Init /\ [][Next]_vars

=============================================================================