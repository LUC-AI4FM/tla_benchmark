---- MODULE PositiveAssign ----
EXTENDS Integers

VARIABLE x

vars == << x >>

\* Small finite set of candidate values; only strictly positive ones may be chosen
Values == {-2, -1, 0, 1, 2, 3}

InitVal == 1

Init == x = InitVal

Assign(v) == /\ v \in Values
             /\ v > 0
             /\ x' = v

Next == \E v \in Values : Assign(v)

Spec == Init /\ [][Next]_vars

\* Domain of the state variable
TypeOK == x \in Values \cup {InitVal}

\* Safety invariant: the variable is never zero
Inv == x # 0

\* Every non-stuttering step assigns a permitted, strictly positive value
TransitionOK == [][x' \in Values /\ x' > 0]_x

THEOREM Spec => []Inv
THEOREM Spec => TransitionOK
====