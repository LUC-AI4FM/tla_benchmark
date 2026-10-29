---- MODULE CaseOtherUpdate ----
EXTENDS Integers

S == {1, 2, 3}

Val == 42

VARIABLES x, f

vars == <<x, f>>

Update(g) ==
    CASE x = 1 -> [g EXCEPT ![2] = Val]
      [] OTHER -> g

Init ==
    /\ x \in S
    /\ f = [i \in S |-> 0]

Next ==
    /\ f' = Update(f)
    /\ x' = x

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ x \in S
    /\ f \in [S -> Int]
====