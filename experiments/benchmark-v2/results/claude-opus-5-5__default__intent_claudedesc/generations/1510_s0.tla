---------------------------- MODULE CaseOtherUpdate ----------------------------
EXTENDS Integers

CONSTANTS Val

S == {1, 2, 3}

VARIABLES x, f

vars == <<x, f>>

\* Record/function update operator defined using CASE with an OTHER clause
Update(g, v) ==
    CASE v = 1 -> [g EXCEPT ![2] = Val]
      [] OTHER -> g

TypeOK ==
    /\ x \in S
    /\ f \in [S -> Int]

Init ==
    /\ x \in S
    /\ f = [i \in S |-> 0]

Next ==
    /\ f' = Update(f, x)
    /\ x' = x

Spec == Init /\ [][Next]_vars

=============================================================================