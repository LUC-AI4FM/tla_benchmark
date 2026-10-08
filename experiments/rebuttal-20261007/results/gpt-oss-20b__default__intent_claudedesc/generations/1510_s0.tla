MODULE CaseExample
EXTENDS Naturals

CONSTANT DOMAIN == {1, 2}

VARIABLES x, f

Init ==
    /\ x \in DOMAIN
    /\ f = [i \in DOMAIN |-> 0]

Next ==
    /\ x' = x
    /\ f' = CASE x = 1 -> [f EXCEPT ![2] = 5]
                 OTHER -> f

Spec == Init /\ [][Next]_<<x, f>>