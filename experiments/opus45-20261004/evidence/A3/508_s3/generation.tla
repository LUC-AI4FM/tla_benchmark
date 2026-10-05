```tla
MODULE Spec

EXTENDS Integers

VARIABLES x, pc

vars == <<x, pc>>

Init ==
    /\ x \in 1..10
    /\ pc = "Lbl_1"

Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ Assert(x ^ 2 <= 100, "Assertion failed: x ^ 2 <= 100")
    /\ pc' = "Done"
    /\ x' = x

Assert(cond, msg) == cond

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Lbl_1
    \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

TypeInvariant ==
    /\ x \in 1..10
    /\ pc \in {"Lbl_1", "Done"}

SafetyInvariant ==
    x ^ 2 <= 100

END MODULE
```