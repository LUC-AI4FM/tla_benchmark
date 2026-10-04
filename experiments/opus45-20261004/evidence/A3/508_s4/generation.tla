---- MODULE Specification ----
EXTENDS Integers

CONSTANTS MinVal, MaxVal

VARIABLES x, pc

vars == <<x, pc>>

Init ==
    /\ x \in MinVal..MaxVal
    /\ pc = "Lbl_1"

Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ Assert(x ^ 2 <= 100, "Failure of assertion at line X")
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
    /\ x \in Int
    /\ pc \in {"Lbl_1", "Done"}

SafetyInvariant ==
    pc = "Done" => x ^ 2 <= 100

====