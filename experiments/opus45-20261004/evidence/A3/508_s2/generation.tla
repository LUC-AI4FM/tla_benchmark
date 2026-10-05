---- MODULE Specification ----
EXTENDS Integers

CONSTANTS MinVal, MaxVal

VARIABLES x, pc

vars == <<x, pc>>

Init ==
    /\ x \in MinVal..MaxVal
    /\ pc = "start"

Assertion ==
    x ^ 2 <= 100

Next ==
    \/ /\ pc = "start"
       /\ Assert(Assertion, "Assertion x ^ 2 <= 100 failed")
       /\ pc' = "Done"
       /\ x' = x
    \/ /\ pc = "Done"
       /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

TypeInvariant ==
    /\ x \in Int
    /\ pc \in {"start", "Done"}

SafetyInvariant ==
    pc = "Done" => x ^ 2 <= 100

====