---------------------------- MODULE BoolToggle ----------------------------
EXTENDS Naturals

VARIABLE b

vars == << b >>

TypeOK == b \in BOOLEAN

Init == b = TRUE

Flip == b' = ~b

Next == Flip \/ UNCHANGED b

Spec == Init /\ [][Next]_vars

\* Safety: the state is always a boolean, so no illegal values appear
Safety == [](b \in BOOLEAN)

\* Liveness-style claims: the system is never deadlocked, because
\* either a flip is enabled or stuttering is allowed
NotDeadlocked == ENABLED Next
AlwaysEnabled == [](ENABLED Flip \/ ENABLED UNCHANGED b)

\* Strong invariant claim. It is expected to FAIL, because b may flip to FALSE.
StrongInv == b = TRUE

\* Weaker observational claim. It holds, because b is initially TRUE.
WeakInv == Init => b = TRUE

\* Property checked by the configuration
Prop == [](b \in BOOLEAN) /\ [](ENABLED Next)

THEOREM Spec => []TypeOK
THEOREM Spec => Prop
=============================================================================