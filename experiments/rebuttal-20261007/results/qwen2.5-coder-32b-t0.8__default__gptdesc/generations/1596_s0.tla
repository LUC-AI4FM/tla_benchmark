------------------------------ MODULE FastMutex ------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS M, N
VARIABLES x, y, b, cs

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N -> FALSE]
        /\ cs = {}

Next ==
    LET ProcessA == {i \in 1..M}
        ProcessB == {i \in (M+1)..N}
        Action(i) ==
            \/ /\ x' = i
               /\ y' = 0
               /\ b' = [b EXCEPT ![i] = TRUE]
               /\ cs' = {}
            \/ /\ y' = i
               /\ b'[i] = FALSE
               /\ cs' = {}
            \/ /\ UNCHANGED <<x, y, b>>
               /\ b[i]
               /\ (y = 0 \/ y = i)
               /\ cs' = {i}
        InCS(i) == cs = {i}
    IN \/ \E i \in ProcessA : Action(i) /\ ~InCS(i)
       \/ \E i \in ProcessB : Action(i) /\ ~InCS(i)

Spec ==
    /\ Init
    /\ [][Next]_<<x, y, b, cs>>
    /\ WF_<<x, y, b, cs>>(ProcessA)
    /\ WF_<<x, y, b, cs>>(ProcessB)
    /\ \A i, j \in 1..N : i # j => ~[]<>(InCS(i) /\ InCS(j))
    /\ <>[](\E i \in 1..N : <>[](InCS(i)))

=============================================================================