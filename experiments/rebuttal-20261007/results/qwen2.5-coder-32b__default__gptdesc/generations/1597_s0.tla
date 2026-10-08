------------------------------- MODULE FastMutualExclusion -------------------------------
EXTENDS Naturals, TLC

CONSTANTS N \* Number of processes (N >= 2)

VARIABLES x, y, b, state, failed

Init == 
    /\ x = [p \in 1..N -> FALSE]
    /\ y = [p \in 1..N -> FALSE]
    /\ b = [p \in 1..N -> FALSE]
    /\ state = [p \in 1..N -> "idle"]
    /\ failed = [p \in 1..N -> FALSE]

Next == 
    \/ \E p \in 1..N : \A q \in 1..N : q # p => ~failed[q] /\ 
        (state[p] = "idle" /\ state[q] # "critical" /\ state[q] # "want_in") 
        -> [][p \in 1..N |-> IF p = THEN TRUE ELSE x[p]]_<<x>> 
           /\ [][p \in 1..N |-> IF p = THEN FALSE ELSE y[p]]_<<y>> 
           /\ [][p \in 1..N |-> IF p = THEN FALSE ELSE b[p]]_<<b>> 
           /\ [][p \in 1..N |-> IF p = THEN "want_in" ELSE state[p]]_<<state>>
    \/ \E p \in 1..N : state[p] = "want_in" 
        -> [][p \in 1..N |-> IF p = THEN TRUE ELSE x[p]]_<<x>> 
           /\ [][p \in 1..N |-> IF p = THEN FALSE ELSE y[p]]_<<y>> 
           /\ [][p \in 1..N |-> IF p = THEN FALSE ELSE b[p]]_<<b>> 
           /\ [][p \in 1..N |-> IF p = THEN "wait" ELSE state[p]]_<<state>>
    \/ \E p \in 1..N : state[p] = "wait" 
        -> [][p \in 1..N |-> IF p = THEN FALSE ELSE x[p]]_<<x>> 
           /\ [][p \in 1..N |-> IF p = THEN TRUE ELSE y[p]]_<<y>> 
           /\ [][p \in 1..N |-> IF p = THEN FALSE ELSE b[p]]_<<b>> 
           /\ [][p \in 1..N |-> IF p = THEN "wait" ELSE state[p]]_<<state>>
    \/ \E p \in 1..N : \A q \in 1..N : q # p => ~failed[q] /\ 
        (state[p] = "wait" /\ (\A r \in 1..N : r # p => y[r] => b[r])) 
        -> [][p \in 1..N |-> IF p = THEN FALSE ELSE x[p]]_<<x>> 
           /\ [][p \in 1..N |-> IF p = THEN FALSE ELSE y[p]]_<<y>> 
           /\ [][p \in 1..N |-> IF p = THEN TRUE ELSE b[p]]_<<b>> 
           /\ [][p \in 1..N |-> IF p = THEN "critical" ELSE state[p]]_<<state>>
    \/ \E p \in 1..N : state[p] = "critical" 
        -> [][p \in 1..N |-> IF p = THEN FALSE ELSE x[p]]_<<x>> 
           /\ [][p \in 1..N |-> IF p = THEN FALSE ELSE y[p]]_<<y>> 
           /\ [][p \in 1..N |-> IF p = THEN FALSE ELSE b[p]]_<<b>> 
           /\ [][p \in 1..N |-> IF p = THEN "idle" ELSE state[p]]_<<state>>
    \/ \E p \in 1..N : failed[p] 
        -> [][p \in 1..N |-> IF p = THEN FALSE ELSE x[p]]_<<x>> 
           /\ [][p \in 1..N |-> IF p = THEN FALSE ELSE y[p]]_<<y>> 
           /\ [][p \in 1..N |-> IF p = THEN FALSE ELSE b[p]]_<<b>> 
           /\ [][p \in 1..N |-> IF p = THEN "failed" ELSE state[p]]_<<state>>

MutualExclusion == \A p, q \in 1..N : p # q => ~ (state[p] = "critical" /\ state[q] = "critical")

Liveness == <>[] (\E p \in 1..N : state[p] = "critical")

Spec == Init /\ [][Next]_<<x, y, b, state>> /\ WF_next(<<x, y, b, state>>) /\ MutualExclusion /\ Liveness

WF_next(vars) == 
    \/ \A p \in 1..N : WFair(p, vars)
    \/ \A p \in 2..N : WFair(p, vars)

WFair(p, vars) == WF_vars(<<x[p], y[p], b[p], state[p]>>, vars)

=============================================================================