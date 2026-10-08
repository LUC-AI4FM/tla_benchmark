```
MODULE FastMutualExclusion
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES x, y, b, j, failed

Init == (* Initial state *)
        /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ j = [i \in 1..N |-> 0]
        /\ failed = [i \in 1..N |-> FALSE]

Try == (* Try to enter critical section *)
        /\ \E i \in 1..N :
            /\ x' = i
            /\ UNCHANGED y
            /\ b' = [b EXCEPT ![i] = TRUE]
            /\ j' = [j EXCEPT ![i] = 1]
            /\ failed' = [failed EXCEPT ![i] = FALSE]
            /\ UNCHANGED <<x, y, b, j, failed>>[i]

Test == (* Test and set *)
        /\ \E i \in 1..N :
            /\ x = i
            /\ j[i] = 1
            /\ y' = IF b[i] THEN y ELSE i
            /\ UNCHANGED x
            /\ b' = [b EXCEPT ![i] = FALSE]
            /\ j' = [j EXCEPT ![i] = 2]
            /\ failed' = [failed EXCEPT ![i] = y /= i]
            /\ UNCHANGED <<x, y, b, j, failed>>[i]

Critical == (* Enter critical section *)
        /\ \E i \in 1..N :
            /\ x = i
            /\ y = i
            /\ j[i] = 2
            /\ x' = 0
            /\ UNCHANGED y
            /\ b' = [b EXCEPT ![i] = FALSE]
            /\ j' = [j EXCEPT ![i] = 0]
            /\ failed' = [failed EXCEPT ![i] = FALSE]
            /\ UNCHANGED <<x, y, b, j, failed>>[i]

Next == (* Global Next action *)
        Try
        \/ Test
        \/ Critical

MutualExclusion == (* Mutual exclusion invariant *)
        \A i, j \in 1..N :
            /\ x = i
            /\ x = j
            ==> i = j

Spec == (* Temporal specification *)
        Init /\ [][Next]_<<x, y, b, j, failed>>
        /\ WF_vars(Try, <<x, y, b, j, failed>>)
        /\ WF_vars(Test, <<x, y, b, j, failed>>)
        /\ WF_vars(Critical, <<x, y, b, j, failed>>)

Theorem == (* Liveness property *)
        Spec
        ==> <>[]<><x = 0>
```