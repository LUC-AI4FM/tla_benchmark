------------------------------- MODULE FastMutex -------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS M, N
VARIABLES x, y, b, cs

Init == /\ x = 0 
        /\ y = 0 
        /\ b = [i \in 1..N -> FALSE] 
        /\ cs = {}

Next ==
    \/ \E i \in 1..M : 
        (b[i] = FALSE) 
        /\ (x' = i) 
        /\ (y' = y)
        /\ (b' = [b EXCEPT ![i] = TRUE])
        /\ (cs' = cs)
    \/ \E j \in M+1..N :
        (b[j] = FALSE) 
        /\ (x' = x)
        /\ (y' = j)
        /\ (b' = [b EXCEPT ![j] = TRUE])
        /\ (cs' = cs)
    \/ \E i \in 1..M : 
        (b[i] = TRUE) 
        /\ (x = i) 
        /\ (y = 0) 
        /\ (b' = b)
        /\ (cs' = {i})
    \/ \E j \in M+1..N :
        (b[j] = TRUE) 
        /\ (x = 0) 
        /\ (y = j) 
        /\ (b' = b)
        /\ (cs' = {j})
    \/ \E i \in 1..M : 
        (b[i] = TRUE) 
        /\ (x = i) 
        /\ (y # 0) 
        /\ (b' = [b EXCEPT ![i] = FALSE])
        /\ (cs' = {})
    \/ \E j \in M+1..N :
        (b[j] = TRUE) 
        /\ (x # 0) 
        /\ (y = j) 
        /\ (b' = [b EXCEPT ![j] = FALSE])
        /\ (cs' = {})

Spec == 
    /\ Init
    /\ [][Next]_<<x, y, b, cs>>
    /\ WF_<<x, y, b, cs>>_(\E i \in 1..M : b[i] = FALSE)
    /\ WF_<<x, y, b, cs>>_(\E j \in M+1..N : b[j] = FALSE)

MutualExclusion == \/ cs = {}
                     \/ (\A i, j \in cs: i = j)

Liveness ==
    [](<>[](\E i \in 1..M : i \in cs))
    /\ [](<>[](\E j \in M+1..N : j \in cs))

=============================================================================