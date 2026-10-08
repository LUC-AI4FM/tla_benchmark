```tla
MODULE FastMutualExclusion

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N \* Number of processes

VARIABLES x, y, b, j, pc \* Shared and local variables

Init == /\ x = 0
        /\ y = 0
        /\ b = <<FALSE>>[1..N]
        /\ \A p \in 1..N: j[p] = 1
        /\ pc = [p \in 1..N -> "entry"]

Next ==
    \/ \E p \in 1..N:
         /\ pc[p] = "entry"
         /\ x = 0
         /\ y = 0
         /\ b' = [b EXCEPT ![p] = TRUE]
         /\ j'[p] = j[p]
         /\ x' = p
         /\ y' = p
         /\ pc'[p] = "test1"
         /\ \A q \in 1..N \ {p}: UNCHANGED <<pc[q], b[q], j[q]>>
    \/ \E p \in 1..N:
         /\ pc[p] = "entry"
         /\ x = 0
         /\ y # 0
         /\ y # p
         /\ b' = [b EXCEPT ![p] = TRUE]
         /\ j'[p] = j[p]
         /\ x' = p
         /\ pc'[p] = "test2"
         /\ \A q \in 1..N \ {p}: UNCHANGED <<pc[q], b[q], j[q]>>
    \/ \E p \in 1..N:
         /\ pc[p] = "entry"
         /\ x = 0
         /\ y = p
         /\ b' = [b EXCEPT ![p] = TRUE]
         /\ j'[p] = j[p]
         /\ pc'[p] = "cs_request"
         /\ \A q \in 1..N \ {p}: UNCHANGED <<pc[q], b[q], j[q]>>
    \/ \E p \in 1..N:
         /\ pc[p] = "entry"
         /\ x # 0
         /\ b' = [b EXCEPT ![p] = TRUE]
         /\ j'[p] = j[p]
         /\ pc'[p] = "wait"
         /\ \A q \in 1..N \ {p}: UNCHANGED <<pc[q], b[q], j[q]>>
    \/ \E p \in 1..N:
         /\ pc[p] = "test1"
         /\ x = p
         /\ y' = y
         /\ j'[p] = j[p]
         /\ b' = [b EXCEPT ![p] = FALSE]
         /\ pc'[p] = "cs_request"
         /\ \A q \in 1..N \ {p}: UNCHANGED <<pc[q], b[q], j[q]>>
    \/ \E p \in 1..N:
         /\ pc[p] = "test2"
         /\ x # y
         /\ y' = y
         /\ j'[p] = j[p]
         /\ b' = [b EXCEPT ![p] = FALSE]
         /\ pc'[p] = "wait"
         /\ \A q \in 1..N \ {p}: UNCHANGED <<pc[q], b[q], j[q]>>
    \/ \E p \in 1..N:
         /\ pc[p] = "test2"
         /\ x = y
         /\ y' = p
         /\ j'[p] = j[p]
         /\ pc'[p] = "cs_request"
         /\ \A q \in 1..N \ {p}: UNCHANGED <<pc[q], b[q], j[q]>>
    \/ \E p \in 1..N:
         /\ pc[p] = "wait"
         /\ \E q \in 1..N: x = q
         /\ b' = [b EXCEPT ![p] = FALSE]
         /\ j'[p] = j[p]
         /\ y' = y
         /\ pc'[p] = "entry"
         /\ \A q \in 1..N \ {p}: UNCHANGED <<pc[q], b[q], j[q]>>
    \/ \E p \in 1..N:
         /\ pc[p] = "wait"
         /\ x = 0
         /\ y' = y
         /\ j'[p] = j[p]
         /\ b' = [b EXCEPT ![p] = FALSE]
         /\ pc'[p] = "entry"
         /\ \A q \in 1..N \ {p}: UNCHANGED <<pc[q], b[q], j[q]>>
    \/ \E p \in 1..N:
         /\ pc[p] = "cs_request"
         /\ y # p
         /\ y' = y
         /\ j'[p] = j[p]
         /\ b' = [b EXCEPT ![p] = FALSE]
         /\ pc'[p] = "wait"
         /\ \A q \in 1..N \ {p}: UNCHANGED <<pc[q], b[q], j[q]>>
    \/ \E p \in 1..N:
         /\ pc[p] = "cs_request"
         /\ y = p
         /\ y' = 0
         /\ x' = 0
         /\ b' = [b EXCEPT ![p] = FALSE]
         /\ j'[p] = 1
         /\ pc'[p] = "entry"
         /\ \A q \in 1..N \ {p}: UNCHANGED <<pc[q], b[q], j[q]>>

MutualExclusion == \/ x = 0
                   \/ (\E p \in 1..N: /\ x = p
                                      /\ y = p
                                      /\ pc[p] = "cs_request"
                                      /\ \A q \in 1..N \ {p}: pc[q] \notin {"cs_request"})

Spec ==
    /\ Init
    /\ [][Next]_<<x, y, b, j, pc>>
    /\ WF_[[pc[p] = "entry"]_p \in 1..N]
    /\ []MutualExclusion
    /\ <>(\E p \in 1..N: <>[][pc[p] = "cs_request"])
```