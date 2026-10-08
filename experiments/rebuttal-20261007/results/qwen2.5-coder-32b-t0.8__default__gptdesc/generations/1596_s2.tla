------------------------------- MODULE FastMutex -------------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANTS M, N

VARIABLES x, y, b, pc1, pc2

Init == 
    /\ x = 0 
    /\ y = 0 
    /\ b = <<FALSE, FALSE>>
    /\ pc1 = [p \in 1..M -> "entry"]
    /\ pc2 = [p \in (M+1)..N -> "entry"]

P1Entry(p) ==
    /\ pc1[p] = "entry"
    /\ x' = p
    /\ y' = 0
    /\ b' = [b EXCEPT ![p-1] = TRUE]
    /\ pc1' = [pc1 EXCEPT ![p] = "wait"]

P2Entry(p) ==
    /\ pc2[p] = "entry"
    /\ x' = p
    /\ y' = 0
    /\ b' = [b EXCEPT ![p-1-M] = TRUE]
    /\ pc2' = [pc2 EXCEPT ![p] = "wait"]

P1Wait(p) ==
    \/ /\ pc1[p] = "wait"
       /\ \E q \in (M+1)..N : b[q-M-1]
          -> y' = p
    \/ /\ pc1[p] = "wait"
       /\ y # p
          -> pc1' = [pc1 EXCEPT ![p] = "wait"]
    \/ /\ pc1[p] = "wait"
       /\ y = p
       /\ b[q-M-1] = FALSE \A q \in (M+1)..N
          -> pc1' = [pc1 EXCEPT ![p] = "critical"]

P2Wait(p) ==
    \/ /\ pc2[p] = "wait"
       /\ \E q \in 1..M : b[q-1]
          -> y' = p
    \/ /\ pc2[p] = "wait"
       /\ y # p
          -> pc2' = [pc2 EXCEPT ![p] = "wait"]
    \/ /\ pc2[p] = "wait"
       /\ y = p
       /\ b[q-1] = FALSE \A q \in 1..M
          -> pc2' = [pc2 EXCEPT ![p] = "critical"]

P1Critical(p) ==
    /\ pc1[p] = "critical"
    /\ pc1' = [pc1 EXCEPT ![p] = "exit"]

P2Critical(p) ==
    /\ pc2[p] = "critical"
    /\ pc2' = [pc2 EXCEPT ![p] = "exit"]

P1Exit(p) ==
    /\ pc1[p] = "exit"
    /\ b' = [b EXCEPT ![p-1] = FALSE]
    /\ pc1' = [pc1 EXCEPT ![p] = "entry"]

P2Exit(p) ==
    /\ pc2[p] = "exit"
    /\ b' = [b EXCEPT ![p-1-M] = FALSE]
    /\ pc2' = [pc2 EXCEPT ![p] = "entry"]

Next == 
    \/ \E p \in 1..M : P1Entry(p)
    \/ \E p \in (M+1)..N : P2Entry(p)
    \/ \E p \in 1..M : P1Wait(p)
    \/ \E p \in (M+1)..N : P2Wait(p)
    \/ \E p \in 1..M : P1Critical(p)
    \/ \E p \in (M+1)..N : P2Critical(p)
    \/ \E p \in 1..M : P1Exit(p)
    \/ \E p \in (M+1)..N : P2Exit(p)

Spec == Init /\ [][Next]_<<x, y, b, pc1, pc2>>

MutualExclusion ==
    \/ \A p \in 1..M : pc1[p] # "critical"
    \/ \A p \in (M+1)..N : pc2[p] # "critical"
    \/ \A p \in 1..M, q \in (M+1)..N : ~(pc1[p] = "critical" /\ pc2[q] = "critical")

Liveness ==
    <>[](\E p \in 1..M : pc1[p] = "critical") 
    \/ <>[](\E p \in (M+1)..N : pc2[p] = "critical")

Fairness ==
    WF_next(<<pc1, x, y, b>>) 
    /\ SF_next({p \in 1..M : pc1[p] = "entry"}) 
    /\ SF_next({p \in 1..M : pc1[p] = "wait"})
    /\ SF_next({p \in (M+1)..N : pc2[p] = "entry"}) 
    /\ SF_next({p \in (M+1)..N : pc2[p] = "wait"})

CompleteSpec == Spec /\ []MutualExclusion /\ Liveness /\ Fairness

===============================================================================