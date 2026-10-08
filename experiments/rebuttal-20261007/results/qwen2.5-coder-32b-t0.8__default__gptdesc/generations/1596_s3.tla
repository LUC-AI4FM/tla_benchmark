------------------------------- MODULE FastMutex -------------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANTS M, N
VARIABLES x, y, b

ASSUME 1 <= M /\ M < N

Init == 
    /\ x = <<0>> ++ [j \in 1..M -> 0]
    /\ y = <<0>> ++ [j \in (M+1)..N -> 0]
    /\ b = FALSE

MutexP ==
    {p \in 1..M}
MutexQ ==
    {p \in (M+1)..N}

DoP(p) == 
    /\ p \in MutexP
    /\ \/ /\ x[p] = 0
           /\ y[p]' = p
           /\ b' = TRUE
       \/ /\ x[p] # 0
          /\ y[x[p]] # p
          /\ IF x[p] <= M THEN x'[x[p]] = 0 ELSE y'[x[p]] = 0
       \/ /\ x[p] # 0
          /\ y[x[p]] = p
          /\ b' = FALSE
       \/ /\ x[p] = 0
          /\ \E q \in MutexQ: y[q] = p
          /\ x'[p] = q

DoQ(p) ==
    /\ p \in MutexQ
    /\ \/ /\ y[p] = 0
           /\ x[p]' = p
           /\ b' = TRUE
       \/ /\ y[p] # 0
          /\ x[y[p]] # p
          /\ IF y[p] <= M THEN x'[y[p]] = 0 ELSE y'[y[p]] = 0
       \/ /\ y[p] # 0
          /\ x[y[p]] = p
          /\ b' = FALSE
       \/ /\ y[p] = 0
          /\ \E q \in MutexP: x[q] = p
          /\ y'[p] = q

Next ==
    \/ \E p \in MutexP: DoP(p) /\ \A q \notin {p}: y' = y[q]
    \/ \E p \in MutexQ: DoQ(p) /\ \A q \notin {p}: x' = x[q]

MutualExclusion == 
    \/ \A p1, p2 \in 1..M: \/ p1 = p2 \/ \/ x[p1] # p2 \/ y[p2] # p1
    \/ \A p1, p2 \in (M+1)..N: \/ p1 = p2 \/ \/ x[p1] # p2 \/ y[p2] # p1
    \/ \A p1 \in 1..M, p2 \in (M+1)..N: \/ x[p1] # p2 /\ y[p2] # p1

Spec ==
    /\ Init
    /\ [][Next]_<<x, y, b>>
    /\ WF_{p \in MutexP}(DoP(p))_<<x, y, b>>
    /\ WF_{p \in MutexQ}(DoQ(p))_<<x, y, b>>
    /\ Stable(b)_[Next]

=============================================================================