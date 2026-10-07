------------------------------- MODULE FastMutex -------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N
ASSUME N \in Nat /\ N >= 2

VARIABLES x, y, b, failed, j, j2, failed2

Proc1 == 1
Proc2(i) == i \in 2..N
Procs == {Proc1} \cup {Proc2(i) : i \in 2..N}

Init == /\ x = 0
        /\ y = 0
        /\ b = [p \in Procs |-> FALSE]
        /\ failed = [p \in Procs |-> FALSE]
        /\ j = [p \in Procs |-> 1]
        /\ j2 = [p \in Procs |-> 1]
        /\ failed2 = [p \in Procs |-> FALSE]

FastMutexEntry(p) ==
    /\ b' = [b EXCEPT ![p] = TRUE]
    /\ x' = p
    /\ IF y # 0 THEN
           /\ y' = y
           /\ failed' = [failed EXCEPT ![p] = TRUE]
       ELSE
           /\ y' = p
           /\ IF x # p THEN
                  /\ b'[p] = FALSE
                  /\ failed2' = [failed2 EXCEPT ![p] = TRUE]
              ELSE
                  /\ failed' = [failed EXCEPT ![p] = FALSE]

FastMutexWait(p) ==
    /\ \A q \in Procs \ {p} : /\ IF b[q] THEN j'[q] = (j[q] + 1) % N ELSE j'[q] = j[q]
    /\ failed2' = [failed2 EXCEPT ![p] = FALSE]

FastMutexCheck(p) ==
    /\ IF y # p THEN
           /\ failed' = [failed EXCEPT ![p] = TRUE]
       ELSE
           /\ failed' = [failed EXCEPT ![p] = FALSE]

FastMutexExit(p) ==
    /\ y' = 0
    /\ b'[p] = FALSE

Next ==
    \E p \in Procs :
        \/ /\ failed[p]
           /\ FastMutexWait(p)
        \/ /\ ~failed[p]
           /\ FastMutexEntry(p)
        \/ /\ failed2[p]
           /\ FastMutexCheck(p)
        \/ /\ ~failed[p] /\ ~failed2[p]
           /\ FastMutexExit(p)

Spec ==
    /\ Init
    /\ [][Next]_<<Procs>>
    /\ WF_next(<<Procs>>)

Invariant ==
    \A p, q \in Procs : p # q => ~(failed[p] = FALSE /\ failed[q] = FALSE)

Liveness ==
    <>[](\E p \in Procs : failed[p] = FALSE)

=============================================================================