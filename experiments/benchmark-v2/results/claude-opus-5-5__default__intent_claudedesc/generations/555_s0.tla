---------------------------- MODULE SemaphoreMutex ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Procs == 0..(N - 1)

VARIABLES pc, sem

vars == <<pc, sem>>

States == {"ncs", "trying", "cs"}

TypeOK ==
    /\ pc \in [Procs -> States]
    /\ sem \in {0, 1}

Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ sem = 1

\* Process leaves its non-critical section and attempts to enter the CS
Try(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "trying"]
    /\ UNCHANGED sem

\* P operation (wait): atomically acquire the semaphore when it is available
Enter(p) ==
    /\ pc[p] = "trying"
    /\ sem = 1
    /\ sem' = 0
    /\ pc' = [pc EXCEPT ![p] = "cs"]

\* V operation (signal): release the semaphore and return to normal state
Exit(p) ==
    /\ pc[p] = "cs"
    /\ sem' = 1
    /\ pc' = [pc EXCEPT ![p] = "ncs"]

Proc(p) == Try(p) \/ Enter(p) \/ Exit(p)

Next == \E p \in Procs : Proc(p)

\* Processes in the CS eventually leave it (weak fairness on Exit).
\* The semaphore is fair: a process waiting on it that finds it available
\* infinitely often eventually acquires it (strong fairness on Enter).
\* No fairness on Try: a process may remain in its non-critical section forever.
Fairness ==
    \A p \in Procs :
        /\ WF_vars(Exit(p))
        /\ SF_vars(Enter(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

SemaphoreConsistency ==
    (sem = 1) <=> (\A p \in Procs : pc[p] # "cs")

AtMostOneInCS ==
    Cardinality({p \in Procs : pc[p] = "cs"}) <= 1

-----------------------------------------------------------------------------
\* Liveness properties

DeadlockFreedom ==
    (\E p \in Procs : pc[p] = "trying") ~> (\E p \in Procs : pc[p] = "cs")

StarvationFreedom ==
    \A p \in Procs : (pc[p] = "trying") ~> (pc[p] = "cs")

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ MutualExclusion /\ SemaphoreConsistency /\ AtMostOneInCS)
THEOREM Spec => DeadlockFreedom /\ StarvationFreedom

=============================================================================