---------------------------- MODULE MCSession9sem ----------------------------
EXTENDS Naturals, TLC

\* Model-checking wrapper for the Session9sem semaphore-based mutual exclusion
\* protocol. The underlying protocol is inlined so the module parses standalone.

CONSTANT N

ConstN == 3

ProcSet == 0..(ConstN-1)

VARIABLES sem, pc

vars == << sem, pc >>

TypeOK ==
    /\ sem \in {0, 1}
    /\ pc \in [ProcSet -> {"ncs", "enter", "cs", "exit"}]

Init ==
    /\ sem = 1
    /\ pc = [p \in ProcSet |-> "ncs"]

\* Non-critical section: decide to try to enter
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "enter"]
    /\ UNCHANGED sem

\* P(sem): wait until the semaphore is available, then acquire it
enter(self) ==
    /\ pc[self] = "enter"
    /\ sem > 0
    /\ sem' = sem - 1
    /\ pc' = [pc EXCEPT ![self] = "cs"]

\* Critical section
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED sem

\* V(sem): release the semaphore
exit(self) ==
    /\ pc[self] = "exit"
    /\ sem' = sem + 1
    /\ pc' = [pc EXCEPT ![self] = "ncs"]

proc(self) == enter(self) \/ cs(self) \/ exit(self) \/ ncs(self)

Next == \E self \in ProcSet : proc(self)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in ProcSet :
          /\ WF_vars(cs(self))
          /\ WF_vars(exit(self))
          /\ SF_vars(enter(self))

-----------------------------------------------------------------------------
\* Safety: mutual exclusion
MutualExclusion ==
    \A i, j \in ProcSet : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Liveness: deadlock/livelock freedom
DeadlockFree ==
    (\E i \in ProcSet : pc[i] = "enter") ~> (\E j \in ProcSet : pc[j] = "cs")

\* Liveness: starvation freedom
StarvationFree ==
    \A i \in ProcSet : (pc[i] = "enter") ~> (pc[i] = "cs")

THEOREM Spec => []TypeOK
THEOREM Spec => []MutualExclusion
THEOREM Spec => DeadlockFree
THEOREM Spec => StarvationFree
=============================================================================