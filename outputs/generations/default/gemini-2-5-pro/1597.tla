---- MODULE LamportFast ----
EXTENDS Integers, FiniteSets, TLC

CONSTANTS N
ASSUME N \in Nat /\ N > 1

ProcSet == 1..N

VARIABLES x, y, b, pc, failed

vars == <<x, y, b, pc, failed>>

Proc1 == 1
Proc2N == 2..N

TypeOK ==
    /\ x \in (0..N)
    /\ y \in (0..N)
    /\ b \in [ProcSet -> BOOLEAN]
    /\ pc \in [ProcSet -> {"ncs", "start", "fast_check", "slow_set_b", "slow_wait", "cs", "exit"}]
    /\ failed \in [ProcSet -> BOOLEAN]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in ProcSet |-> FALSE]
    /\ pc = [i \in ProcSet |-> "ncs"]
    /\ failed = [i \in ProcSet |-> FALSE]

\* The action for a process `self` to move from the non-critical section
\* to the start of the mutual exclusion protocol.
P_ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, failed>>

\* Start of the protocol. Set flags and check for contention on y. This is the
\* first step of the fast path.
P_start(self) ==
    /\ pc[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ x' = self
    /\ IF y /= 0
       THEN /\ pc' = [pc EXCEPT ![self] = "slow_set_b"]
            /\ UNCHANGED <<y>>
       ELSE /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "fast_check"]
    /\ UNCHANGED <<failed>>

\* Check if the fast path was successful by re-reading x.
P_fast_check(self) ==
    /\ pc[self] = "fast_check"
    /\ IF x = self
       THEN pc' = [pc EXCEPT ![self] = "cs"]
       ELSE pc' = [pc EXCEPT ![self] = "slow_set_b"]
    /\ UNCHANGED <<x, y, b, failed>>

\* Start of the slow path: retract the intention to enter by setting b[self] to FALSE.
P_slow_set_b(self) ==
    /\ pc[self] = "slow_set_b"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "slow_wait"]
    /\ UNCHANGED <<x, y, failed>>

\* Slow path wait: wait until y is free, then retry the protocol from the start.
P_slow_wait(self) ==
    /\ pc[self] = "slow_wait"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, failed>>

\* A process in the critical section can choose to exit.
P_cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<x, y, b, failed>>

\* Exit protocol: release the lock by clearing y and b[self].
P_exit(self) ==
    /\ pc[self] = "exit"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<x, failed>>

\* Actions for the distinguished process 1.
P1(self) ==
    \/ P_ncs(self)
    \/ P_start(self)
    \/ P_fast_check(self)
    \/ P_slow_set_b(self)
    \/ P_slow_wait(self)
    \/ P_cs(self)
    \/ P_exit(self)

\* Actions for the family of processes 2..N.
P2N(self) ==
    \/ P_ncs(self)
    \/ P_start(self)
    \/ P_fast_check(self)
    \/ P_slow_set_b(self)
    \/ P_slow_wait(self)
    \/ P_cs(self)
    \/ P_exit(self)

\* The next-state relation. A non-failed process may take a step.
Next ==
    \/ (~failed[Proc1] /\ P1(Proc1))
    \/ (\E i \in Proc2N: ~failed[i] /\ P2N(i))

\* Fairness ensures that no process that is enabled forever is ignored forever.
Fairness ==
    /\ WF_vars(~failed[Proc1] /\ P1(Proc1))
    /\ \A i \in Proc2N: WF_vars(~failed[i] /\ P2N(i))

Spec == Init /\ [][Next]_vars /\ Fairness

\* --- PROPERTIES ---

\* Mutual exclusion invariant: at most one process is in the critical section.
MutualExclusion ==
    \A i, j \in ProcSet: (i /= j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Liveness property: Infinitely often, some process is in the critical section.
Liveness == []<>(\E i \in ProcSet: pc[i] = "cs")

=============================================================================