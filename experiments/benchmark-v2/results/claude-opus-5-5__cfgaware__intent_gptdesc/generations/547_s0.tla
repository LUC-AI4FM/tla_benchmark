------------------------------ MODULE OneBitMutex ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 1

Procs == 1..N

VARIABLES flag, j, pc

vars == << flag, j, pc >>

Labels == {"ncs", "e1", "e2", "e3", "e4", "e5", "cs", "f"}

-----------------------------------------------------------------------------
Init ==
    /\ flag = [p \in Procs |-> FALSE]
    /\ j    = [p \in Procs |-> 0]
    /\ pc   = [p \in Procs |-> "ncs"]

\* Noncritical section: the process may decide to try to enter.
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << flag, j >>

\* Assert own flag and start scanning lower-numbered processes.
e1(self) ==
    /\ pc[self] = "e1"
    /\ flag' = [flag EXCEPT ![self] = TRUE]
    /\ j' = [j EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "e2"]

\* Scan lower-numbered processes; on finding a raised flag, back off.
e2(self) ==
    /\ pc[self] = "e2"
    /\ IF j[self] < self
          THEN IF flag[j[self]]
                  THEN /\ pc' = [pc EXCEPT ![self] = "e3"]
                       /\ UNCHANGED << flag, j >>
                  ELSE /\ j' = [j EXCEPT ![self] = j[self] + 1]
                       /\ UNCHANGED << flag, pc >>
          ELSE IF self = N
                  THEN /\ j' = [j EXCEPT ![self] = 0]
                       /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ UNCHANGED flag
                  ELSE /\ j' = [j EXCEPT ![self] = self + 1]
                       /\ pc' = [pc EXCEPT ![self] = "e5"]
                       /\ UNCHANGED flag

\* Momentarily clear own flag (back off to avoid livelock).
e3(self) ==
    /\ pc[self] = "e3"
    /\ flag' = [flag EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "e4"]
    /\ UNCHANGED j

\* Wait for the lower-numbered process's flag to become false, then retry.
e4(self) ==
    /\ pc[self] = "e4"
    /\ ~flag[j[self]]
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << flag, j >>

\* Wait for each higher-numbered process's flag to become false.
e5(self) ==
    /\ pc[self] = "e5"
    /\ ~flag[j[self]]
    /\ IF j[self] = N
          THEN /\ j' = [j EXCEPT ![self] = 0]
               /\ pc' = [pc EXCEPT ![self] = "cs"]
          ELSE /\ j' = [j EXCEPT ![self] = j[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = "e5"]
    /\ UNCHANGED flag

\* Critical section action.
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "f"]
    /\ UNCHANGED << flag, j >>

\* Exit: clear own flag and local state.
f(self) ==
    /\ pc[self] = "f"
    /\ flag' = [flag EXCEPT ![self] = FALSE]
    /\ j' = [j EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]

Proc(self) ==
    \/ ncs(self) \/ e1(self) \/ e2(self) \/ e3(self)
    \/ e4(self) \/ e5(self) \/ cs(self) \/ f(self)

\* All steps except leaving the noncritical section.
ProtocolStep(self) ==
    \/ e1(self) \/ e2(self) \/ e3(self)
    \/ e4(self) \/ e5(self) \/ cs(self) \/ f(self)

Next == \E self \in Procs : Proc(self)

Fairness == \A self \in Procs : WF_vars(ProtocolStep(self))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Properties

TypeOK ==
    /\ flag \in [Procs -> BOOLEAN]
    /\ j \in [Procs -> 0..N]
    /\ pc \in [Procs -> Labels]

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* A process in the critical section has completed the entry protocol:
\* its flag is raised and its scan index has been reset.
EntryCompleted ==
    \A p \in Procs : pc[p] \in {"cs", "f"} => (flag[p] /\ j[p] = 0)

\* Index is meaningful (points to another process) during scanning/waiting.
IndexOK ==
    \A p \in Procs :
        /\ pc[p] \in {"e3", "e4"} => (j[p] \in 1..(p-1))
        /\ pc[p] = "e5" => (j[p] \in (p+1)..N)

\* Some step is always enabled (no deadlock).
NoDeadlock == ENABLED Next

Trying(p) == pc[p] \in {"e1", "e2", "e3", "e4", "e5"}

\* Deadlock freedom: if some process is trying, some process eventually enters.
DeadlockFreedom ==
    (\E p \in Procs : Trying(p)) ~> (\E p \in Procs : pc[p] = "cs")

\* If others eventually stop trying (stay in ncs), a trying process enters.
StarvationFreedomUnderQuiescence ==
    \A p \in Procs :
        (Trying(p) /\ <>[](\A q \in Procs \ {p} : pc[q] = "ncs"))
            ~> (pc[p] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion /\ EntryCompleted /\ IndexOK)
THEOREM Spec => DeadlockFreedom
=============================================================================