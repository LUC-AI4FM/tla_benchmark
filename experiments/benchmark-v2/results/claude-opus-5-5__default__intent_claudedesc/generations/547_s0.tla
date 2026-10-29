--------------------------- MODULE OneBitMutex ---------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

Procs == 0 .. (N - 1)

VARIABLES
    flag,   \* flag[i] : the single shared bit owned by process i
    pc,     \* pc[i]   : control location of process i
    j       \* j[i]    : index of the process that process i is currently checking

vars == << flag, pc, j >>

Labels == {"ncs", "e1", "e2", "e3", "e4", "e5", "cs", "exit"}

TypeOK ==
    /\ flag \in [Procs -> BOOLEAN]
    /\ pc   \in [Procs -> Labels]
    /\ j    \in [Procs -> 0 .. N]

Init ==
    /\ flag = [i \in Procs |-> FALSE]
    /\ pc   = [i \in Procs |-> "ncs"]
    /\ j    = [i \in Procs |-> 0]

-----------------------------------------------------------------------------
(* Non-critical section: the process may stay here forever.               *)
NCS(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << flag, j >>

(* Entry: raise own flag and start checking from process 0.               *)
E1(self) ==
    /\ pc[self] = "e1"
    /\ flag' = [flag EXCEPT ![self] = TRUE]
    /\ j'    = [j EXCEPT ![self] = 0]
    /\ pc'   = [pc EXCEPT ![self] = "e2"]

(* Check lower-numbered processes in increasing order.                    *)
E2(self) ==
    /\ pc[self] = "e2"
    /\ IF j[self] < self
         THEN IF flag[j[self]]
                THEN /\ pc' = [pc EXCEPT ![self] = "e3"]
                     /\ UNCHANGED j
                ELSE /\ j'  = [j EXCEPT ![self] = j[self] + 1]
                     /\ pc' = [pc EXCEPT ![self] = "e2"]
         ELSE /\ j'  = [j EXCEPT ![self] = self + 1]
              /\ pc' = [pc EXCEPT ![self] = "e4"]
    /\ UNCHANGED flag

(* Conflict with a lower-numbered process: back off (lower own flag).     *)
E3(self) ==
    /\ pc[self] = "e3"
    /\ flag' = [flag EXCEPT ![self] = FALSE]
    /\ pc'   = [pc EXCEPT ![self] = "e5"]
    /\ UNCHANGED j

(* Wait for that lower-numbered process to lower its flag, then restart.  *)
E5(self) ==
    /\ pc[self] = "e5"
    /\ ~flag[j[self]]
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << flag, j >>

(* Check higher-numbered processes in increasing order, waiting for each. *)
E4(self) ==
    /\ pc[self] = "e4"
    /\ IF j[self] < N
         THEN /\ ~flag[j[self]]
              /\ j'  = [j EXCEPT ![self] = j[self] + 1]
              /\ pc' = [pc EXCEPT ![self] = "e4"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ UNCHANGED j
    /\ UNCHANGED flag

(* Critical section.                                                      *)
CS(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED << flag, j >>

(* Exit protocol: clear own flag.                                         *)
Exit(self) ==
    /\ pc[self] = "exit"
    /\ flag' = [flag EXCEPT ![self] = FALSE]
    /\ pc'   = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED j

(* All steps except leaving the non-critical section.                     *)
Protocol(self) ==
    \/ E1(self) \/ E2(self) \/ E3(self) \/ E4(self) \/ E5(self)
    \/ CS(self) \/ Exit(self)

Proc(self) == NCS(self) \/ Protocol(self)

Next == \E self \in Procs : Proc(self)

(* A process is never forced to leave its non-critical section, but once  *)
(* it has started the protocol it keeps taking steps (weak fairness).     *)
Fairness == \A self \in Procs : WF_vars(Protocol(self))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety: mutual exclusion.                                              *)
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

(* Liveness: deadlock freedom. If some process is trying to enter, then   *)
(* eventually some process is in its critical section.                    *)
Trying(i) == pc[i] \in {"e1", "e2", "e3", "e4", "e5"}

DeadlockFreedom ==
    (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : pc[i] = "cs")

(* A process in its critical section eventually releases it.              *)
EventuallyExits ==
    \A i \in Procs : (pc[i] = "cs") ~> (pc[i] = "ncs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadlockFreedom /\ EventuallyExits
=============================================================================