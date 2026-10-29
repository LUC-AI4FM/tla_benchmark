---------------------------- MODULE OneBitMutex ----------------------------
(***************************************************************************)
(* Lamport's one-bit mutual exclusion algorithm for N processes            *)
(* (processes 0..N-1). Each process owns one Boolean flag x[i] and a local *)
(* index j[i] in 0..N. A process cycles through noncritical section,       *)
(* entry protocol, critical section and exit. In the entry protocol it     *)
(* scans lower-numbered processes: if one has its flag raised, it backs    *)
(* off. Backing off means clearing its own flag, waiting for that flag to  *)
(* clear, and restarting. This avoids livelock. It then waits for every    *)
(* higher-numbered process to lower its flag.                              *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 1

Procs == 0 .. (N - 1)

VARIABLES x,   \* x[i] : the single Boolean flag of process i
          j,   \* j[i] : local index of process i, in 0..N
          pc   \* pc[i]: control location of process i

vars == << x, j, pc >>

Labels  == {"ncs", "e1", "e2", "e3", "e4", "e5", "e6", "cs", "ex"}
Trying  == {"e1", "e2", "e3", "e4", "e5", "e6"}

-----------------------------------------------------------------------------
Init == /\ x  = [i \in Procs |-> FALSE]
        /\ j  = [i \in Procs |-> 0]
        /\ pc = [i \in Procs |-> "ncs"]

(* Noncritical work; a process may stay here forever (no fairness). *)
ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED << x, j >>

(* Raise own flag and reset the scan pointer. *)
e1(self) == /\ pc[self] = "e1"
            /\ x' = [x EXCEPT ![self] = TRUE]
            /\ j' = [j EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "e2"]

(* Scan lower-numbered processes. *)
e2(self) == /\ pc[self] = "e2"
            /\ IF j[self] < self
                 THEN IF x[j[self]]
                        THEN /\ pc' = [pc EXCEPT ![self] = "e3"]
                             /\ UNCHANGED j
                        ELSE /\ j' = [j EXCEPT ![self] = j[self] + 1]
                             /\ pc' = [pc EXCEPT ![self] = "e2"]
                 ELSE /\ j' = [j EXCEPT ![self] = self + 1]
                      /\ pc' = [pc EXCEPT ![self] = "e5"]
            /\ UNCHANGED x

(* Back off: momentarily clear own flag. *)
e3(self) == /\ pc[self] = "e3"
            /\ x' = [x EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "e4"]
            /\ UNCHANGED j

(* Wait for the conflicting lower-numbered flag to clear, then retry. *)
e4(self) == /\ pc[self] = "e4"
            /\ ~ x[j[self]]
            /\ pc' = [pc EXCEPT ![self] = "e1"]
            /\ UNCHANGED << x, j >>

(* Loop over higher-numbered processes. *)
e5(self) == /\ pc[self] = "e5"
            /\ IF j[self] < N
                 THEN pc' = [pc EXCEPT ![self] = "e6"]
                 ELSE pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, j >>

(* Wait for a higher-numbered flag to become false, then advance. *)
e6(self) == /\ pc[self] = "e6"
            /\ ~ x[j[self]]
            /\ j' = [j EXCEPT ![self] = j[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "e5"]
            /\ UNCHANGED x

(* Critical action. *)
cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "ex"]
            /\ UNCHANGED << x, j >>

(* Exit: clear the flag and the local state. *)
ex(self) == /\ pc[self] = "ex"
            /\ x' = [x EXCEPT ![self] = FALSE]
            /\ j' = [j EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "ncs"]

(* All steps of the protocol other than leaving the noncritical section. *)
Protocol(self) == e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
                  \/ e5(self) \/ e6(self) \/ cs(self) \/ ex(self)

Proc(self) == ncs(self) \/ Protocol(self)

(* Interleaving: exactly one process takes a step at a time. *)
Next == \E self \in Procs : Proc(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(Protocol(self))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
TypeOK == /\ x  \in [Procs -> BOOLEAN]
          /\ j  \in [Procs -> 0 .. N]
          /\ pc \in [Procs -> Labels]

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~ (pc[p] = "cs" /\ pc[q] = "cs")

(* A process is in the critical section only after completing the entry *)
(* protocol: its flag is raised and its pointer has passed all processes. *)
EntryCompleted ==
    \A p \in Procs : (pc[p] \in {"cs", "ex"}) => (x[p] /\ j[p] = N)

(* Inductive strengthening (Lamport): a process past the lower scan with *)
(* its flag raised has priority over the processes it has already passed. *)
InScan(p) == pc[p] \in {"e5", "e6", "cs", "ex"}

Passed(p, q) ==
    \/ q < p
    \/ /\ q > p
       /\ \/ pc[p] \in {"cs", "ex"}
          \/ (pc[p] \in {"e5", "e6"} /\ q < j[p])

FlagsConsistent ==
    \A p \in Procs :
        /\ (pc[p] \in {"e2", "e5", "e6", "cs", "ex", "e3"}) => x[p]
        /\ (pc[p] \in {"ncs", "e1", "e4"}) => ~ x[p]
        /\ (pc[p] \in {"e2"}) => j[p] <= p
        /\ (pc[p] \in {"e3", "e4"}) => j[p] < p
        /\ (pc[p] \in {"e5", "e6"}) => (j[p] > p /\ j[p] <= N)
        /\ (pc[p] = "e6") => j[p] < N

Inv == /\ TypeOK
       /\ FlagsConsistent
       /\ EntryCompleted
       /\ \A p, q \in Procs :
             (p # q /\ InScan(p) /\ Passed(p, q)) =>
                 ~ (InScan(q) /\ Passed(q, p))
       /\ MutualExclusion

(* Absence of deadlock: some process always has an enabled step. *)
DeadlockFree == \E p \in Procs : ENABLED Proc(p)

THEOREM Safety == Spec => [](TypeOK /\ MutualExclusion /\ EntryCompleted)
THEOREM NoDeadlock == Spec => []DeadlockFree

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
(* Global progress: if some process is trying, some process eventually *)
(* enters the critical section.                                         *)
DeadlockFreedom ==
    (\E p \in Procs : pc[p] \in Trying) ~> (\E p \in Procs : pc[p] = "cs")

(* If the other processes eventually stop trying for good (they remain in  *)
(* the noncritical section), then a requesting process eventually enters. *)
OthersStop(p) == <>[](\A q \in Procs \ {p} : pc[q] = "ncs")

NoStarvationWhenOthersStop ==
    \A p \in Procs :
        OthersStop(p) => [](pc[p] \in Trying => <>(pc[p] = "cs"))

(* Each process that enters the critical section eventually leaves it. *)
CSExits == \A p \in Procs : (pc[p] = "cs") ~> (pc[p] = "ncs")

THEOREM Liveness == Spec => /\ DeadlockFreedom
                            /\ NoStarvationWhenOthersStop
                            /\ CSExits
=============================================================================