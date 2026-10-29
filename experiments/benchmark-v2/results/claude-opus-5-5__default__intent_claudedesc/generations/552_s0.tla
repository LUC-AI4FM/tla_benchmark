---------------------------- MODULE OneBitMutex ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat /\ N > 0

Procs == 0 .. (N - 1)

Labels == {"ncs", "e1", "e2", "e3", "e4", "e5", "cs", "f"}

VARIABLES
    x,      \* shared array of one-bit flags, one per process
    pc,     \* program counter of each process
    idx     \* index of the process currently being examined in the scan

vars == << x, pc, idx >>

TypeOK ==
    /\ x   \in [Procs -> BOOLEAN]
    /\ pc  \in [Procs -> Labels]
    /\ idx \in [Procs -> 0 .. N]

Init ==
    /\ x   = [p \in Procs |-> FALSE]
    /\ pc  = [p \in Procs |-> "ncs"]
    /\ idx = [p \in Procs |-> 0]

(***************************************************************************)
(* Non-critical section: a process may stay here forever.                 *)
(***************************************************************************)
NCS(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << x, idx >>

(***************************************************************************)
(* Entry: raise own flag and start scanning lower-numbered processes.      *)
(***************************************************************************)
E1(self) ==
    /\ pc[self] = "e1"
    /\ x'   = [x EXCEPT ![self] = TRUE]
    /\ idx' = [idx EXCEPT ![self] = 0]
    /\ pc'  = [pc EXCEPT ![self] = "e2"]

(***************************************************************************)
(* Scan lower-numbered processes in order.  On conflict, back off.         *)
(***************************************************************************)
E2(self) ==
    /\ pc[self] = "e2"
    /\ IF idx[self] < self
         THEN IF x[idx[self]]
                THEN /\ pc'  = [pc EXCEPT ![self] = "e3"]
                     /\ UNCHANGED << x, idx >>
                ELSE /\ idx' = [idx EXCEPT ![self] = idx[self] + 1]
                     /\ UNCHANGED << x, pc >>
         ELSE /\ idx' = [idx EXCEPT ![self] = self + 1]
              /\ pc'  = [pc EXCEPT ![self] = "e5"]
              /\ UNCHANGED x

(***************************************************************************)
(* Back off: clear own flag.                                               *)
(***************************************************************************)
E3(self) ==
    /\ pc[self] = "e3"
    /\ x'  = [x EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "e4"]
    /\ UNCHANGED idx

(***************************************************************************)
(* Wait until the conflicting lower-numbered process lowers its flag,      *)
(* then restart the entry protocol.                                        *)
(***************************************************************************)
E4(self) ==
    /\ pc[self] = "e4"
    /\ ~ x[idx[self]]
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << x, idx >>

(***************************************************************************)
(* Verify that no higher-numbered process has its flag set.                *)
(***************************************************************************)
E5(self) ==
    /\ pc[self] = "e5"
    /\ IF idx[self] < N
         THEN /\ ~ x[idx[self]]
              /\ idx' = [idx EXCEPT ![self] = idx[self] + 1]
              /\ UNCHANGED << x, pc >>
         ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ UNCHANGED << x, idx >>

(***************************************************************************)
(* Critical section.                                                       *)
(***************************************************************************)
CS(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "f"]
    /\ UNCHANGED << x, idx >>

(***************************************************************************)
(* Exit protocol: clear own flag.                                          *)
(***************************************************************************)
F(self) ==
    /\ pc[self] = "f"
    /\ x'  = [x EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED idx

(***************************************************************************)
(* All steps except leaving the non-critical section.                      *)
(***************************************************************************)
Trying(self) ==
    \/ E1(self) \/ E2(self) \/ E3(self) \/ E4(self)
    \/ E5(self) \/ CS(self) \/ F(self)

Proc(self) == NCS(self) \/ Trying(self)

Next == \E self \in Procs : Proc(self)

Fairness == \A self \in Procs : WF_vars(Trying(self))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety: mutual exclusion.                                               *)
(***************************************************************************)
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

(***************************************************************************)
(* Liveness: starvation freedom.                                           *)
(***************************************************************************)
StarvationFree ==
    \A p \in Procs : (pc[p] \in {"e1", "e2", "e3", "e4", "e5"}) ~> (pc[p] = "cs")

(***************************************************************************)
(* Weaker liveness: some trying process eventually enters.                 *)
(***************************************************************************)
DeadlockFree ==
    (\E p \in Procs : pc[p] \in {"e1", "e2", "e3", "e4", "e5"})
        ~> (\E p \in Procs : pc[p] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
=============================================================================