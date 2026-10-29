---------------------------- MODULE MCSession9onebit ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the one-bit mutual exclusion algorithm.      *)
(* The original wrapper EXTENDS Session9onebit. So that this module parses *)
(* on its own, the one-bit algorithm from Session9onebit is included here. *)
(* The algorithm's state variables are pc and flag.                        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, Procs

(***************************************************************************)
(* Concrete model constants: three processes, 0..2.                        *)
(***************************************************************************)
ConstN     == 3
ConstProcs == 0 .. (ConstN - 1)

ASSUME Procs \subseteq Nat

VARIABLES pc, flag

vars == << pc, flag >>

Labels == {"ncs", "e1", "e2", "e3", "e4", "cs"}

Trying == {"e1", "e2", "e3", "e4"}

TypeOK ==
    /\ pc   \in [Procs -> Labels]
    /\ flag \in [Procs -> BOOLEAN]

Init ==
    /\ pc   = [i \in Procs |-> "ncs"]
    /\ flag = [i \in Procs |-> FALSE]

(***************************************************************************)
(* The one-bit algorithm (Burns / Lamport).                                *)
(***************************************************************************)
NCS(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED flag

E1(self) ==
    /\ pc[self] = "e1"
    /\ flag' = [flag EXCEPT ![self] = TRUE]
    /\ pc'   = [pc EXCEPT ![self] = "e2"]

E2(self) ==
    /\ pc[self] = "e2"
    /\ IF \E j \in Procs : j < self /\ flag[j]
         THEN /\ flag' = [flag EXCEPT ![self] = FALSE]
              /\ pc'   = [pc EXCEPT ![self] = "e3"]
         ELSE /\ pc'   = [pc EXCEPT ![self] = "e4"]
              /\ UNCHANGED flag

E3(self) ==
    /\ pc[self] = "e3"
    /\ \A j \in Procs : j < self => ~flag[j]
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED flag

E4(self) ==
    /\ pc[self] = "e4"
    /\ \A j \in Procs : j > self => ~flag[j]
    /\ pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED flag

CS(self) ==
    /\ pc[self] = "cs"
    /\ flag' = [flag EXCEPT ![self] = FALSE]
    /\ pc'   = [pc EXCEPT ![self] = "ncs"]

(* Every step except leaving the noncritical section must be fair. *)
Rest(self) == E1(self) \/ E2(self) \/ E3(self) \/ E4(self) \/ CS(self)

proc(self) == NCS(self) \/ Rest(self)

Next == \E self \in Procs : proc(self)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in Procs : WF_vars(Rest(self))

(***************************************************************************)
(* Safety                                                                  *)
(***************************************************************************)
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)
(* Deadlock/livelock freedom: if some process is trying to enter, then     *)
(* some process eventually reaches the critical section.                   *)
DeadlockFree ==
    (\E i \in Procs : pc[i] \in Trying) ~> (\E i \in Procs : pc[i] = "cs")

(* Starvation freedom for process 0. *)
NoStarveProc0 ==
    (pc[0] \in Trying) ~> (pc[0] = "cs")

(* Starvation freedom for process 1.                                       *)
(* NOTE: NoStarveProc1 is NOT satisfied by the one-bit algorithm.          *)
NoStarveProc1 ==
    (pc[1] \in Trying) ~> (pc[1] = "cs")

THEOREM Spec => []TypeOK
THEOREM Spec => []MutualExclusion
THEOREM Spec => DeadlockFree
THEOREM Spec => NoStarveProc0
=============================================================================