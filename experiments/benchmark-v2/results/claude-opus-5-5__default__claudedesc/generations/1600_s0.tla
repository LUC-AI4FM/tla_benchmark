------------------------------- MODULE FastMutex -------------------------------
(***************************************************************************)
(* Lamport's Fast Mutual Exclusion algorithm for N processes.              *)
(*                                                                         *)
(* Shared variables:                                                       *)
(*   x : last writer of the "claim" register                               *)
(*   y : the "winner" register (0 means free)                              *)
(*   b : Boolean array of flags, b[i] = TRUE iff process i is competing    *)
(* Local (per-process) variables:                                          *)
(*   j      : loop counter                                                 *)
(*   failed : TRUE iff the process lost the race                           *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 1

ProcSet == 1..N

VARIABLES x, y, b, j, failed, pc

vars == << x, y, b, j, failed, pc >>

TypeOK ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ b \in [ProcSet -> BOOLEAN]
    /\ j \in [ProcSet -> 0..(N+1)]
    /\ failed \in [ProcSet -> BOOLEAN]
    /\ pc \in [ProcSet -> {"ncs", "start", "l1", "l2", "l3", "l4", "l5",
                           "l6", "l7", "l8", "l9", "l10", "cs", "l11", "l12"}]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in ProcSet |-> FALSE]
    /\ j = [i \in ProcSet |-> 0]
    /\ failed = [i \in ProcSet |-> FALSE]
    /\ pc = [i \in ProcSet |-> "ncs"]

(* Noncritical section *)
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, j, failed >>

(* Raise flag *)
start(self) ==
    /\ pc[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "l1"]
    /\ UNCHANGED << x, y, j, failed >>

(* Write identity to x *)
l1(self) ==
    /\ pc[self] = "l1"
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "l2"]
    /\ UNCHANGED << y, b, j, failed >>

(* Check whether y is nonzero *)
l2(self) ==
    /\ pc[self] = "l2"
    /\ IF y # 0
          THEN pc' = [pc EXCEPT ![self] = "l3"]
          ELSE pc' = [pc EXCEPT ![self] = "l5"]
    /\ UNCHANGED << x, y, b, j, failed >>

(* Back off: lower flag *)
l3(self) ==
    /\ pc[self] = "l3"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "l4"]
    /\ UNCHANGED << x, y, j, failed >>

(* Wait for y to clear, then restart *)
l4(self) ==
    /\ pc[self] = "l4"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, j, failed >>

(* Write y *)
l5(self) ==
    /\ pc[self] = "l5"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "l6"]
    /\ UNCHANGED << x, b, j, failed >>

(* Check whether x still holds own identity *)
l6(self) ==
    /\ pc[self] = "l6"
    /\ IF x # self
          THEN pc' = [pc EXCEPT ![self] = "l7"]
          ELSE pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << x, y, b, j, failed >>

(* Clear own flag and initialize loop counter *)
l7(self) ==
    /\ pc[self] = "l7"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ j' = [j EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "l8"]
    /\ UNCHANGED << x, y, failed >>

(* Wait for all flags to drop *)
l8(self) ==
    /\ pc[self] = "l8"
    /\ IF j[self] <= N
          THEN /\ ~b[j[self]]
               /\ j' = [j EXCEPT ![self] = j[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = "l8"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "l9"]
               /\ UNCHANGED j
    /\ UNCHANGED << x, y, b, failed >>

(* Check whether y still belongs to self *)
l9(self) ==
    /\ pc[self] = "l9"
    /\ IF y # self
          THEN pc' = [pc EXCEPT ![self] = "l10"]
          ELSE pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << x, y, b, j, failed >>

(* Wait for y = 0 and mark as failed *)
l10(self) ==
    /\ pc[self] = "l10"
    /\ y = 0
    /\ failed' = [failed EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << x, y, b, j >>

(* Critical section (entered only if not failed) *)
cs(self) ==
    /\ pc[self] = "cs"
    /\ IF ~failed[self]
          THEN /\ pc' = [pc EXCEPT ![self] = "l11"]
               /\ UNCHANGED failed
          ELSE /\ failed' = [failed EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, j >>

(* Clear y *)
l11(self) ==
    /\ pc[self] = "l11"
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![self] = "l12"]
    /\ UNCHANGED << x, b, j, failed >>

(* Clear own flag and loop *)
l12(self) ==
    /\ pc[self] = "l12"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED << x, y, j, failed >>

Proc(self) ==
    \/ ncs(self) \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self)
    \/ l4(self) \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self)
    \/ l9(self) \/ l10(self) \/ cs(self) \/ l11(self) \/ l12(self)

Next == \E self \in ProcSet : Proc(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in ProcSet : WF_vars(Proc(self))

-----------------------------------------------------------------------------
(* Helper predicates (used for TLC postcondition state counting) *)

InCS(i) == pc[i] = "cs" /\ ~failed[i]

SomeoneInCS == \E i \in ProcSet : InCS(i)

Contention == \A i \in ProcSet : pc[i] = "l8"

(* Safety: mutual exclusion *)
Invariant ==
    \A i, k \in ProcSet : (i # k) => ~(InCS(i) /\ InCS(k))

(* Liveness: some process is repeatedly in the critical section *)
Liveness == []<>SomeoneInCS

=============================================================================