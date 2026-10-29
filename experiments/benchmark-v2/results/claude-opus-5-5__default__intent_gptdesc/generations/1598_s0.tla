------------------------------ MODULE FastMutex ------------------------------
(***************************************************************************)
(* Lamport's fast mutual-exclusion algorithm for N processes, with         *)
(* spinning and back-off/retry.                                            *)
(*                                                                         *)
(* Shared state:                                                           *)
(*   x, y : two shared "tour" registers. Each holds a process id, or 0     *)
(*          meaning "none".                                                *)
(*   b    : per-process boolean intent flags.                              *)
(* Local state:                                                            *)
(*   pc   : control location of each process.                              *)
(*   j    : loop index used while a process spins on the others' flags.    *)
(*                                                                         *)
(* Protocol of process i (control locations in brackets):                  *)
(*   [ncs]   noncritical section                                           *)
(*   [start] b[i] := TRUE                                                  *)
(*   [l1]    x := i                                                        *)
(*   [l2]    IF y # 0 THEN b[i] := FALSE ; goto l3  ELSE goto l4           *)
(*   [l3]    await y = 0 ; goto start                         (retry)      *)
(*   [l4]    y := i                                                        *)
(*   [l5]    IF x # i THEN b[i] := FALSE ; j := 1 ; goto l6                *)
(*           ELSE goto cs                                     (fast path)  *)
(*   [l6]    FOR j IN 1..N : await ~b[j]                      (spin)       *)
(*   [l7]    IF y # i THEN goto l8 ELSE goto cs                            *)
(*   [l8]    await y = 0 ; goto start                         (retry)      *)
(*   [cs]    critical section                                              *)
(*   [l9]    y := 0                                           (cleanup)    *)
(*   [l10]   b[i] := FALSE ; goto ncs                         (cleanup)    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat /\ N > 0

ProcSet == 1..N

VARIABLES x, y, b, pc, j

vars == << x, y, b, pc, j >>

Labels == {"ncs", "start", "l1", "l2", "l3", "l4", "l5",
           "l6", "l7", "l8", "cs", "l9", "l10"}

TypeOK ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ b \in [ProcSet -> BOOLEAN]
    /\ pc \in [ProcSet -> Labels]
    /\ j \in [ProcSet -> 1..(N+1)]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in ProcSet |-> FALSE]
    /\ pc = [i \in ProcSet |-> "ncs"]
    /\ j = [i \in ProcSet |-> 1]

-----------------------------------------------------------------------------
(* Actions of process self *)

\* Leave the noncritical section and begin an entry attempt.
\* (Not subject to fairness: a process may stay in its NCS forever.)
Ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, j >>

\* Set the local intent flag.
Start(self) ==
    /\ pc[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "l1"]
    /\ UNCHANGED << x, y, j >>

\* Write the first tour register.
L1(self) ==
    /\ pc[self] = "l1"
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "l2"]
    /\ UNCHANGED << y, b, j >>

\* Read the second tour register; if occupied, withdraw intent and back off.
L2(self) ==
    /\ pc[self] = "l2"
    /\ IF y # 0
          THEN /\ b' = [b EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "l3"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "l4"]
               /\ b' = b
    /\ UNCHANGED << x, y, j >>

\* Wait until the second register is free, then retry from the start.
L3(self) ==
    /\ pc[self] = "l3"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, j >>

\* Write the second tour register.
L4(self) ==
    /\ pc[self] = "l4"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "l5"]
    /\ UNCHANGED << x, b, j >>

\* Re-read the first register: fast path if unchanged, otherwise slow path.
L5(self) ==
    /\ pc[self] = "l5"
    /\ IF x # self
          THEN /\ b' = [b EXCEPT ![self] = FALSE]
               /\ j' = [j EXCEPT ![self] = 1]
               /\ pc' = [pc EXCEPT ![self] = "l6"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
               /\ UNCHANGED << b, j >>
    /\ UNCHANGED << x, y >>

\* Spin on every process's intent flag in turn.
L6(self) ==
    /\ pc[self] = "l6"
    /\ IF j[self] <= N
          THEN /\ ~b[j[self]]
               /\ j' = [j EXCEPT ![self] = j[self] + 1]
               /\ pc' = pc
          ELSE /\ pc' = [pc EXCEPT ![self] = "l7"]
               /\ j' = j
    /\ UNCHANGED << x, y, b >>

\* Check whether we still own the second register.
L7(self) ==
    /\ pc[self] = "l7"
    /\ IF y # self
          THEN pc' = [pc EXCEPT ![self] = "l8"]
          ELSE pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << x, y, b, j >>

\* Lost the race: wait for the register to clear, then retry.
L8(self) ==
    /\ pc[self] = "l8"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, j >>

\* Critical section.
CS(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "l9"]
    /\ UNCHANGED << x, y, b, j >>

\* Cleanup: reset the second register.
L9(self) ==
    /\ pc[self] = "l9"
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![self] = "l10"]
    /\ UNCHANGED << x, b, j >>

\* Cleanup: withdraw intent and restart the loop.
L10(self) ==
    /\ pc[self] = "l10"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED << x, y, j >>

\* All steps other than leaving the noncritical section.
Trying(self) ==
    \/ Start(self) \/ L1(self) \/ L2(self) \/ L3(self) \/ L4(self)
    \/ L5(self)    \/ L6(self) \/ L7(self) \/ L8(self)
    \/ CS(self)    \/ L9(self) \/ L10(self)

Proc(self) == Ncs(self) \/ Trying(self)

Next == \E self \in ProcSet : Proc(self)

Fairness == \A self \in ProcSet : WF_vars(Trying(self))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

InCS(i) == pc[i] = "cs"

\* Safety: no two distinct processes are in the critical section at once.
MutualExclusion ==
    \A p, q \in ProcSet : (p # q) => ~(InCS(p) /\ InCS(q))

TryingSet == Labels \ {"ncs", "cs", "l9", "l10"}

\* System-wide liveness (deadlock freedom): if some process is trying to
\* enter, then eventually some process enters the critical section.
DeadlockFreedom ==
    (\E i \in ProcSet : pc[i] \in TryingSet) ~> (\E i \in ProcSet : InCS(i))

\* While processes keep trying, some process enters infinitely often.
InfinitelyOftenEntry ==
    ([]<>(\E i \in ProcSet : pc[i] \in TryingSet))
        => []<>(\E i \in ProcSet : InCS(i))

\* Optional per-process starvation freedom. Lamport's fast mutex does NOT
\* guarantee this, and a model checker is expected to produce a
\* counterexample. It is included for completeness.
StarvationFreedom ==
    \A i \in ProcSet : (pc[i] \in TryingSet) ~> InCS(i)

THEOREM Spec => []TypeOK
THEOREM Spec => []MutualExclusion
THEOREM Spec => DeadlockFreedom
THEOREM Spec => InfinitelyOftenEntry
=============================================================================