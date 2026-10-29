---------------------------- MODULE FastMutex ----------------------------
(***************************************************************************)
(* Lamport's fast mutual-exclusion algorithm for N processes, using only   *)
(* atomic read/write registers.                                            *)
(*                                                                         *)
(* Shared variables:                                                       *)
(*   x, y : scalar registers holding a process id or 0                     *)
(*   b[i] : one Boolean flag per process                                   *)
(* Local variables (per process):                                          *)
(*   pc[i] : program counter                                               *)
(*   j[i]  : loop index bounded by 1..N+1                                  *)
(* All variables range over finite domains, so no unbounded counters or    *)
(* queues are used.                                                        *)
(*                                                                         *)
(* Algorithm, per process self:                                            *)
(*   ncs:   noncritical section (may stay here forever; not fair)          *)
(*   start: b[self] := TRUE                                                *)
(*   l1:    x := self                                                      *)
(*   l2:    if y # 0 then goto l3 else goto l5                             *)
(*   l3:    b[self] := FALSE                                               *)
(*   l4:    await y = 0 ; goto start                                       *)
(*   l5:    y := self                                                      *)
(*   l6:    if x # self then goto l7 else goto cs                          *)
(*   l7:    b[self] := FALSE ; j := 1                                      *)
(*   l8:    while j <= N do (await ~b[j] ; j := j + 1)                     *)
(*   l9:    if y # self then goto l10 else goto cs                         *)
(*   l10:   await y = 0 ; goto start                                       *)
(*   cs:    critical section                                               *)
(*   l11:   y := 0                                                         *)
(*   l12:   b[self] := FALSE ; goto ncs                                    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat /\ N > 0

ProcSet == 1..N

VARIABLES x, y, b, j, pc

vars == << x, y, b, j, pc >>

Labels == {"ncs", "start", "l1", "l2", "l3", "l4", "l5", "l6",
           "l7", "l8", "l9", "l10", "cs", "l11", "l12"}

TypeOK ==
  /\ x \in 0..N
  /\ y \in 0..N
  /\ b \in [ProcSet -> BOOLEAN]
  /\ j \in [ProcSet -> 0..(N+1)]
  /\ pc \in [ProcSet -> Labels]

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in ProcSet |-> FALSE]
  /\ j = [i \in ProcSet |-> 0]
  /\ pc = [i \in ProcSet |-> "ncs"]

ncs(self) ==
  /\ pc[self] = "ncs"
  /\ pc' = [pc EXCEPT ![self] = "start"]
  /\ UNCHANGED << x, y, b, j >>

start(self) ==
  /\ pc[self] = "start"
  /\ b' = [b EXCEPT ![self] = TRUE]
  /\ pc' = [pc EXCEPT ![self] = "l1"]
  /\ UNCHANGED << x, y, j >>

l1(self) ==
  /\ pc[self] = "l1"
  /\ x' = self
  /\ pc' = [pc EXCEPT ![self] = "l2"]
  /\ UNCHANGED << y, b, j >>

l2(self) ==
  /\ pc[self] = "l2"
  /\ IF y # 0
       THEN pc' = [pc EXCEPT ![self] = "l3"]
       ELSE pc' = [pc EXCEPT ![self] = "l5"]
  /\ UNCHANGED << x, y, b, j >>

l3(self) ==
  /\ pc[self] = "l3"
  /\ b' = [b EXCEPT ![self] = FALSE]
  /\ pc' = [pc EXCEPT ![self] = "l4"]
  /\ UNCHANGED << x, y, j >>

l4(self) ==
  /\ pc[self] = "l4"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![self] = "start"]
  /\ UNCHANGED << x, y, b, j >>

l5(self) ==
  /\ pc[self] = "l5"
  /\ y' = self
  /\ pc' = [pc EXCEPT ![self] = "l6"]
  /\ UNCHANGED << x, b, j >>

l6(self) ==
  /\ pc[self] = "l6"
  /\ IF x # self
       THEN pc' = [pc EXCEPT ![self] = "l7"]
       ELSE pc' = [pc EXCEPT ![self] = "cs"]
  /\ UNCHANGED << x, y, b, j >>

l7(self) ==
  /\ pc[self] = "l7"
  /\ b' = [b EXCEPT ![self] = FALSE]
  /\ j' = [j EXCEPT ![self] = 1]
  /\ pc' = [pc EXCEPT ![self] = "l8"]
  /\ UNCHANGED << x, y >>

l8(self) ==
  /\ pc[self] = "l8"
  /\ IF j[self] <= N
       THEN /\ ~b[j[self]]
            /\ j' = [j EXCEPT ![self] = j[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "l8"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "l9"]
            /\ UNCHANGED j
  /\ UNCHANGED << x, y, b >>

l9(self) ==
  /\ pc[self] = "l9"
  /\ IF y # self
       THEN pc' = [pc EXCEPT ![self] = "l10"]
       ELSE pc' = [pc EXCEPT ![self] = "cs"]
  /\ UNCHANGED << x, y, b, j >>

l10(self) ==
  /\ pc[self] = "l10"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![self] = "start"]
  /\ UNCHANGED << x, y, b, j >>

cs(self) ==
  /\ pc[self] = "cs"
  /\ pc' = [pc EXCEPT ![self] = "l11"]
  /\ UNCHANGED << x, y, b, j >>

l11(self) ==
  /\ pc[self] = "l11"
  /\ y' = 0
  /\ pc' = [pc EXCEPT ![self] = "l12"]
  /\ UNCHANGED << x, b, j >>

l12(self) ==
  /\ pc[self] = "l12"
  /\ b' = [b EXCEPT ![self] = FALSE]
  /\ pc' = [pc EXCEPT ![self] = "ncs"]
  /\ UNCHANGED << x, y, j >>

Proc(self) ==
  \/ ncs(self)   \/ start(self) \/ l1(self)  \/ l2(self)
  \/ l3(self)    \/ l4(self)    \/ l5(self)  \/ l6(self)
  \/ l7(self)    \/ l8(self)    \/ l9(self)  \/ l10(self)
  \/ cs(self)    \/ l11(self)   \/ l12(self)

(* All steps of a process except leaving the noncritical section. *)
ProgressStep(self) == (pc[self] # "ncs") /\ Proc(self)

Next == \E self \in ProcSet : Proc(self)

(***************************************************************************)
(* Weak fairness on every algorithmic step of every process, except the    *)
(* step out of the noncritical section (a process may stay there forever). *)
(***************************************************************************)
Fairness == \A self \in ProcSet : WF_vars(ProgressStep(self))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Safety: mutual exclusion *)
Mutex ==
  \A p, q \in ProcSet : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

(* Liveness: deadlock freedom. If some process is trying, some process *)
(* eventually enters the critical section.                             *)
DeadlockFree ==
  (\E p \in ProcSet : pc[p] # "ncs") ~> (\E p \in ProcSet : pc[p] = "cs")

(* Liveness: every process that repeatedly tries to enter the critical *)
(* section enters it infinitely often (stated per the requirements).   *)
StarvationFree ==
  \A p \in ProcSet : ([]<>(pc[p] # "ncs")) => ([]<>(pc[p] = "cs"))

(* Individual progress from the trying region. *)
TryingLeadsToCS ==
  \A p \in ProcSet : (pc[p] = "start") ~> (pc[p] = "cs")

THEOREM Spec => [](TypeOK /\ Mutex)
THEOREM Spec => DeadlockFree
=============================================================================