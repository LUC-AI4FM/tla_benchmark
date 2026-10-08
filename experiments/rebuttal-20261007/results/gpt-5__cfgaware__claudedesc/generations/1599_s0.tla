---- MODULE FastMutex ----
EXTENDS Naturals, TLC

CONSTANT N

(*
Lamport's Fast Mutual Exclusion algorithm for N processes (1..N).

Shared variables:
- x: last process to register interest (0 means none)
- y: "winner" slot (0 means none)
- b: array of booleans, b[i] = TRUE when process i is trying to enter

Each process has a local variable:
- j: loop counter for scanning other processes' flags in the slow path

Blocking awaits occur at labels l4 (await y = 0), l8 (await (j = self) \/ ~b[j]),
and l10 (await y = 0). The critical section label is "cs" and the noncritical
section label is "ncs".

The FairSpec below composes the base temporal behavior with weak fairness on
every process's protocol action. The safety property Invariant asserts mutual
exclusion. The conditional liveness property CondLiveness asserts that if some
process is perpetually outside the noncritical section, then some process enters
the critical section infinitely often.
*)

\* Processes are 1..N
Proc == 1..N

VARIABLES x, y, b, pc, j

vars == << x, y, b, pc, j >>

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in Proc |-> FALSE]
  /\ pc = [i \in Proc |-> "ncs"]
  /\ j = [i \in Proc |-> 0]

(*
Control states (pc[self]) used:
  "ncs"  : noncritical section
  "l1"   : b[self] := TRUE
  "l2"   : x := self
  "l3"   : if y # 0 then (set b[self]:=FALSE; goto l4) else goto l5
  "l4"   : await y = 0; then goto l8a         (blocking await)
  "l5"   : y := self
  "l6"   : if x = self then goto cs else goto l7
  "l7"   : b[self] := FALSE; goto l8a
  "l8a"  : j := 1; goto l8
  "l8"   : await (j=self) \/ ~b[j]; goto l8c  (blocking await)
  "l8c"  : if j < N then j := j+1; goto l8 else goto l9
  "l9"   : if y = self then goto cs else goto l10
  "l10"  : await y = 0; goto l2               (blocking await)
  "cs"   : critical section (skip; goto l11)
  "l11"  : y := 0
  "l12"  : b[self] := FALSE; goto ncs
*)

A_ncs(self) ==
  /\ pc[self] = "ncs"
  /\ pc' = [pc EXCEPT ![self] = "l1"]
  /\ UNCHANGED << x, y, b, j >>

A_l1(self) ==
  /\ pc[self] = "l1"
  /\ b' = [b EXCEPT ![self] = TRUE]
  /\ pc' = [pc EXCEPT ![self] = "l2"]
  /\ UNCHANGED << x, y, j >>

A_l2(self) ==
  /\ pc[self] = "l2"
  /\ x' = self
  /\ pc' = [pc EXCEPT ![self] = "l3"]
  /\ UNCHANGED << y, b, j >>

A_l3_to_l4(self) ==
  /\ pc[self] = "l3"
  /\ y # 0
  /\ b' = [b EXCEPT ![self] = FALSE]
  /\ pc' = [pc EXCEPT ![self] = "l4"]
  /\ UNCHANGED << x, y, j >>

A_l3_to_l5(self) ==
  /\ pc[self] = "l3"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![self] = "l5"]
  /\ UNCHANGED << x, y, b, j >>

A_l4_await(self) ==
  /\ pc[self] = "l4"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![self] = "l8a"]
  /\ UNCHANGED << x, y, b, j >>

A_l5(self) ==
  /\ pc[self] = "l5"
  /\ y' = self
  /\ pc' = [pc EXCEPT ![self] = "l6"]
  /\ UNCHANGED << x, b, j >>

A_l6_true(self) ==
  /\ pc[self] = "l6"
  /\ x = self
  /\ pc' = [pc EXCEPT ![self] = "cs"]
  /\ UNCHANGED << x, y, b, j >>

A_l6_false(self) ==
  /\ pc[self] = "l6"
  /\ x # self
  /\ pc' = [pc EXCEPT ![self] = "l7"]
  /\ UNCHANGED << x, y, b, j >>

A_l7(self) ==
  /\ pc[self] = "l7"
  /\ b' = [b EXCEPT ![self] = FALSE]
  /\ pc' = [pc EXCEPT ![self] = "l8a"]
  /\ UNCHANGED << x, y, j >>

A_l8a(self) ==
  /\ pc[self] = "l8a"
  /\ j' = [j EXCEPT ![self] = 1]
  /\ pc' = [pc EXCEPT ![self] = "l8"]
  /\ UNCHANGED << x, y, b >>

A_l8_await(self) ==
  /\ pc[self] = "l8"
  /\ j[self] \in 1..N
  /\ ( (j[self] = self) \/ ~b[j[self]] )
  /\ pc' = [pc EXCEPT ![self] = "l8c"]
  /\ UNCHANGED << x, y, b, j >>

A_l8c_more(self) ==
  /\ pc[self] = "l8c"
  /\ j[self] < N
  /\ j' = [j EXCEPT ![self] = j[self] + 1]
  /\ pc' = [pc EXCEPT ![self] = "l8"]
  /\ UNCHANGED << x, y, b >>

A_l8c_done(self) ==
  /\ pc[self] = "l8c"
  /\ j[self] >= N
  /\ pc' = [pc EXCEPT ![self] = "l9"]
  /\ UNCHANGED << x, y, b, j >>

A_l9_haveY(self) ==
  /\ pc[self] = "l9"
  /\ y = self
  /\ pc' = [pc EXCEPT ![self] = "cs"]
  /\ UNCHANGED << x, y, b, j >>

A_l9_noY(self) ==
  /\ pc[self] = "l9"
  /\ y # self
  /\ pc' = [pc EXCEPT ![self] = "l10"]
  /\ UNCHANGED << x, y, b, j >>

A_l10_await(self) ==
  /\ pc[self] = "l10"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![self] = "l2"]
  /\ UNCHANGED << x, y, b, j >>

A_cs(self) ==
  /\ pc[self] = "cs"
  /\ pc' = [pc EXCEPT ![self] = "l11"]
  /\ UNCHANGED << x, y, b, j >>

A_l11(self) ==
  /\ pc[self] = "l11"
  /\ y' = 0
  /\ pc' = [pc EXCEPT ![self] = "l12"]
  /\ UNCHANGED << x, b, j >>

A_l12(self) ==
  /\ pc[self] = "l12"
  /\ b' = [b EXCEPT ![self] = FALSE]
  /\ pc' = [pc EXCEPT ![self] = "ncs"]
  /\ UNCHANGED << x, y, j >>

Proc(self) ==
  \/ A_ncs(self)
  \/ A_l1(self)
  \/ A_l2(self)
  \/ A_l3_to_l4(self)
  \/ A_l3_to_l5(self)
  \/ A_l4_await(self)
  \/ A_l5(self)
  \/ A_l6_true(self)
  \/ A_l6_false(self)
  \/ A_l7(self)
  \/ A_l8a(self)
  \/ A_l8_await(self)
  \/ A_l8c_more(self)
  \/ A_l8c_done(self)
  \/ A_l9_haveY(self)
  \/ A_l9_noY(self)
  \/ A_l10_await(self)
  \/ A_cs(self)
  \/ A_l11(self)
  \/ A_l12(self)

Next ==
  \E self \in Proc: Proc(self)

Spec ==
  Init /\ [][Next]_vars

FairSpec ==
  Spec /\ \A self \in Proc: WF_vars(Proc(self))

Invariant ==
  \A i, k \in Proc: (i # k) => ~(pc[i] = "cs" /\ pc[k] = "cs")

CondLiveness ==
  (<>[](\E i \in Proc: pc[i] # "ncs")) => ([]<>(\E k \in Proc: pc[k] = "cs"))

====