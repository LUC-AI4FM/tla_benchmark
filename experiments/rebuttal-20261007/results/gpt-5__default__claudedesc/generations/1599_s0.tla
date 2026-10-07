------------------------------ MODULE LamportFastMutex ------------------------------

EXTENDS Naturals, Integers

CONSTANT N

VARIABLES x, y, b, pc, j

Proc == 1..N

vars == << x, y, b, pc, j >>

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in Proc |-> FALSE]
  /\ pc = [i \in Proc |-> "ncs"]
  /\ j = [i \in Proc |-> 1]

(*
 Labels:
   "ncs"  - noncritical section
   "l1"   - b[self] := TRUE
   "l2"   - x := self
   "l3"   - if y = 0 then goto l4 else goto l7
   "l4"   - await x = self
   "l5"   - y := self
   "l6"   - if x = self then goto "cs" else goto l7
   "l7"   - b[self] := FALSE
   "l8"   - await y = 0
   "l9"   - j := 1
   "l10"  - scan b[1..N] with await ~b[j] for j != self
   "l11"  - if y = self then goto "cs" else goto l1
   "cs"   - critical section; then y := 0; b[self] := FALSE; goto "ncs"
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
  /\ y = 0
  /\ pc' = [pc EXCEPT ![self] = "l4"]
  /\ UNCHANGED << x, y, b, j >>

A_l3_to_l7(self) ==
  /\ pc[self] = "l3"
  /\ y # 0
  /\ pc' = [pc EXCEPT ![self] = "l7"]
  /\ UNCHANGED << x, y, b, j >>

A_l4(self) ==
  /\ pc[self] = "l4"
  /\ x = self
  /\ pc' = [pc EXCEPT ![self] = "l5"]
  /\ UNCHANGED << x, y, b, j >>

A_l5(self) ==
  /\ pc[self] = "l5"
  /\ y' = self
  /\ pc' = [pc EXCEPT ![self] = "l6"]
  /\ UNCHANGED << x, b, j >>

A_l6_to_cs(self) ==
  /\ pc[self] = "l6"
  /\ x = self
  /\ pc' = [pc EXCEPT ![self] = "cs"]
  /\ UNCHANGED << x, y, b, j >>

A_l6_to_l7(self) ==
  /\ pc[self] = "l6"
  /\ x # self
  /\ pc' = [pc EXCEPT ![self] = "l7"]
  /\ UNCHANGED << x, y, b, j >>

A_l7(self) ==
  /\ pc[self] = "l7"
  /\ b' = [b EXCEPT ![self] = FALSE]
  /\ pc' = [pc EXCEPT ![self] = "l8"]
  /\ UNCHANGED << x, y, j >>

A_l8(self) ==
  /\ pc[self] = "l8"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![self] = "l9"]
  /\ UNCHANGED << x, y, b, j >>

A_l9(self) ==
  /\ pc[self] = "l9"
  /\ j' = [j EXCEPT ![self] = 1]
  /\ pc' = [pc EXCEPT ![self] = "l10"]
  /\ UNCHANGED << x, y, b >>

A_l10_step_self(self) ==
  /\ pc[self] = "l10"
  /\ j[self] <= N
  /\ j[self] = self
  /\ j' = [j EXCEPT ![self] = @ + 1]
  /\ pc' = [pc EXCEPT ![self] = "l10"]
  /\ UNCHANGED << x, y, b >>

A_l10_step_other(self) ==
  /\ pc[self] = "l10"
  /\ j[self] <= N
  /\ j[self] # self
  /\ ~b[j[self]]
  /\ j' = [j EXCEPT ![self] = @ + 1]
  /\ pc' = [pc EXCEPT ![self] = "l10"]
  /\ UNCHANGED << x, y, b >>

A_l10_done(self) ==
  /\ pc[self] = "l10"
  /\ j[self] > N
  /\ pc' = [pc EXCEPT ![self] = "l11"]
  /\ UNCHANGED << x, y, b, j >>

A_l11_to_cs(self) ==
  /\ pc[self] = "l11"
  /\ y = self
  /\ pc' = [pc EXCEPT ![self] = "cs"]
  /\ UNCHANGED << x, y, b, j >>

A_l11_retry(self) ==
  /\ pc[self] = "l11"
  /\ y # self
  /\ pc' = [pc EXCEPT ![self] = "l1"]
  /\ UNCHANGED << x, y, b, j >>

A_cs(self) ==
  /\ pc[self] = "cs"
  /\ y' = 0
  /\ b' = [b EXCEPT ![self] = FALSE]
  /\ pc' = [pc EXCEPT ![self] = "ncs"]
  /\ UNCHANGED << x, j >>

ProcStep(self) ==
  A_ncs(self)
  \/ A_l1(self)
  \/ A_l2(self)
  \/ A_l3_to_l4(self)
  \/ A_l3_to_l7(self)
  \/ A_l4(self)
  \/ A_l5(self)
  \/ A_l6_to_cs(self)
  \/ A_l6_to_l7(self)
  \/ A_l7(self)
  \/ A_l8(self)
  \/ A_l9(self)
  \/ A_l10_step_self(self)
  \/ A_l10_step_other(self)
  \/ A_l10_done(self)
  \/ A_l11_to_cs(self)
  \/ A_l11_retry(self)
  \/ A_cs(self)

Next ==
  \E self \in Proc: ProcStep(self)

Spec ==
  Init /\ [][Next]_vars

FairSpec ==
  Spec /\ \A self \in Proc: WF_vars(ProcStep(self))

InCS(i) == pc[i] = "cs"

Invariant ==
  \A i, j \in Proc: (i # j) => ~(InCS(i) /\ InCS(j))

SomeProcAlwaysOutsideNCS ==
  \E i \in Proc: <>[] (pc[i] # "ncs")

SomeProcEntersCSInfinitelyOften ==
  \E i \in Proc: []<> (pc[i] = "cs")

CondLiveness ==
  SomeProcAlwaysOutsideNCS => SomeProcEntersCSInfinitelyOften

=============================================================================