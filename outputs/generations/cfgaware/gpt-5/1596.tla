---- MODULE FastMutex ----
EXTENDS Naturals

CONSTANTS N, M

(*
  Assumptions on constants
*)
ASSUME N \in Nat /\ N >= 1 /\ M \in Nat /\ 0 <= M /\ M <= N

(*
  Process sets
*)
PidSet == 1..N
ProcA == 1..M
ProcB == (M+1)..N

PCLabels == {"ncs","testY","waitY","check","waitB","cs"}

VARIABLES x, y, b, pc

vars == << x, y, b, pc >>

TypeOK ==
  /\ x \in ({0} \cup PidSet)
  /\ y \in ({0} \cup PidSet)
  /\ b \in [PidSet -> BOOLEAN]
  /\ pc \in [PidSet -> PCLabels]

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in PidSet |-> FALSE]
  /\ pc = [i \in PidSet |-> "ncs"]
  /\ TypeOK

StepTry(self) ==
  /\ self \in PidSet
  /\ pc[self] \in {"ncs","waitY"}
  /\ y = 0
  /\ x' = self
  /\ b' = [b EXCEPT ![self] = TRUE]
  /\ pc' = [pc EXCEPT ![self] = "testY"]
  /\ UNCHANGED << y >>

StepTestYTake(self) ==
  /\ self \in PidSet
  /\ pc[self] = "testY"
  /\ y = 0
  /\ y' = self
  /\ pc' = [pc EXCEPT ![self] = "check"]
  /\ UNCHANGED << x, b >>

StepTestYBackoff(self) ==
  /\ self \in PidSet
  /\ pc[self] = "testY"
  /\ y # 0
  /\ b' = [b EXCEPT ![self] = FALSE]
  /\ pc' = [pc EXCEPT ![self] = "waitY"]
  /\ UNCHANGED << x, y >>

StepCheckFast(self) ==
  /\ self \in PidSet
  /\ pc[self] = "check"
  /\ x = self
  /\ pc' = [pc EXCEPT ![self] = "cs"]
  /\ UNCHANGED << x, y, b >>

StepCheckSlow(self) ==
  /\ self \in PidSet
  /\ pc[self] = "check"
  /\ x # self
  /\ b' = [b EXCEPT ![self] = FALSE]
  /\ pc' = [pc EXCEPT ![self] = "waitB"]
  /\ UNCHANGED << x, y >>

StepWaitB(self) ==
  /\ self \in PidSet
  /\ pc[self] = "waitB"
  /\ \A j \in PidSet: j = self \/ ~b[j]
  /\ pc' = [pc EXCEPT ![self] = IF y = self THEN "cs" ELSE "waitY"]
  /\ UNCHANGED << x, y, b >>

StepCSExit(self) ==
  /\ self \in PidSet
  /\ pc[self] = "cs"
  /\ y' = 0
  /\ b' = [b EXCEPT ![self] = FALSE]
  /\ pc' = [pc EXCEPT ![self] = "ncs"]
  /\ UNCHANGED << x >>

ProcStep(self) ==
  StepTry(self)
  \/ StepTestYTake(self)
  \/ StepTestYBackoff(self)
  \/ StepCheckFast(self)
  \/ StepCheckSlow(self)
  \/ StepWaitB(self)
  \/ StepCSExit(self)

AClass ==
  \E i \in ProcA: ProcStep(i)

BClass ==
  \E j \in ProcB: ProcStep(j)

Next ==
  AClass \/ BClass

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(AClass) /\ WF_vars(BClass)

(*
  Mutual exclusion: no two distinct processes are in the critical section simultaneously.
*)
Invariant ==
  \A p, q \in PidSet: p # q => ~(pc[p] = "cs" /\ pc[q] = "cs")

(*
  Liveness: some process enters (is in) the critical section infinitely often.
*)
Liveness ==
  []<>(\E p \in PidSet: pc[p] = "cs")

====