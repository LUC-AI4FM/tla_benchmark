------------------------------- MODULE FastMutex -------------------------------

EXTENDS Naturals

CONSTANT N

VARIABLES x, y, b, pc, j, failed

Proc == 1..N

PcVals == {"a0","a1","a2","a2b","a3","a4","a4c","a5","a6","a7","cs"}

vars == << x, y, b, pc, j, failed >>

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in Proc |-> FALSE]
  /\ pc = [i \in Proc |-> "a0"]
  /\ j = [i \in Proc |-> 1]
  /\ failed = [i \in Proc |-> FALSE]

A0(self) ==
  /\ pc[self] = "a0"
  /\ x' = self
  /\ b' = [b EXCEPT ![self] = TRUE]
  /\ pc' = [pc EXCEPT ![self] = "a1"]
  /\ UNCHANGED << y, j, failed >>

A1_to_a2(self) ==
  /\ pc[self] = "a1"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![self] = "a2"]
  /\ UNCHANGED << x, y, b, j, failed >>

A1_to_a5(self) ==
  /\ pc[self] = "a1"
  /\ y # 0
  /\ pc' = [pc EXCEPT ![self] = "a5"]
  /\ UNCHANGED << x, y, b, j, failed >>

A5(self) ==
  /\ pc[self] = "a5"
  /\ b' = [b EXCEPT ![self] = FALSE]
  /\ pc' = [pc EXCEPT ![self] = "a6"]
  /\ UNCHANGED << x, y, j, failed >>

A6(self) ==
  /\ pc[self] = "a6"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![self] = "a0"]
  /\ UNCHANGED << x, y, b, j, failed >>

A2(self) ==
  /\ pc[self] = "a2"
  /\ y' = self
  /\ pc' = [pc EXCEPT ![self] = "a2b"]
  /\ UNCHANGED << x, b, j, failed >>

A2b_to_cs(self) ==
  /\ pc[self] = "a2b"
  /\ x = self
  /\ pc' = [pc EXCEPT ![self] = "cs"]
  /\ UNCHANGED << x, y, b, j, failed >>

A2b_to_a3(self) ==
  /\ pc[self] = "a2b"
  /\ x # self
  /\ pc' = [pc EXCEPT ![self] = "a3"]
  /\ UNCHANGED << x, y, b, j, failed >>

A3(self) ==
  /\ pc[self] = "a3"
  /\ b' = [b EXCEPT ![self] = FALSE]
  /\ j' = [j EXCEPT ![self] = 1]
  /\ failed' = [failed EXCEPT ![self] = FALSE]
  /\ pc' = [pc EXCEPT ![self] = "a4"]
  /\ UNCHANGED << x, y >>

A4_iter_mark(self) ==
  /\ pc[self] = "a4"
  /\ j[self] <= N
  /\ j[self] # self
  /\ b[j[self]]
  /\ j' = [j EXCEPT ![self] = j[self] + 1]
  /\ failed' = [failed EXCEPT ![self] = TRUE]
  /\ pc' = [pc EXCEPT ![self] = "a4"]
  /\ UNCHANGED << x, y, b >>

A4_iter_skip(self) ==
  /\ pc[self] = "a4"
  /\ j[self] <= N
  /\ (j[self] = self \/ ~b[j[self]])
  /\ j' = [j EXCEPT ![self] = j[self] + 1]
  /\ pc' = [pc EXCEPT ![self] = "a4"]
  /\ UNCHANGED << x, y, b, failed >>

A4_done(self) ==
  /\ pc[self] = "a4"
  /\ j[self] > N
  /\ pc' = [pc EXCEPT ![self] = "a4c"]
  /\ UNCHANGED << x, y, b, j, failed >>

A4c_to_cs(self) ==
  /\ pc[self] = "a4c"
  /\ ~failed[self]
  /\ y = self
  /\ pc' = [pc EXCEPT ![self] = "cs"]
  /\ UNCHANGED << x, y, b, j, failed >>

A4c_to_a7(self) ==
  /\ pc[self] = "a4c"
  /\ ~(~failed[self] /\ y = self)
  /\ pc' = [pc EXCEPT ![self] = "a7"]
  /\ UNCHANGED << x, y, b, j, failed >>

A7(self) ==
  /\ pc[self] = "a7"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![self] = "a0"]
  /\ UNCHANGED << x, y, b, j, failed >>

CS(self) ==
  /\ pc[self] = "cs"
  /\ y' = 0
  /\ b' = [b EXCEPT ![self] = FALSE]
  /\ pc' = [pc EXCEPT ![self] = "a0"]
  /\ UNCHANGED << x, j, failed >>

ProcNext(self) ==
  \/ A0(self)
  \/ A1_to_a2(self)
  \/ A1_to_a5(self)
  \/ A5(self)
  \/ A6(self)
  \/ A2(self)
  \/ A2b_to_cs(self)
  \/ A2b_to_a3(self)
  \/ A3(self)
  \/ A4_iter_mark(self)
  \/ A4_iter_skip(self)
  \/ A4_done(self)
  \/ A4c_to_cs(self)
  \/ A4c_to_a7(self)
  \/ A7(self)
  \/ CS(self)

Next ==
  \E self \in Proc: ProcNext(self)

Spec ==
  Init /\ [][Next]_vars /\ \A self \in Proc: WF_vars(ProcNext(self))

IsInCS(i) == pc[i] = "cs"

MutualExclusion ==
  \A i, j \in Proc: i # j => ~(IsInCS(i) /\ IsInCS(j))

TypeOK ==
  /\ x \in {0} \cup Proc
  /\ y \in {0} \cup Proc
  /\ b \in [Proc -> BOOLEAN]
  /\ pc \in [Proc -> PcVals]
  /\ j \in [Proc -> 1..(N+1)]
  /\ failed \in [Proc -> BOOLEAN]

SomeProcessInfinitelyOftenInCS ==
  \E i \in Proc: []<>(IsInCS(i))

===============================================================================