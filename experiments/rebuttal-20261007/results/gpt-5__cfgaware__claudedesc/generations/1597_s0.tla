---- MODULE FastMutex ----
EXTENDS Integers, Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 2

(*
  Lamport's Fast Mutex for N processes.
  Shared variables: x, y, b.
  Local variables:
    - For process 1 (Proc1): j, failed
    - For processes 2..N (Proc2): j2, failed2
*)

VARIABLES
  x, y,                \* integers in 0..N
  b,                   \* [Proc -> BOOLEAN]
  pc,                  \* [Proc -> {"start","checkY","waitY0a","checkX","scanCheck","waitY0b","cs"}]
  j, failed,           \* locals for Proc1 (modeled for all processes; only p=1 uses them)
  j2, failed2          \* locals for Proc2 (modeled for all processes; only p>=2 uses them)

Proc == 1..N

Proc2 == 2..N

Labels == {"start","checkY","waitY0a","checkX","scanCheck","waitY0b","cs"}

InCS(p) == pc[p] = "cs"

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [p \in Proc |-> FALSE]
  /\ pc = [p \in Proc |-> "start"]
  /\ j = [p \in Proc |-> 1]
  /\ failed = [p \in Proc |-> FALSE]
  /\ j2 = [p \in Proc |-> 1]
  /\ failed2 = [p \in Proc |-> FALSE]

(*
  Steps for process 1 (Proc1), using locals j and failed.
*)
NextFor1(self) ==
  \/
    /\ pc[self] = "start"
    /\ x' = self
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "checkY"]
    /\ UNCHANGED << y, j, failed, j2, failed2 >>
  \/
    /\ pc[self] = "checkY"
    /\ y = 0
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "checkX"]
    /\ UNCHANGED << x, b, j, failed, j2, failed2 >>
  \/
    /\ pc[self] = "checkY"
    /\ y # 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "waitY0a"]
    /\ UNCHANGED << x, y, j, failed, j2, failed2 >>
  \/
    /\ pc[self] = "waitY0a"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>
  \/
    /\ pc[self] = "checkX"
    /\ x = self
    /\ pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>
  \/
    /\ pc[self] = "checkX"
    /\ x # self
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ j' = [j EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "scanCheck"]
    /\ UNCHANGED << x, y, failed, j2, failed2 >>
  \/
    /\ pc[self] = "scanCheck"
    /\ j[self] <= N
    /\ (j[self] = self \/ ~b[j[self]])
    /\ j' = [j EXCEPT ![self] = j[self] + 1]
    /\ UNCHANGED << x, y, b, pc, failed, j2, failed2 >>
  \/
    /\ pc[self] = "scanCheck"
    /\ j[self] > N
    /\ y = self
    /\ pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>
  \/
    /\ pc[self] = "scanCheck"
    /\ j[self] > N
    /\ y # self
    /\ failed' = [failed EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "waitY0b"]
    /\ UNCHANGED << x, y, b, j, j2, failed2 >>
  \/
    /\ pc[self] = "waitY0b"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>
  \/
    /\ pc[self] = "cs"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, j, failed, j2, failed2 >>

(*
  Steps for processes 2..N (Proc2), using locals j2 and failed2.
*)
NextFor2(self) ==
  \/
    /\ pc[self] = "start"
    /\ x' = self
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "checkY"]
    /\ UNCHANGED << y, j, failed, j2, failed2 >>
  \/
    /\ pc[self] = "checkY"
    /\ y = 0
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "checkX"]
    /\ UNCHANGED << x, b, j, failed, j2, failed2 >>
  \/
    /\ pc[self] = "checkY"
    /\ y # 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "waitY0a"]
    /\ UNCHANGED << x, y, j, failed, j2, failed2 >>
  \/
    /\ pc[self] = "waitY0a"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>
  \/
    /\ pc[self] = "checkX"
    /\ x = self
    /\ pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>
  \/
    /\ pc[self] = "checkX"
    /\ x # self
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ j2' = [j2 EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "scanCheck"]
    /\ UNCHANGED << x, y, j, failed, failed2 >>
  \/
    /\ pc[self] = "scanCheck"
    /\ j2[self] <= N
    /\ (j2[self] = self \/ ~b[j2[self]])
    /\ j2' = [j2 EXCEPT ![self] = j2[self] + 1]
    /\ UNCHANGED << x, y, b, pc, j, failed, failed2 >>
  \/
    /\ pc[self] = "scanCheck"
    /\ j2[self] > N
    /\ y = self
    /\ pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>
  \/
    /\ pc[self] = "scanCheck"
    /\ j2[self] > N
    /\ y # self
    /\ failed2' = [failed2 EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "waitY0b"]
    /\ UNCHANGED << x, y, b, j, failed, j2 >>
  \/
    /\ pc[self] = "waitY0b"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>
  \/
    /\ pc[self] = "cs"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, j, failed, j2, failed2 >>

ProcStep(self) ==
  (self = 1 /\ NextFor1(self))
  \/
  (self # 1 /\ NextFor2(self))

Next ==
  \E self \in Proc: ProcStep(self)

vars == << x, y, b, pc, j, failed, j2, failed2 >>

Spec ==
  Init /\ [][Next]_vars /\ \A self \in Proc: WF_vars(ProcStep(self))

Invariant ==
  \A p \in Proc: \A q \in Proc: (p # q) => ~(InCS(p) /\ InCS(q))

Liveness ==
  []<>(\E p \in Proc: InCS(p))

====