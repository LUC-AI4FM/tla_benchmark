---- MODULE FastMutex ----
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 2

(*
--algorithm FastME
variables x = 0, y = 0, b = [i \in 2..N |-> FALSE];

define
  Proc == {1} \cup (2..N);
end define;

fair process One \in {1}:
begin
l0_1:
  x := 1;
l1_1:
  y := 1;
test_1:
  if x # 1 then goto waity0 else goto await1;
await1:
  await y = 1;
cs:
  skip; \* critical section
  y := 0;
  goto l0_1;
waity0:
  await y = 0;
  goto cs;
end process;

fair process Others \in 2..N:
begin
l0:
  b[self] := TRUE;
l1:
  x := self;
testY:
  if y # 0 then goto backoff1 else goto setY;
backoff1:
  b[self] := FALSE;
waitY0:
  await y = 0;
  goto l0;
setY:
  y := self;
testX:
  if x # self then goto backoff2 else goto cs;
backoff2:
  b[self] := FALSE;
waitClear:
  await (\A j \in 2..N: ~b[j]) /\ y = 0;
  goto l0;
cs:
  skip; \* critical section
  y := 0;
  b[self] := FALSE;
  goto l0;
end process;
end algorithm
*)

VARIABLES x, y, b, pc

Proc == {1} \cup (2..N)

vars == << x, y, b, pc >>

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in 2..N |-> FALSE]
  /\ pc = [ i \in Proc |-> IF i = 1 THEN "l0_1" ELSE "l0" ]

(*
  Process 1 actions
*)
One_L0 ==
  /\ pc[1] = "l0_1"
  /\ x' = 1
  /\ pc' = [pc EXCEPT ![1] = "l1_1"]
  /\ UNCHANGED << y, b >>

One_L1 ==
  /\ pc[1] = "l1_1"
  /\ y' = 1
  /\ pc' = [pc EXCEPT ![1] = "test_1"]
  /\ UNCHANGED << x, b >>

One_Test_to_Await1 ==
  /\ pc[1] = "test_1"
  /\ x = 1
  /\ pc' = [pc EXCEPT ![1] = "await1"]
  /\ UNCHANGED << x, y, b >>

One_Test_to_WaitY0 ==
  /\ pc[1] = "test_1"
  /\ x # 1
  /\ pc' = [pc EXCEPT ![1] = "waity0"]
  /\ UNCHANGED << x, y, b >>

One_Await1 ==
  /\ pc[1] = "await1"
  /\ y = 1
  /\ pc' = [pc EXCEPT ![1] = "cs"]
  /\ UNCHANGED << x, y, b >>

One_WaitY0 ==
  /\ pc[1] = "waity0"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![1] = "cs"]
  /\ UNCHANGED << x, y, b >>

One_CS ==
  /\ pc[1] = "cs"
  /\ y' = 0
  /\ pc' = [pc EXCEPT ![1] = "l0_1"]
  /\ UNCHANGED << x, b >>

OneStep ==
  \/ One_L0
  \/ One_L1
  \/ One_Test_to_Await1
  \/ One_Test_to_WaitY0
  \/ One_Await1
  \/ One_WaitY0
  \/ One_CS

(*
  Others (processes 2..N) actions, parameterized by i
*)
O_L0(i) ==
  /\ i \in 2..N
  /\ pc[i] = "l0"
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "l1"]
  /\ UNCHANGED << x, y >>

O_L1(i) ==
  /\ i \in 2..N
  /\ pc[i] = "l1"
  /\ x' = i
  /\ pc' = [pc EXCEPT ![i] = "testY"]
  /\ UNCHANGED << y, b >>

O_TestY_to_Backoff1(i) ==
  /\ i \in 2..N
  /\ pc[i] = "testY"
  /\ y # 0
  /\ pc' = [pc EXCEPT ![i] = "backoff1"]
  /\ UNCHANGED << x, y, b >>

O_TestY_to_SetY(i) ==
  /\ i \in 2..N
  /\ pc[i] = "testY"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "setY"]
  /\ UNCHANGED << x, y, b >>

O_Backoff1(i) ==
  /\ i \in 2..N
  /\ pc[i] = "backoff1"
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "waitY0"]
  /\ UNCHANGED << x, y >>

O_WaitY0(i) ==
  /\ i \in 2..N
  /\ pc[i] = "waitY0"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "l0"]
  /\ UNCHANGED << x, y, b >>

O_SetY(i) ==
  /\ i \in 2..N
  /\ pc[i] = "setY"
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "testX"]
  /\ UNCHANGED << x, b >>

O_TestX_to_CS(i) ==
  /\ i \in 2..N
  /\ pc[i] = "testX"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b >>

O_TestX_to_Backoff2(i) ==
  /\ i \in 2..N
  /\ pc[i] = "testX"
  /\ x # i
  /\ pc' = [pc EXCEPT ![i] = "backoff2"]
  /\ UNCHANGED << x, y, b >>

O_Backoff2(i) ==
  /\ i \in 2..N
  /\ pc[i] = "backoff2"
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "waitClear"]
  /\ UNCHANGED << x, y >>

O_WaitClear(i) ==
  /\ i \in 2..N
  /\ pc[i] = "waitClear"
  /\ (\A j \in 2..N: ~b[j]) /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "l0"]
  /\ UNCHANGED << x, y, b >>

O_CS(i) ==
  /\ i \in 2..N
  /\ pc[i] = "cs"
  /\ y' = 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "l0"]
  /\ UNCHANGED x

OtherStep(i) ==
  /\ i \in 2..N
  /\ ( O_L0(i)
     \/ O_L1(i)
     \/ O_TestY_to_Backoff1(i)
     \/ O_TestY_to_SetY(i)
     \/ O_Backoff1(i)
     \/ O_WaitY0(i)
     \/ O_SetY(i)
     \/ O_TestX_to_CS(i)
     \/ O_TestX_to_Backoff2(i)
     \/ O_Backoff2(i)
     \/ O_WaitClear(i)
     \/ O_CS(i)
     )

Next ==
  \/ OneStep
  \/ \E i \in 2..N: OtherStep(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(OneStep)
  /\ \A i \in 2..N: WF_vars(OtherStep(i))

InCS(p) == p \in Proc /\ pc[p] = "cs"

Invariant ==
  \A p, q \in Proc: (p # q) => ~(InCS(p) /\ InCS(q))

Liveness ==
  []<>(\E p \in Proc: InCS(p))

====