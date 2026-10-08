---- MODULE LamportFastMutex ----
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat \ {0}

VARIABLES x, y, b, pc, S

Proc == 1..N

vars == << x, y, b, pc, S >>

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in Proc |-> FALSE]
  /\ pc = [i \in Proc |-> "start"]
  /\ S = [i \in Proc |-> {}]

Start(i) ==
  /\ i \in Proc
  /\ pc[i] = "start"
  /\ x' = i
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "tryY"]
  /\ UNCHANGED << y, S >>

TryY_Take(i) ==
  /\ i \in Proc
  /\ pc[i] = "tryY"
  /\ y = 0
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "chkX"]
  /\ UNCHANGED << x, b, S >>

TryY_Busy(i) ==
  /\ i \in Proc
  /\ pc[i] = "tryY"
  /\ y # 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "waitY0"]
  /\ UNCHANGED << x, y, S >>

WaitY0(i) ==
  /\ i \in Proc
  /\ pc[i] = "waitY0"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "start"]
  /\ UNCHANGED << x, y, b, S >>

ChkX_OK(i) ==
  /\ i \in Proc
  /\ pc[i] = "chkX"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b, S >>

ChkX_Fail(i) ==
  /\ i \in Proc
  /\ pc[i] = "chkX"
  /\ x # i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ S' = [S EXCEPT ![i] = Proc \ {i}]
  /\ pc' = [pc EXCEPT ![i] = "loop1"]
  /\ UNCHANGED << x, y >>

LoopRem(i, j) ==
  /\ i \in Proc
  /\ j \in Proc
  /\ pc[i] = "loop1"
  /\ j \in S[i]
  /\ ~b[j]
  /\ S' = [S EXCEPT ![i] = S[i] \ {j}]
  /\ UNCHANGED << x, y, b, pc >>

LoopEmptyOwn(i) ==
  /\ i \in Proc
  /\ pc[i] = "loop1"
  /\ S[i] = {}
  /\ y = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b, S >>

LoopEmptyLost(i) ==
  /\ i \in Proc
  /\ pc[i] = "loop1"
  /\ S[i] = {}
  /\ y # i
  /\ pc' = [pc EXCEPT ![i] = "waitY0b"]
  /\ UNCHANGED << x, y, b, S >>

WaitY0b(i) ==
  /\ i \in Proc
  /\ pc[i] = "waitY0b"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "start"]
  /\ UNCHANGED << x, y, b, S >>

CSExit(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ y' = 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "start"]
  /\ UNCHANGED << x, S >>

Step(i) ==
  Start(i)
  \/ TryY_Take(i)
  \/ TryY_Busy(i)
  \/ WaitY0(i)
  \/ ChkX_OK(i)
  \/ ChkX_Fail(i)
  \/ ( \E j \in S[i] : LoopRem(i, j) )
  \/ LoopEmptyOwn(i)
  \/ LoopEmptyLost(i)
  \/ WaitY0b(i)
  \/ CSExit(i)

Next ==
  \E i \in Proc : Step(i)

Spec ==
  Init
  /\ [][Next]_vars
  /\ \A i \in Proc : WF_vars(Step(i))

Invariant ==
  \A i \in Proc : \A j \in Proc :
    i # j => ~(pc[i] = "cs" /\ pc[j] = "cs")

Liveness ==
  []<>(\E i \in Proc : pc[i] = "cs")

====