----------------------------- MODULE FastMutex -----------------------------
EXTENDS Naturals

CONSTANT N

VARIABLES x, y, b, S, pc

Proc == 1..N

vars == << x, y, b, S, pc >>

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [p \in Proc |-> FALSE]
  /\ S = [p \in Proc |-> {}]
  /\ pc = [p \in Proc |-> "start"]

Start(p) ==
  /\ p \in Proc
  /\ pc[p] = "start"
  /\ b' = [b EXCEPT ![p] = TRUE]
  /\ x' = p
  /\ pc' = [pc EXCEPT ![p] = "checkY"]
  /\ UNCHANGED << y, S >>

CheckY_NotZero(p) ==
  /\ p \in Proc
  /\ pc[p] = "checkY"
  /\ y # 0
  /\ b' = [b EXCEPT ![p] = FALSE]
  /\ pc' = [pc EXCEPT ![p] = "waitY0"]
  /\ UNCHANGED << x, y, S >>

CheckY_Zero(p) ==
  /\ p \in Proc
  /\ pc[p] = "checkY"
  /\ y = 0
  /\ y' = p
  /\ pc' = [pc EXCEPT ![p] = "checkX"]
  /\ UNCHANGED << x, b, S >>

WaitY0(p) ==
  /\ p \in Proc
  /\ pc[p] = "waitY0"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![p] = "start"]
  /\ UNCHANGED << x, y, b, S >>

CheckX_Eq(p) ==
  /\ p \in Proc
  /\ pc[p] = "checkX"
  /\ x = p
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED << x, y, b, S >>

CheckX_Ne(p) ==
  /\ p \in Proc
  /\ pc[p] = "checkX"
  /\ x # p
  /\ b' = [b EXCEPT ![p] = FALSE]
  /\ S' = [S EXCEPT ![p] = Proc \ {p}]
  /\ pc' = [pc EXCEPT ![p] = "waitBFalse"]
  /\ UNCHANGED << x, y >>

WaitB_Rem(p) ==
  /\ p \in Proc
  /\ pc[p] = "waitBFalse"
  /\ \E j \in S[p]: ~b[j]
  /\ S' = [S EXCEPT ![p] = S[p] \ {CHOOSE k \in S[p]: ~b[k]}]
  /\ pc' = pc
  /\ UNCHANGED << x, y, b >>

WaitB_Done_Yeq(p) ==
  /\ p \in Proc
  /\ pc[p] = "waitBFalse"
  /\ S[p] = {}
  /\ y = p
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED << x, y, b, S >>

WaitB_Done_Yne(p) ==
  /\ p \in Proc
  /\ pc[p] = "waitBFalse"
  /\ S[p] = {}
  /\ y # p
  /\ pc' = [pc EXCEPT ![p] = "waitY0"]
  /\ UNCHANGED << x, y, b, S >>

LeaveCS(p) ==
  /\ p \in Proc
  /\ pc[p] = "cs"
  /\ y' = 0
  /\ b' = [b EXCEPT ![p] = FALSE]
  /\ pc' = [pc EXCEPT ![p] = "start"]
  /\ UNCHANGED << x, S >>

ProcStep(p) ==
  Start(p)
  \/ CheckY_NotZero(p)
  \/ CheckY_Zero(p)
  \/ WaitY0(p)
  \/ CheckX_Eq(p)
  \/ CheckX_Ne(p)
  \/ WaitB_Rem(p)
  \/ WaitB_Done_Yeq(p)
  \/ WaitB_Done_Yne(p)
  \/ LeaveCS(p)

Next ==
  \E p \in Proc: ProcStep(p)

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

MutualExclusion ==
  \A p, q \in Proc: (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

Liveness ==
  []<>(\E p \in Proc: pc[p] = "cs")
=============================