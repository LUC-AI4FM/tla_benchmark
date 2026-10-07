----------------------------- MODULE FastMutex -----------------------------

EXTENDS Naturals

CONSTANT N

Proc == 1..N
Null == 0

VARIABLES x, y, b, S, pc

Labels == {
  "start", "setx", "checky", "sety", "checkx",
  "loop", "checky2", "retry", "cs", "unsetb"
}

vars == << x, y, b, S, pc >>

Other(p) == Proc \ {p}

Init ==
  /\ x = Null
  /\ y = Null
  /\ b \in [Proc -> BOOLEAN]
  /\ b = [p \in Proc |-> FALSE]
  /\ S \in [Proc -> SUBSET Proc]
  /\ S = [p \in Proc |-> {}]
  /\ pc \in [Proc -> Labels]
  /\ pc = [p \in Proc |-> "start"]

Start(p) ==
  /\ pc[p] = "start"
  /\ b'  = [b EXCEPT ![p] = TRUE]
  /\ pc' = [pc EXCEPT ![p] = "setx"]
  /\ UNCHANGED << x, y, S >>

SetX(p) ==
  /\ pc[p] = "setx"
  /\ x' = p
  /\ pc' = [pc EXCEPT ![p] = "checky"]
  /\ UNCHANGED << y, b, S >>

CheckYBusy(p) ==
  /\ pc[p] = "checky"
  /\ y # Null
  /\ b'  = [b EXCEPT ![p] = FALSE]
  /\ pc' = [pc EXCEPT ![p] = "retry"]
  /\ UNCHANGED << x, y, S >>

SetY(p) ==
  /\ pc[p] = "checky"
  /\ y = Null
  /\ y' = p
  /\ pc' = [pc EXCEPT ![p] = "checkx"]
  /\ UNCHANGED << x, b, S >>

CheckX_Success(p) ==
  /\ pc[p] = "checkx"
  /\ x = p
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED << x, y, b, S >>

CheckX_Fallback(p) ==
  /\ pc[p] = "checkx"
  /\ x # p
  /\ b'  = [b EXCEPT ![p] = FALSE]
  /\ S'  = [S EXCEPT ![p] = Other(p)]
  /\ pc' = [pc EXCEPT ![p] = "loop"]
  /\ UNCHANGED << x, y >>

LoopRemove(p) ==
  /\ pc[p] = "loop"
  /\ \E t \in S[p]: ~b[t]
  /\ LET k == CHOOSE t \in S[p]: ~b[t]
     IN S' = [S EXCEPT ![p] = @ \ {k}]
  /\ UNCHANGED << x, y, b, pc >>

LoopToCheckY2(p) ==
  /\ pc[p] = "loop"
  /\ S[p] = {}
  /\ pc' = [pc EXCEPT ![p] = "checky2"]
  /\ UNCHANGED << x, y, b, S >>

CheckY2_Success(p) ==
  /\ pc[p] = "checky2"
  /\ y = p
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED << x, y, b, S >>

CheckY2_Fail(p) ==
  /\ pc[p] = "checky2"
  /\ y # p
  /\ pc' = [pc EXCEPT ![p] = "retry"]
  /\ UNCHANGED << x, y, b, S >>

Retry(p) ==
  /\ pc[p] = "retry"
  /\ y = Null
  /\ pc' = [pc EXCEPT ![p] = "start"]
  /\ UNCHANGED << x, y, b, S >>

ExitY(p) ==
  /\ pc[p] = "cs"
  /\ y' = Null
  /\ pc' = [pc EXCEPT ![p] = "unsetb"]
  /\ UNCHANGED << x, b, S >>

UnsetB(p) ==
  /\ pc[p] = "unsetb"
  /\ b'  = [b EXCEPT ![p] = FALSE]
  /\ pc' = [pc EXCEPT ![p] = "start"]
  /\ UNCHANGED << x, y, S >>

ProcNext(p) ==
  \/ Start(p)
  \/ SetX(p)
  \/ CheckYBusy(p)
  \/ SetY(p)
  \/ CheckX_Success(p)
  \/ CheckX_Fallback(p)
  \/ LoopRemove(p)
  \/ LoopToCheckY2(p)
  \/ CheckY2_Success(p)
  \/ CheckY2_Fail(p)
  \/ Retry(p)
  \/ ExitY(p)
  \/ UnsetB(p)

Next ==
  \E p \in Proc: ProcNext(p)

TypeOK ==
  /\ x \in Proc \cup {Null}
  /\ y \in Proc \cup {Null}
  /\ b \in [Proc -> BOOLEAN]
  /\ S \in [Proc -> SUBSET Proc]
  /\ pc \in [Proc -> Labels]

MutualExclusion ==
  \A p,q \in Proc: (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

Liveness ==
  []<>(\E p \in Proc: pc[p] = "cs")

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================