----------------------------- MODULE FastMutex -----------------------------
EXTENDS Naturals

CONSTANT N
ASSUME N \in Nat /\ N >= 1

Proc == 1..N

VARIABLES pc, X, Y, b
vars == << pc, X, Y, b >>

Init ==
  /\ pc = [i \in Proc |-> "ncs"]
  /\ X = 0
  /\ Y = 0
  /\ b = [i \in Proc |-> FALSE]

StartAttempt(i) ==
  /\ i \in Proc
  /\ pc[i] = "ncs"
  /\ pc' = [pc EXCEPT ![i] = "try"]
  /\ UNCHANGED << X, Y, b >>

SetFlag(i) ==
  /\ i \in Proc
  /\ pc[i] = "try"
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "setX"]
  /\ UNCHANGED << X, Y >>

SetX(i) ==
  /\ i \in Proc
  /\ pc[i] = "setX"
  /\ X' = i
  /\ pc' = [pc EXCEPT ![i] = "checkY"]
  /\ UNCHANGED << Y, b >>

CheckY(i) ==
  /\ i \in Proc
  /\ pc[i] = "checkY"
  /\ IF Y # 0 THEN
       /\ b' = [b EXCEPT ![i] = FALSE]
       /\ pc' = [pc EXCEPT ![i] = "waitY0"]
       /\ UNCHANGED << X, Y >>
     ELSE
       /\ Y' = i
       /\ pc' = [pc EXCEPT ![i] = "checkX"]
       /\ UNCHANGED << X, b >>

CheckX(i) ==
  /\ i \in Proc
  /\ pc[i] = "checkX"
  /\ IF X = i THEN
       /\ pc' = [pc EXCEPT ![i] = "cs"]
       /\ UNCHANGED << X, Y, b >>
     ELSE
       /\ b' = [b EXCEPT ![i] = FALSE]
       /\ pc' = [pc EXCEPT ![i] = "waitOthers"]
       /\ UNCHANGED << X, Y >>

WaitOthers(i) ==
  /\ i \in Proc
  /\ pc[i] = "waitOthers"
  /\ \A k \in Proc : (k # i) => b[k] = FALSE
  /\ pc' = [pc EXCEPT ![i] = "checkY2"]
  /\ UNCHANGED << X, Y, b >>

CheckY2(i) ==
  /\ i \in Proc
  /\ pc[i] = "checkY2"
  /\ IF Y = i THEN
       /\ pc' = [pc EXCEPT ![i] = "cs"]
       /\ UNCHANGED << X, Y, b >>
     ELSE
       /\ pc' = [pc EXCEPT ![i] = "waitY0"]
       /\ UNCHANGED << X, Y, b >>

WaitY0(i) ==
  /\ i \in Proc
  /\ pc[i] = "waitY0"
  /\ Y = 0
  /\ pc' = [pc EXCEPT ![i] = "try"]
  /\ UNCHANGED << X, Y, b >>

Exit(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ Y' = 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "ncs"]
  /\ UNCHANGED X

ProcStep(i) ==
  SetFlag(i) \/ SetX(i) \/ CheckY(i) \/ CheckX(i)
  \/ WaitOthers(i) \/ CheckY2(i) \/ WaitY0(i) \/ Exit(i)

Next ==
  \E i \in Proc :
    StartAttempt(i) \/ ProcStep(i)

Spec ==
  Init /\ [] [Next]_vars /\ (\A i \in Proc : WF_vars(ProcStep(i)))

\* Safety invariants
TypeInv ==
  /\ pc \in [Proc -> {"ncs","try","setX","checkY","checkX","waitOthers","checkY2","waitY0","cs"}]
  /\ X \in 0..N
  /\ Y \in 0..N
  /\ b \in [Proc -> BOOLEAN]

MutualExclusion ==
  \A i, j \in Proc : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Liveness property (conditional progress)
Attempting(i) == pc[i] # "ncs"
InCS(i) == pc[i] = "cs"

Liveness ==
  (\E i \in Proc : <>[] Attempting(i)) => []<> (\E j \in Proc : InCS(j))

=============================================================================