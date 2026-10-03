----------------------------- MODULE FastMutex -----------------------------
EXTENDS Naturals

CONSTANT N, defaultInitValue

VARIABLES x, y, b, pc, j, failed

Proc == 1..N

vars == << x, y, b, pc, j, failed >>

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [p \in Proc |-> FALSE]
  /\ pc = [p \in Proc |-> "start"]
  /\ j = [p \in Proc |-> 0]
  /\ failed = [p \in Proc |-> FALSE]

Start(p) ==
  /\ p \in Proc
  /\ pc[p] = "start"
  /\ b' = [b EXCEPT ![p] = TRUE]
  /\ x' = p
  /\ pc' = [pc EXCEPT ![p] = "checkY"]
  /\ UNCHANGED << y, j, failed >>

CheckY(p) ==
  /\ p \in Proc
  /\ pc[p] = "checkY"
  /\ IF y # 0
        THEN /\ b' = [b EXCEPT ![p] = FALSE]
             /\ pc' = [pc EXCEPT ![p] = "waitY0"]
             /\ UNCHANGED << x, y, j, failed >>
        ELSE /\ pc' = [pc EXCEPT ![p] = "setY"]
             /\ UNCHANGED << x, y, b, j, failed >>

WaitY0(p) ==
  /\ p \in Proc
  /\ pc[p] = "waitY0"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![p] = "start"]
  /\ UNCHANGED << x, y, b, j, failed >>

SetY(p) ==
  /\ p \in Proc
  /\ pc[p] = "setY"
  /\ y' = p
  /\ pc' = [pc EXCEPT ![p] = "checkX"]
  /\ UNCHANGED << x, b, j, failed >>

CheckX(p) ==
  /\ p \in Proc
  /\ pc[p] = "checkX"
  /\ IF x = p
        THEN /\ pc' = [pc EXCEPT ![p] = "cs"]
             /\ UNCHANGED << x, y, b, j, failed >>
        ELSE /\ b' = [b EXCEPT ![p] = FALSE]
             /\ j' = [j EXCEPT ![p] = 1]
             /\ failed' = [failed EXCEPT ![p] = FALSE]
             /\ pc' = [pc EXCEPT ![p] = "scan"]
             /\ UNCHANGED << x, y >>

ScanAdvance(p) ==
  /\ p \in Proc
  /\ pc[p] = "scan"
  /\ (
       /\ j[p] \in 1..N
       /\ ( j[p] = p \/ ~b[j[p]] )
       /\ j' = [j EXCEPT ![p] = j[p] + 1]
       /\ UNCHANGED << x, y, b, pc, failed >>
     \/
       /\ j[p] = N + 1
       /\ pc' = [pc EXCEPT ![p] = "afterScan"]
       /\ UNCHANGED << x, y, b, j, failed >>
     )

AfterScan(p) ==
  /\ p \in Proc
  /\ pc[p] = "afterScan"
  /\ IF y = p
        THEN /\ failed' = [failed EXCEPT ![p] = FALSE]
             /\ pc' = [pc EXCEPT ![p] = "cs"]
             /\ UNCHANGED << x, y, b, j >>
        ELSE /\ failed' = [failed EXCEPT ![p] = TRUE]
             /\ pc' = [pc EXCEPT ![p] = "waitY0Retry"]
             /\ UNCHANGED << x, y, b, j >>

WaitY0Retry(p) ==
  /\ p \in Proc
  /\ pc[p] = "waitY0Retry"
  /\ y = 0
  /\ failed' = [failed EXCEPT ![p] = FALSE]
  /\ pc' = [pc EXCEPT ![p] = "start"]
  /\ UNCHANGED << x, y, b, j >>

CS(p) ==
  /\ p \in Proc
  /\ pc[p] = "cs"
  /\ y' = 0
  /\ b' = [b EXCEPT ![p] = FALSE]
  /\ pc' = [pc EXCEPT ![p] = "start"]
  /\ UNCHANGED << x, j, failed >>

ProcNext(p) ==
  \/ Start(p)
  \/ CheckY(p)
  \/ WaitY0(p)
  \/ SetY(p)
  \/ CheckX(p)
  \/ ScanAdvance(p)
  \/ AfterScan(p)
  \/ WaitY0Retry(p)
  \/ CS(p)

Next ==
  \E p \in Proc : ProcNext(p)

Spec ==
  Init /\ [][Next]_vars /\
  (\A p \in Proc :
      /\ WF_vars(Start(p))
      /\ WF_vars(CheckY(p))
      /\ WF_vars(WaitY0(p))
      /\ WF_vars(SetY(p))
      /\ WF_vars(CheckX(p))
      /\ WF_vars(ScanAdvance(p))
      /\ WF_vars(AfterScan(p))
      /\ WF_vars(WaitY0Retry(p))
      /\ WF_vars(CS(p))
   )

Invariant ==
  \A p, q \in Proc : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

Liveness ==
  \E p \in Proc : []<>(pc[p] = "cs")

============================================================================