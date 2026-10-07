----------------------------- MODULE FastMutex -----------------------------
EXTENDS Naturals, TLC

CONSTANT N

ProcSet == 1..N

VARIABLES x, y, b, pc, j, failed

Vars == << x, y, b, pc, j, failed >>

PCVals == {"try", "setx", "checkY", "awaitY0", "sety", "fastCheck", "scanInit", "scan", "confirmY", "CS"}

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in ProcSet |-> FALSE]
  /\ pc = [i \in ProcSet |-> "try"]
  /\ j = [i \in ProcSet |-> 0]
  /\ failed = [i \in ProcSet |-> FALSE]

TypeOK ==
  /\ x \in ProcSet \cup {0}
  /\ y \in ProcSet \cup {0}
  /\ b \in [ProcSet -> BOOLEAN]
  /\ pc \in [ProcSet -> PCVals]
  /\ j \in [ProcSet -> 0..N]
  /\ failed \in [ProcSet -> BOOLEAN]

Try(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "try"
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "setx"]
  /\ UNCHANGED << x, y, j, failed >>

SetX(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "setx"
  /\ x' = i
  /\ pc' = [pc EXCEPT ![i] = "checkY"]
  /\ UNCHANGED << y, b, j, failed >>

CheckY(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "checkY"
  /\ IF y # 0 THEN
        /\ b' = [b EXCEPT ![i] = FALSE]
        /\ pc' = [pc EXCEPT ![i] = "awaitY0"]
        /\ UNCHANGED << x, y, j, failed >>
     ELSE
        /\ pc' = [pc EXCEPT ![i] = "sety"]
        /\ UNCHANGED << x, y, b, j, failed >>

SetY(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "sety"
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "fastCheck"]
  /\ UNCHANGED << x, b, j, failed >>

FastCheck(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "fastCheck"
  /\ IF x = i THEN
        /\ pc' = [pc EXCEPT ![i] = "CS"]
        /\ UNCHANGED << x, y, b, j, failed >>
     ELSE
        /\ b' = [b EXCEPT ![i] = FALSE]
        /\ pc' = [pc EXCEPT ![i] = "scanInit"]
        /\ UNCHANGED << x, y, j, failed >>

ScanInit(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "scanInit"
  /\ j' = [j EXCEPT ![i] = 1]
  /\ failed' = [failed EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "scan"]
  /\ UNCHANGED << x, y, b >>

Scan(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "scan"
  /\ LET jj == j[i] IN
       /\ jj \in 1..N
       /\ failed' = [failed EXCEPT ![i] = failed[i] \/ (jj # i /\ b[jj])]
       /\ IF jj < N THEN
             /\ j' = [j EXCEPT ![i] = jj + 1]
             /\ pc' = [pc EXCEPT ![i] = "scan"]
          ELSE
             /\ j' = j
             /\ pc' = [pc EXCEPT ![i] = "confirmY"]
  /\ UNCHANGED << x, y, b >>

ConfirmY(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "confirmY"
  /\ IF (~failed[i]) /\ y = i THEN
        /\ pc' = [pc EXCEPT ![i] = "CS"]
        /\ UNCHANGED << x, y, b, j, failed >>
     ELSE
        /\ pc' = [pc EXCEPT ![i] = "awaitY0"]
        /\ UNCHANGED << x, y, b, j, failed >>

AwaitY0(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "awaitY0"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "try"]
  /\ UNCHANGED << x, y, b, j, failed >>

Exit(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "CS"
  /\ y' = 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "try"]
  /\ UNCHANGED << x, j, failed >>

Proc(i) ==
     Try(i)
  \/ SetX(i)
  \/ CheckY(i)
  \/ SetY(i)
  \/ FastCheck(i)
  \/ ScanInit(i)
  \/ Scan(i)
  \/ ConfirmY(i)
  \/ AwaitY0(i)
  \/ Exit(i)

Next ==
  \E i \in ProcSet : Proc(i)

Spec ==
  Init /\ [][Next]_Vars /\ \A i \in ProcSet : WF_Vars(Proc(i))

Mutex ==
  \A p, q \in ProcSet : p # q => ~(pc[p] = "CS" /\ pc[q] = "CS")

Liveness ==
  \E i \in ProcSet : []<>(pc[i] = "CS")
=============================================================================