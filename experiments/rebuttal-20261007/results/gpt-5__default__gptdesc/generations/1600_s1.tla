---- MODULE FastMutex ----
EXTENDS Naturals

CONSTANTS N

ASSUME N \in Nat \ {0}

VARIABLES x, y, b, pc, j, failed

ProcSet == 1..N
PCStates == {"try1","try2","waitY0","try3","scan","checkY","waitY0b","cs","exit"}

vars == << x, y, b, pc, j, failed >>

TypeOK ==
  /\ x \in 0..N
  /\ y \in 0..N
  /\ b \in [ProcSet -> BOOLEAN]
  /\ pc \in [ProcSet -> PCStates]
  /\ j \in [ProcSet -> ProcSet]
  /\ failed \in [ProcSet -> BOOLEAN]

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in ProcSet |-> FALSE]
  /\ pc = [i \in ProcSet |-> "try1"]
  /\ j = [i \in ProcSet |-> 1]
  /\ failed = [i \in ProcSet |-> FALSE]

NextJ(i) == IF j[i] = N THEN 1 ELSE j[i] + 1

Try1(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "try1"
  /\ x' = i
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ j' = [j EXCEPT ![i] = 1]
  /\ failed' = [failed EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "try2"]
  /\ UNCHANGED << y >>

Try2_setY(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "try2"
  /\ y = 0
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "try3"]
  /\ UNCHANGED << x, b, j, failed >>

Try2_wait(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "try2"
  /\ y # 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ failed' = [failed EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "waitY0"]
  /\ UNCHANGED << x, y, j >>

WaitY0(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "waitY0"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "try1"]
  /\ UNCHANGED << x, y, b, j, failed >>

Try3_fast(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "try3"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b, j, failed >>

Try3_slow(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "try3"
  /\ x # i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ j' = [j EXCEPT ![i] = 1]
  /\ failed' = [failed EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "scan"]
  /\ UNCHANGED << x, y >>

ScanAdvance(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "scan"
  /\ j[i] # i
  /\ ~ b[j[i]]
  /\ j' = [j EXCEPT ![i] = NextJ(i)]
  /\ UNCHANGED << x, y, b, pc, failed >>

ScanStop(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "scan"
  /\ j[i] = i \/ b[j[i]]
  /\ pc' = [pc EXCEPT ![i] = "checkY"]
  /\ UNCHANGED << x, y, b, j, failed >>

CheckY_toCS(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "checkY"
  /\ y = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b, j, failed >>

CheckY_retry(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "checkY"
  /\ y # i
  /\ pc' = [pc EXCEPT ![i] = "waitY0b"]
  /\ UNCHANGED << x, y, b, j, failed >>

WaitY0b(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "waitY0b"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "try1"]
  /\ UNCHANGED << x, y, b, j, failed >>

CSStep(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "exit"]
  /\ UNCHANGED << x, y, b, j, failed >>

Exit(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "exit"
  /\ y' = 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "try1"]
  /\ UNCHANGED << x, j, failed >>

Proc(i) ==
  Try1(i)
  \/ Try2_setY(i)
  \/ Try2_wait(i)
  \/ WaitY0(i)
  \/ Try3_fast(i)
  \/ Try3_slow(i)
  \/ ScanAdvance(i)
  \/ ScanStop(i)
  \/ CheckY_toCS(i)
  \/ CheckY_retry(i)
  \/ WaitY0b(i)
  \/ CSStep(i)
  \/ Exit(i)

Next == \E i \in ProcSet: Proc(i)

Mutex ==
  \A i, k \in ProcSet: i # k => ~(pc[i] = "cs" /\ pc[k] = "cs")

EventuallyCS ==
  []<>(\E i \in ProcSet: pc[i] = "cs")

Spec ==
  Init /\ [][Next]_vars /\ \A i \in ProcSet: WF_vars(Proc(i))

====