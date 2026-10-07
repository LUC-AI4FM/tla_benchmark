------------------------------ MODULE FastMutex ------------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

VARIABLES x, y, b, pc, j, failed

Proc == 1..N

PCVals == {"ncs", "set1", "checky", "waity1", "checkx", "scan", "postscan", "waity2", "cs"}

vars == << x, y, b, pc, j, failed >>

TypeOK ==
  /\ x \in 0..N
  /\ y \in 0..N
  /\ b \in [Proc -> BOOLEAN]
  /\ pc \in [Proc -> PCVals]
  /\ j \in [Proc -> 1..(N+1)]
  /\ failed \in [Proc -> BOOLEAN]

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in Proc |-> FALSE]
  /\ pc = [i \in Proc |-> "ncs"]
  /\ j = [i \in Proc |-> 1]
  /\ failed = [i \in Proc |-> FALSE]

NCS(i) ==
  /\ i \in Proc
  /\ pc[i] = "ncs"
  /\ pc' = [pc EXCEPT ![i] = "set1"]
  /\ UNCHANGED << x, y, b, j, failed >>

SetIntent(i) ==
  /\ i \in Proc
  /\ pc[i] = "set1"
  /\ x' = i
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "checky"]
  /\ UNCHANGED << y, j, failed >>

CheckY_GoSetY(i) ==
  /\ i \in Proc
  /\ pc[i] = "checky"
  /\ y = 0
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "checkx"]
  /\ UNCHANGED << x, b, j, failed >>

CheckY_Fail(i) ==
  /\ i \in Proc
  /\ pc[i] = "checky"
  /\ y # 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "waity1"]
  /\ UNCHANGED << x, y, j, failed >>

WaitY1(i) ==
  /\ i \in Proc
  /\ pc[i] = "waity1"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "set1"]
  /\ UNCHANGED << x, y, b, j, failed >>

GoCS_Direct(i) ==
  /\ i \in Proc
  /\ pc[i] = "checkx"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b, j, failed >>

StartScan(i) ==
  /\ i \in Proc
  /\ pc[i] = "checkx"
  /\ x # i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ j' = [j EXCEPT ![i] = 1]
  /\ failed' = [failed EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "scan"]
  /\ UNCHANGED << x, y >>

ScanStep(i) ==
  /\ i \in Proc
  /\ pc[i] = "scan"
  /\ j[i] <= N
  /\ LET k == j[i] IN
     /\ j' = [j EXCEPT ![i] = j[i] + 1]
     /\ failed' = [failed EXCEPT ![i] = failed[i] \/ (k # i /\ b[k])]
     /\ pc' = [pc EXCEPT ![i] = "scan"]
     /\ UNCHANGED << x, y, b >>

ScanDone(i) ==
  /\ i \in Proc
  /\ pc[i] = "scan"
  /\ j[i] > N
  /\ pc' = [pc EXCEPT ![i] = "postscan"]
  /\ UNCHANGED << x, y, b, j, failed >>

PostScanToCS(i) ==
  /\ i \in Proc
  /\ pc[i] = "postscan"
  /\ y = i
  /\ ~failed[i]
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b, j, failed >>

PostScanRetry(i) ==
  /\ i \in Proc
  /\ pc[i] = "postscan"
  /\ (y # i) \/ failed[i]
  /\ pc' = [pc EXCEPT ![i] = "waity2"]
  /\ UNCHANGED << x, y, b, j, failed >>

WaitY2(i) ==
  /\ i \in Proc
  /\ pc[i] = "waity2"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "set1"]
  /\ UNCHANGED << x, y, b, j, failed >>

CSLeave(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ y' = 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "ncs"]
  /\ UNCHANGED << x, j, failed >>

ProcStep(i) ==
  \/ NCS(i)
  \/ SetIntent(i)
  \/ CheckY_GoSetY(i)
  \/ CheckY_Fail(i)
  \/ WaitY1(i)
  \/ GoCS_Direct(i)
  \/ StartScan(i)
  \/ ScanStep(i)
  \/ ScanDone(i)
  \/ PostScanToCS(i)
  \/ PostScanRetry(i)
  \/ WaitY2(i)
  \/ CSLeave(i)

Next ==
  \E i \in Proc : ProcStep(i)

Spec ==
  Init /\ [][Next]_vars /\ \A i \in Proc : WF_vars(ProcStep(i))

MutualExclusion ==
  \A i, j2 \in Proc : i # j2 => ~(pc[i] = "cs" /\ pc[j2] = "cs")

InfinitelyOftenCS ==
  []<>(\E i \in Proc : pc[i] = "cs")

=============================================================================