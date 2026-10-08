---- MODULE FastMutex ----
EXTENDS Naturals

CONSTANTS N, M

VARIABLES X, Y, b, pc, k

Proc == 1..N

States == {
  "Idle", "Announce", "SetX", "CheckY", "SetY", "Probe",
  "WaitOthers", "Retry", "CS", "ExitY", "ExitB"
}

vars == << X, Y, b, pc, k >>

Others(i) == Proc \ {i}

Init ==
  /\ X = 0
  /\ Y = 0
  /\ b = [i \in Proc |-> FALSE]
  /\ pc = [i \in Proc |-> "Idle"]
  /\ k = [i \in Proc |-> 0]

Start(i) ==
  /\ pc[i] = "Idle"
  /\ pc' = [pc EXCEPT ![i] = "Announce"]
  /\ UNCHANGED << X, Y, b, k >>

Announce(i) ==
  /\ pc[i] = "Announce"
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "SetX"]
  /\ UNCHANGED << X, Y, k >>

SetX(i) ==
  /\ pc[i] = "SetX"
  /\ X' = i
  /\ pc' = [pc EXCEPT ![i] = "CheckY"]
  /\ UNCHANGED << Y, b, k >>

CheckYGo(i) ==
  /\ pc[i] = "CheckY"
  /\ Y = 0
  /\ pc' = [pc EXCEPT ![i] = "SetY"]
  /\ UNCHANGED << X, Y, b, k >>

CheckYSpin(i) ==
  /\ pc[i] = "CheckY"
  /\ Y # 0
  /\ k[i] < M
  /\ k' = [k EXCEPT ![i] = k[i] + 1]
  /\ UNCHANGED << X, Y, b, pc >>

CheckYAbort(i) ==
  /\ pc[i] = "CheckY"
  /\ Y # 0
  /\ k[i] = M
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "Retry"]
  /\ k' = [k EXCEPT ![i] = 0]
  /\ UNCHANGED << X, Y >>

SetY(i) ==
  /\ pc[i] = "SetY"
  /\ Y' = i
  /\ pc' = [pc EXCEPT ![i] = "Probe"]
  /\ UNCHANGED << X, b, k >>

ProbeFast(i) ==
  /\ pc[i] = "Probe"
  /\ X = i
  /\ pc' = [pc EXCEPT ![i] = "CS"]
  /\ UNCHANGED << X, Y, b, k >>

ProbeSlow(i) ==
  /\ pc[i] = "Probe"
  /\ X # i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "WaitOthers"]
  /\ k' = [k EXCEPT ![i] = 0]
  /\ UNCHANGED << X, Y >>

WaitOthersProceed(i) ==
  /\ pc[i] = "WaitOthers"
  /\ \A j \in Others(i): b[j] = FALSE
  /\ pc' = [pc EXCEPT ![i] = IF Y = i THEN "CS" ELSE "Retry"]
  /\ UNCHANGED << X, Y, b, k >>

WaitOthersSpin(i) ==
  /\ pc[i] = "WaitOthers"
  /\ \E j \in Others(i): b[j] = TRUE
  /\ k[i] < M
  /\ k' = [k EXCEPT ![i] = k[i] + 1]
  /\ UNCHANGED << X, Y, b, pc >>

WaitOthersAbort(i) ==
  /\ pc[i] = "WaitOthers"
  /\ \E j \in Others(i): b[j] = TRUE
  /\ k[i] = M
  /\ pc' = [pc EXCEPT ![i] = "Retry"]
  /\ k' = [k EXCEPT ![i] = 0]
  /\ UNCHANGED << X, Y, b >>

RetryProceed(i) ==
  /\ pc[i] = "Retry"
  /\ Y = 0
  /\ pc' = [pc EXCEPT ![i] = "Announce"]
  /\ UNCHANGED << X, Y, b, k >>

RetrySpin(i) ==
  /\ pc[i] = "Retry"
  /\ Y # 0
  /\ k[i] < M
  /\ k' = [k EXCEPT ![i] = k[i] + 1]
  /\ UNCHANGED << X, Y, b, pc >>

EnterDone(i) ==
  /\ pc[i] = "CS"
  /\ pc' = [pc EXCEPT ![i] = "ExitY"]
  /\ UNCHANGED << X, Y, b, k >>

ExitY(i) ==
  /\ pc[i] = "ExitY"
  /\ pc' = [pc EXCEPT ![i] = "ExitB"]
  /\ IF Y = i THEN Y' = 0 ELSE Y' = Y
  /\ UNCHANGED << X, b, k >>

ExitB(i) ==
  /\ pc[i] = "ExitB"
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "Idle"]
  /\ k' = [k EXCEPT ![i] = 0]
  /\ UNCHANGED << X, Y >>

ProcStep(i) ==
  Start(i) \/
  Announce(i) \/
  SetX(i) \/
  CheckYGo(i) \/
  CheckYSpin(i) \/
  CheckYAbort(i) \/
  SetY(i) \/
  ProbeFast(i) \/
  ProbeSlow(i) \/
  WaitOthersProceed(i) \/
  WaitOthersSpin(i) \/
  WaitOthersAbort(i) \/
  RetryProceed(i) \/
  RetrySpin(i) \/
  EnterDone(i) \/
  ExitY(i) \/
  ExitB(i)

Next == \E i \in Proc: ProcStep(i)

TypeOK ==
  /\ X \in 0..N
  /\ Y \in 0..N
  /\ b \in [Proc -> BOOLEAN]
  /\ pc \in [Proc -> States]
  /\ k \in [Proc -> 0..M]

Mutex ==
  \A i, j \in Proc: i # j => ~(pc[i] = "CS" /\ pc[j] = "CS")

Invariant == TypeOK /\ Mutex

Fairness == \A i \in Proc: WF_vars(ProcStep(i))

Spec == Init /\ [][Next]_vars /\ Fairness

Liveness == []<>(\E i \in Proc: pc[i] = "CS")

====