----------------------------- MODULE FastMutex -----------------------------
EXTENDS Naturals, TLC

CONSTANT N

(*
  Fast mutual exclusion algorithm (Peterson's Fast Mutex) for N processes.
  Shared state: x, y in 0..N; b : [1..N -> BOOLEAN]
  Each process i cycles through:
    - noncritical section (ncs)
    - doorway and contention protocol (try*)
    - critical section (cs)
    - exit: clear indicators and return to ncs
*)

ProcSet == 1..N

VARIABLES pc, x, y, b, j

vars == << pc, x, y, b, j >>

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in ProcSet |-> FALSE]
  /\ pc = [i \in ProcSet |-> "ncs"]
  /\ j  = [i \in ProcSet |-> 1]

NCS(i) ==
  /\ pc[i] = "ncs"
  /\ pc' = [pc EXCEPT ![i] = "try1"]
  /\ UNCHANGED << x, y, b, j >>

Try1(i) ==
  /\ pc[i] = "try1"
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "try2"]
  /\ UNCHANGED << x, y, j >>

Try2(i) ==
  /\ pc[i] = "try2"
  /\ x' = i
  /\ pc' = [pc EXCEPT ![i] = "try3"]
  /\ UNCHANGED << y, b, j >>

Try3a(i) ==
  /\ pc[i] = "try3"
  /\ y # 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "waitY0"]
  /\ UNCHANGED << x, y, j >>

Try3b(i) ==
  /\ pc[i] = "try3"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "try4"]
  /\ UNCHANGED << x, y, b, j >>

WaitY0(i) ==
  /\ pc[i] = "waitY0"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "try1"]
  /\ UNCHANGED << x, y, b, j >>

Try4(i) ==
  /\ pc[i] = "try4"
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "try5"]
  /\ UNCHANGED << x, b, j >>

Try5a(i) ==
  /\ pc[i] = "try5"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b, j >>

Try5b(i) ==
  /\ pc[i] = "try5"
  /\ x # i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ j' = [j EXCEPT ![i] = 1]
  /\ pc' = [pc EXCEPT ![i] = "scan"]
  /\ UNCHANGED << x, y >>

ScanInc(i) ==
  /\ pc[i] = "scan"
  /\ j[i] <= N
  /\ (j[i] = i \/ ~b[j[i]])
  /\ j' = [j EXCEPT ![i] = j[i] + 1]
  /\ UNCHANGED << pc, x, y, b >>

ScanFound(i) ==
  /\ pc[i] = "scan"
  /\ j[i] <= N
  /\ j[i] # i
  /\ b[j[i]]
  /\ pc' = [pc EXCEPT ![i] = "contend"]
  /\ UNCHANGED << x, y, b, j >>

ScanDone(i) ==
  /\ pc[i] = "scan"
  /\ j[i] = N + 1
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b, j >>

ContendWait(i) ==
  /\ pc[i] = "contend"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "try1"]
  /\ UNCHANGED << x, y, b, j >>

CS(i) ==
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "exit"]
  /\ UNCHANGED << x, y, b, j >>

Exit(i) ==
  /\ pc[i] = "exit"
  /\ y' = 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "ncs"]
  /\ UNCHANGED << x, j >>

ProcStep(i) ==
     NCS(i)
  \/ Try1(i)
  \/ Try2(i)
  \/ Try3a(i)
  \/ Try3b(i)
  \/ WaitY0(i)
  \/ Try4(i)
  \/ Try5a(i)
  \/ Try5b(i)
  \/ ScanInc(i)
  \/ ScanFound(i)
  \/ ScanDone(i)
  \/ ContendWait(i)
  \/ CS(i)
  \/ Exit(i)

Next == \E i \in ProcSet: ProcStep(i)

Spec == Init /\ [][Next]_vars

InCS(p) == pc[p] = "cs"

Mutex == \A i, k \in ProcSet: i # k => ~(InCS(i) /\ InCS(k))

Invariant == Mutex

CondLiveness ==
  \A i \in ProcSet: (<>[] (pc[i] # "ncs")) => <> (pc[i] = "cs")

FairSpec ==
  Spec
  /\ \A i \in ProcSet:
       /\ WF_vars(Try1(i))
       /\ WF_vars(Try2(i))
       /\ WF_vars(Try3a(i))
       /\ WF_vars(Try3b(i))
       /\ WF_vars(WaitY0(i))
       /\ WF_vars(Try4(i))
       /\ WF_vars(Try5a(i))
       /\ WF_vars(Try5b(i))
       /\ WF_vars(ScanInc(i))
       /\ WF_vars(ScanFound(i))
       /\ WF_vars(ScanDone(i))
       /\ WF_vars(ContendWait(i))
       /\ WF_vars(Exit(i))

=============================================================================