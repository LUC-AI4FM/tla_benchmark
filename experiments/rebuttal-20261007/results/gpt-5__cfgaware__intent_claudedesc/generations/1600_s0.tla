---- MODULE FastMutex ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, defaultInitValue

VARIABLES X, Y, b, pc

ProcSet == 1..N

Labels == {"A0", "A1", "A1w", "A3", "A5", "A6", "CS"}

vars == << X, Y, b, pc >>

TypeOK ==
  /\ X \in 0..N
  /\ Y \in 0..N
  /\ b \in [ProcSet -> BOOLEAN]
  /\ pc \in [ProcSet -> Labels]

Init ==
  /\ X = 0
  /\ Y = 0
  /\ b = [i \in ProcSet |-> FALSE]
  /\ pc = [i \in ProcSet |-> "A0"]

Proc(i) ==
  \/ /\ pc[i] = "A0"
     /\ b' = [b EXCEPT ![i] = TRUE]
     /\ X' = i
     /\ UNCHANGED Y
     /\ pc' = [pc EXCEPT ![i] = "A1"]
  \/ /\ pc[i] = "A1" /\ Y # 0
     /\ b' = [b EXCEPT ![i] = FALSE]
     /\ UNCHANGED << X, Y >>
     /\ pc' = [pc EXCEPT ![i] = "A1w"]
  \/ /\ pc[i] = "A1" /\ Y = 0
     /\ Y' = i
     /\ UNCHANGED << X, b >>
     /\ pc' = [pc EXCEPT ![i] = "A3"]
  \/ /\ pc[i] = "A1w" /\ Y = 0
     /\ UNCHANGED << X, Y, b >>
     /\ pc' = [pc EXCEPT ![i] = "A0"]
  \/ /\ pc[i] = "A3" /\ X = i
     /\ UNCHANGED << X, Y, b >>
     /\ pc' = [pc EXCEPT ![i] = "CS"]
  \/ /\ pc[i] = "A3" /\ X # i
     /\ b' = [b EXCEPT ![i] = FALSE]
     /\ UNCHANGED << X, Y >>
     /\ pc' = [pc EXCEPT ![i] = "A5"]
  \/ /\ pc[i] = "A5"
     /\ \A j \in ProcSet: (j = i) \/ (b[j] = FALSE)
     /\ UNCHANGED << X, Y, b >>
     /\ pc' = [pc EXCEPT ![i] = "A6"]
  \/ /\ pc[i] = "A6" /\ Y = i
     /\ UNCHANGED << X, Y, b >>
     /\ pc' = [pc EXCEPT ![i] = "CS"]
  \/ /\ pc[i] = "A6" /\ Y # i
     /\ UNCHANGED << X, Y, b >>
     /\ pc' = [pc EXCEPT ![i] = "A1w"]
  \/ /\ pc[i] = "CS"
     /\ Y' = 0
     /\ b' = [b EXCEPT ![i] = FALSE]
     /\ UNCHANGED X
     /\ pc' = [pc EXCEPT ![i] = "A0"]

Next == \E i \in ProcSet: Proc(i)

MutualExclusion ==
  Cardinality({ i \in ProcSet: pc[i] = "CS" }) <= 1

Invariant == TypeOK /\ MutualExclusion

Liveness == []<>(\E i \in ProcSet: pc[i] = "CS")

Spec ==
  Init /\ [][Next]_vars /\ \A i \in ProcSet: WF_vars(Proc(i))

====