------------------------------ MODULE FastMutex ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N >= 1

VARIABLES x, y, b, S, pc

Proc == 1..N
Null == 0
PCVals == {"start", "L1", "awaitY0", "L2", "awaitAllFalse", "cs"}

vars == << x, y, b, S, pc >>

TypeOK ==
  /\ x \in Proc \cup {Null}
  /\ y \in Proc \cup {Null}
  /\ b \in [Proc -> BOOLEAN]
  /\ S \in [Proc -> SUBSET Proc]
  /\ pc \in [Proc -> PCVals]

Init ==
  /\ x = Null
  /\ y = Null
  /\ b = [i \in Proc |-> FALSE]
  /\ S = [i \in Proc |-> {}]
  /\ pc = [i \in Proc |-> "start"]

OthersFalse(i) == \A j \in Proc: j # i => b[j] = FALSE

Start(i) ==
  /\ pc[i] = "start"
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ x' = i
  /\ S' = [S EXCEPT ![i] = {}]
  /\ pc' = [pc EXCEPT ![i] = "L1"]
  /\ UNCHANGED y

L1_yNonZero(i) ==
  /\ pc[i] = "L1"
  /\ y # Null
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "awaitY0"]
  /\ UNCHANGED << x, y, S >>

L1_yZero(i) ==
  /\ pc[i] = "L1"
  /\ y = Null
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "L2"]
  /\ UNCHANGED << x, b, S >>

AwaitY0(i) ==
  /\ pc[i] = "awaitY0"
  /\ y = Null
  /\ pc' = [pc EXCEPT ![i] = "start"]
  /\ UNCHANGED << x, y, b, S >>

L2_xEq(i) ==
  /\ pc[i] = "L2"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b, S >>

L2_xNeq(i) ==
  /\ pc[i] = "L2"
  /\ x # i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ S' = [S EXCEPT ![i] = { j \in Proc : j # i /\ b[j] }]
  /\ pc' = [pc EXCEPT ![i] = "awaitAllFalse"]
  /\ UNCHANGED << x, y >>

AwaitAllFalse(i) ==
  /\ pc[i] = "awaitAllFalse"
  /\ OthersFalse(i)
  /\ S' = [S EXCEPT ![i] = {}]
  /\ pc' = [pc EXCEPT ![i] = IF y # i THEN "awaitY0" ELSE "cs"]
  /\ UNCHANGED << x, y, b >>

CSExit(i) ==
  /\ pc[i] = "cs"
  /\ y' = Null
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ S' = [S EXCEPT ![i] = {}]
  /\ pc' = [pc EXCEPT ![i] = "start"]
  /\ UNCHANGED x

ProcStep(i) ==
  Start(i)
  \/ L1_yNonZero(i)
  \/ L1_yZero(i)
  \/ AwaitY0(i)
  \/ L2_xEq(i)
  \/ L2_xNeq(i)
  \/ AwaitAllFalse(i)
  \/ CSExit(i)

Next == \E i \in Proc: ProcStep(i)

Mutex ==
  \A i, j \in Proc: (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

SomeInCSInfOften ==
  []<>(\E i \in Proc: pc[i] = "cs")

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================