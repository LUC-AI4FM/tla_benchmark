MODULE FastMutex
EXTENDS Naturals, Sequences, TLC, Temporal

CONSTANTS N

VARIABLES x, y, b, j

State == {"Idle", "SetB", "CheckXY", "Critical"}

Init ==
  /\ x = 0
  /\ y = 0
  /\ b \in [1..N -> BOOLEAN]
  /\ b = [i \in 1..N |-> FALSE]
  /\ j \in [1..N -> State]
  /\ j = [i \in 1..N |-> "Idle"]

TryAction(i) ==
  /\ i \in 1..N
  /\ j[i] = "Idle"
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ j' = [j EXCEPT ![i] = "SetB"]
  /\ UNCHANGED <<x, y>>

CheckAction(i) ==
  /\ i \in 1..N
  /\ j[i] = "SetB"
  /\ x = 0
  /\ y = 0
  /\ j' = [j EXCEPT ![i] = "Critical"]
  /\ UNCHANGED <<x, y, b>>

WaitAction(i) ==
  /\ i \in 1..N
  /\ j[i] = "SetB"
  /\ (x > 0 \/ y > 0)
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ j' = [j EXCEPT ![i] = "Idle"]
  /\ UNCHANGED <<x, y>>

EnterCS(i) ==
  /\ i \in 1..N
  /\ j[i] = "Critical"
  /\ x' = i
  /\ y' = i
  /\ UNCHANGED <<b, j>>

ExitCS(i) ==
  /\ i \in 1..N
  /\ j[i] = "Critical"
  /\ x' = 0
  /\ y' = 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ j' = [j EXCEPT ![i] = "Idle"]

Next ==
  \E i \in 1..N :
    (TryAction(i) \/ CheckAction(i) \/ WaitAction(i) \/ EnterCS(i) \/ ExitCS(i))

vars == <<x, y, b, j>>

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

MutualExclusion ==
  \A i, k \in 1..N : ((j[i] = "Critical") /\ (i # k)) => j[k] # "Critical"

Liveness ==
  \E i \in 1..N : []<>(j[i] = "Critical")

THEOREM Spec => MutualExclusion
THEOREM Spec => Liveness