---------------------------- MODULE DistributedTerminationDetection ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N
VARIABLES state, terminated

state == [i \in 1..N |-> "active" \/ "inactive"]
terminated == FALSE

Init ==
  /\ state \in [1..N -> {"active", "inactive"}]
  /\ terminated = FALSE

TypeInvariant ==
  /\ state \in [1..N -> {"active", "inactive"}]
  /\ terminated \in BOOLEAN

LocalTermination(i) ==
  /\ state[i] = "active"
  /\ state' = [state EXCEPT ![i] = "inactive"]
  /\ terminated' = terminated
  /\ UNCHANGED << >>

ActivateProcess(i, j) ==
  /\ state[i] = "active"
  /\ state[j] = "inactive"
  /\ state' = [state EXCEPT ![j] = "active"]
  /\ terminated' = terminated
  /\ UNCHANGED << >>

DetectTermination ==
  /\ \A i \in 1..N : state[i] = "inactive"
  /\ terminated' = TRUE
  /\ UNCHANGED state

Next ==
  \/ \E i \in 1..N : LocalTermination(i)
  \/ \E i, j \in 1..N : ActivateProcess(i, j)
  \/ DetectTermination

Spec ==
  Init /\ [][Next]_<<state, terminated>>

THEOREM Spec => []TypeInvariant
THEOREM Spec => WF_<< >>(DetectTermination)
THEOREM Spec => [](terminated => \A i \in 1..N : state[i] = "inactive")
THEOREM Spec => []( \A i \in 1..N : state[i] = "inactive" ) => <>terminated
=============================================================================