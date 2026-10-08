```tla
MODULE TerminationDetection

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node

VARIABLES state, detected

(* --algorithm TerminationDetection
variables 
  state = [n \in Node |-> "active"], 
  detected = FALSE;

begin
Init:
  /\ state = [n \in Node |-> "active"]
  /\ detected = FALSE;

Next ==
  \/ /\ E\<exists> n \in Node : state[n] = "active"
     /\ state' = [state EXCEPT ![n] = "inactive"]
        /\ detected' = detected
  \/ /\ E\<exists> n, m \in Node : state[n] = "active" /\ state[m] = "inactive"
     /\ state' = [state EXCEPT ![m] = "active"]
        /\ detected' = detected
  \/ /\ UNCHANGED state
     /\ detected' = (IF \A n \in Node: state[n] = "inactive" THEN TRUE ELSE detected);

Spec ==
  Init /\ [][Next]_<<state, detected>>;

TerminationDetected ==
  <>(detected = TRUE);

Quiescence ==
  [](detected => []\<forall> n \in Node : state[n] = "inactive");

FairDetection ==
  WF_next(S_<<state>>, <<detected>>) /\ SF_next(S_<<state>>, <<detected>>);

Correctness ==
  Spec /\ TerminationDetected /\ Quiescence;

THEOREM Correctness /\ FairDetection
end algorithm *)
```