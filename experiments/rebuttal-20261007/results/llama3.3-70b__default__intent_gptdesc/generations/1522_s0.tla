```
MODULE WeightedTerminationDetection
EXTENDS Integers, FiniteSets

CONSTANTS ProcSet, Leader
VARIABLES state, weight, messages

Init ==
  /\ state = [p \in ProcSet |-> IF p = Leader THEN "active" ELSE "idle"]
  /\ weight = [p \in ProcSet |-> IF p = Leader THEN 1 ELSE 0]
  /\ messages = {}

Next ==
  \/ \E p \in ProcSet :
      /\ state[p] = "active"
      /\ state' = [state EXCEPT ![p] = "idle"]
      /\ weight' = [weight EXCEPT ![p] = 0]
      /\ messages' = messages \cup {<<p, Leader, weight[p]>>}
  \/ \E p \in ProcSet :
      /\ state[p] = "idle"
      /\ weight[p] = 0
      /\ \E q \in ProcSet : 
          /\ messages' = messages \cup {<<q, p, 1/2>>}
          /\ weight' = [weight EXCEPT ![p] = 1/2]
          /\ state' = state
  \/ \E m \in messages :
      /\ LET p == m[1] , q == m[2] IN
        /\ messages' = messages \ {m}
        /\ weight' = [weight EXCEPT ![q] = weight[q] + m[3]]
        /\ state' = state

Spec ==
  /\ Init
  /\ [][Next]_state
  /\ WF_vars(Next, state, weight, messages)

TerminationDetected == 
  /\ state[Leader] = "idle"
  /\ weight[Leader] = 1
  /\ messages = {}

SafetyInv ==
  /\ TerminationDetected => \A p \in ProcSet : state[p] = "idle"
  /\ TerminationDetected => messages = {}
  /\ \A p, q \in ProcSet, m \in messages :
      /\ m[3] > 0
      /\ m[3] * 2 == 1

LivenessInv ==
  <>TerminationDetected

THEOREM Spec => []SafetyInv
THEOREM Spec => LivenessInv
```