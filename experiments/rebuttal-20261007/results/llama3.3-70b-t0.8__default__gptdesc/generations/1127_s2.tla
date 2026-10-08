```
MODULE TwoPhaseCommit
EXTENDS Integers, FiniteSets

CONSTANTS RMs, DecideSet
VARIABLES state, decided

Init ==
  /\ state \in [RMs -> {"working"}]
  /\ decided = {}

Next ==
  \/ \E rm \in RMs :
      /\ state[rm] = "working"
      /\ state' = [state EXCEPT ![rm] = "prepared"]
      /\ decided' = decided
      /\ UNCHANGED << >>
  \/ \E rm \in RMs, d \in DecideSet :
      /\ state[rm] = "prepared"
      /\ decided' = decided \cup {rm}
      /\ state' = [state EXCEPT ![rm] = IF d = "commit" THEN "committed" ELSE "aborted"]
      /\ UNCHANGED << >>

Spec == Init /\ [][Next]_<<state, decided>>

TypeCorrectness ==
  state \in [RMs -> {"working", "prepared", "committed", "aborted"}]

ConsistencyInvariant ==
  \A rm1, rm2 \in RMs :
    \/ decided[rm1] = {}
    \/ decided[rm2] = {}
    \/ decided[rm1] = decided[rm2]

SafetyInv == TypeCorrectness /\ ConsistencyInvariant

Fairness == SF_VARIABLES(<<state, decided>>)

THEOREM Spec => []SafetyInv
THEOREM Spec => Fairness
```