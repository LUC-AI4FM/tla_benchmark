```
MODULE TwoPhaseCommit
EXTENDS Integers, TLC

CONSTANTS RMs, DecideValue
VARIABLES state, decision

Init ==
  /\ state = [r \in RMs |-> "working"]
  /\ decision = << >>

Next ==
  \/ \E r \in RMs :
        /\ state[r] = "working"
        /\ state' = [state EXCEPT ![r] = "prepared"]
        /\ decision' = decision
  \/ \E r \in RMs, dv \in DecideValue :
        /\ state[r] = "prepared"
        /\ dv \in {"committed", "aborted"}
        /\ state' = [state EXCEPT ![r] = dv]
        /\ decision' = <<dv >> @ decision

Spec == Init /\ [][Next]_<<state, decision>>

TypeInvariant ==
  decision \subseteq RMs \X {"committed", "aborted"}

ConsistencyInvariant ==
  \A r1, r2 \in RMs :
    \/ decision[1] = ""
    \/ decision[2] = ""
    \/ decision[1] = decision[2]

Safety == []TypeInvariant /\ []ConsistencyInvariant

Fairness == SF_VARIABLES(state)

THEOREM Spec => []TypeInvariant
THEOREM Spec => []ConsistencyInvariant

```
Note that the TLC module is included for model checking with the TLA+ Toolbox. DecideValue is assumed to be a set containing "committed" and "aborted". RMs represents the set of resource managers, which can be an arbitrary set of identifiers.