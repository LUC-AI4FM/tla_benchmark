```
MODULE TwoPhaseCommit
EXTENDS Integers, FiniteSets

CONSTANTS RMs
VARIABLES state

Init == (state = [r \in RMs |-> "working"])

Prepare(r) == (state[r] = "working") /\ (state' = [state EXCEPT ![r] = "prepared"])
Decide(r, d) == (state[r] = "prepared") /\ (d \in {"committed", "aborted"}) /\ (state' = [state EXCEPT ![r] = d])

Next == \E r \in RMs : Prepare(r) \/ \E d \in {"committed", "aborted"} : Decide(r, d)

Spec == Init /\ [][Next]_state

TypeCorrectness == \A r \in RMs : state[r] \in {"working", "prepared", "committed", "aborted"}
Consistency == \A r1, r2 \in RMs : (state[r1] = "committed") => (state[r2] # "aborted")

THEOREM Spec => []TypeCorrectness
THEOREM Spec => []Consistency

Fairness == \A r \in RMs : <>[](Prepare(r) \/ \E d \in {"committed", "aborted"} : Decide(r, d))

THEOREM Spec /\ Fairness => <>(\E r \in RMs : state[r] \in {"committed", "aborted"})
```