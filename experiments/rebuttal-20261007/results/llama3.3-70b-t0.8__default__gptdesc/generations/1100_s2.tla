```
MODULE MutualExclusionLock
EXTENDS Integers

CONSTANTS P1, P2
VARIABLES pc, locked

Init == 
  (pc = [p \in {P1, P2} |-> "ncl"] /\ locked = FALSE)

Next == 
  (\E p \in {P1, P2} : 
    (pc[p] = "ncl" /\ locked = FALSE /\
      pc' = [pc EXCEPT ![p] = "l1"] /\ locked' = FALSE) \/
    (pc[p] = "l1" /\ locked = FALSE /\
      pc' = [pc EXCEPT ![p] = "cs"] /\ locked' = TRUE) \/
    (pc[p] = "cs" /\ locked = TRUE /\
      pc' = [pc EXCEPT ![p] = "ncl"] /\ locked' = FALSE)
  )

Spec == Init /\ [][Next]_<<pc, locked>>

MutualExclusionInvariant == 
  \A p1 \in {P1, P2}, p2 \in {P1, P2} : 
    (p1 # p2) => ~(pc[p1] = "cs" /\ pc[p2] = "cs")

LivenessProperty == 
  <>[]<>(pc[P1] = "l1" => <>(pc[P1] = "cs"))

THEOREM Spec => []MutualExclusionInvariant
THEOREM Spec => LivenessProperty

Fairness == SF_VARIABLES(<<pc, locked>>)
```
Note: The above specification is a direct translation of the given description into TLA+ and assumes that "ncl" stands for non-critical location, "l1" stands for waiting location for process 1, and "cs" stands for critical section. The `THEOREM` statements are used to assert the desired properties (mutual exclusion invariant and liveness property) of the specification.