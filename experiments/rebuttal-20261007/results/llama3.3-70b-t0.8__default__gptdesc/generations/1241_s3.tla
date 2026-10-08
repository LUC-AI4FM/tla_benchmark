```
MODULE Translation
EXTENDS Integers, Sequences, TLC

CONSTANTS AlgTree, ProcTree, ProcessTree, LabelTree, FairnessOption
VARIABLES spec, init, next, termination, fairness

Init ==
  /\ spec = << >>
  /\ init = FALSE
  /\ next = FALSE
  /\ termination = FALSE
  /\ fairness = "noFairness"

Next ==
  /\ IF fairness = "noFairness" THEN
    /\ spec' = Append(spec, "NoFairness")
    /\ init' = init
    /\ next' = next
    /\ termination' = termination
    /\ fairness' = fairness
  ELSE IF fairness = "weakProcessFairness" THEN
    /\ spec' = Append(spec, "WeakProcessFairness")
    /\ init' = init
    /\ next' = next
    /\ termination' = termination
    /\ fairness' = fairness
  ELSE IF fairness = "weakNextFairness" THEN
    /\ spec' = Append(spec, "WeakNextFairness")
    /\ init' = init
    /\ next' = next
    /\ termination' = termination
    /\ fairness' = fairness
  ELSE IF fairness = "strongProcessFairness" THEN
    /\ spec' = Append(spec, "StrongProcessFairness")
    /\ init' = init
    /\ next' = next
    /\ termination' = termination
    /\ fairness' = fairness
  ELSE
    /\ spec' = spec
    /\ init' = init
    /\ next' = next
    /\ termination' = termination
    /\ fairness' = fairness

Spec ==
  /\ Init
  /\ [][Next]_spec
  /\ WF Variables (Next)

TerminationProperty ==
  <>(termination = TRUE)

THEOREM Spec => []TerminationProperty
```