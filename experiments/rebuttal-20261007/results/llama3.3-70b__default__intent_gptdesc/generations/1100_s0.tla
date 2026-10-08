```
MODULE MutualExclusionLock
EXTENDS Integers, FiniteSets

CONSTANTS NumProcesses
VARIABLES lock, processStates

Init ==
  /\ lock = "unlocked"
  /\ processStates \in [1..NumProcesses -> {"nonCritical"}]

Next ==
  \/ \E p \in 1..NumProcesses :
      /\ processStates[p] = "nonCritical"
      /\ processStates' = [processStates EXCEPT ![p] = "acquiring"]
      /\ lock' = lock
  \/ \E p \in 1..NumProcesses :
      /\ processStates[p] = "acquiring"
      /\ lock = "unlocked"
      /\ processStates' = [processStates EXCEPT ![p] = "critical"]
      /\ lock' = "locked"
  \/ \E p \in 1..NumProcesses :
      /\ processStates[p] = "acquiring"
      /\ lock = "locked"
      /\ processStates' = processStates
      /\ lock' = lock
  \/ \E p \in 1..NumProcesses :
      /\ processStates[p] = "critical"
      /\ processStates' = [processStates EXCEPT ![p] = "releasing"]
      /\ lock' = lock
  \/ \E p \in 1..NumProcesses :
      /\ processStates[p] = "releasing"
      /\ processStates' = [processStates EXCEPT ![p] = "nonCritical"]
      /\ lock' = "unlocked"

Spec ==
  Init /\ [][Next]_<<lock, processStates>>

MutualExclusion ==
  \A p1, p2 \in 1..NumProcesses :
    ~ (processStates[p1] = "critical" /\ processStates[p2] = "critical" /\ p1 # p2)

LockConsistency ==
  /\ \A p \in 1..NumProcesses :
      (processStates[p] = "critical" \/ processStates[p] = "releasing") => lock = "locked"
  /\ \A p \in 1..NumProcesses :
      processStates[p] # "critical" /\ processStates[p] # "releasing" => lock = "unlocked"

TypeInvariant ==
  /\ lock \in {"locked", "unlocked"}
  /\ processStates \in [1..NumProcesses -> {"nonCritical", "acquiring", "critical", "releasing"}]

THEOREM Spec => []MutualExclusion
THEOREM Spec => []LockConsistency
THEOREM Spec => []TypeInvariant

FAIRNESS <<Next>>_<<lock, processStates>>
```