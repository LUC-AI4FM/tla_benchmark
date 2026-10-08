```
MODULE RingTermination
EXTENDS Naturals, TLC

CONSTANTS N, MaxPending

VARIABLES active, pending, terminationDetected

NodeSet == 1..N
NextNode(i) == IF i < N THEN i + 1 ELSE 1

TypeInvariant ==
  /\ active \in [NodeSet -> BOOLEAN]
  /\ pending \in [NodeSet -> Nat]
  /\ terminationDetected \in BOOLEAN
  /\ \A i \in NodeSet : pending[i] <= MaxPending

Init ==
  TypeInvariant
  /\ active = [i \in NodeSet |-> TRUE]
  /\ pending = [i \in NodeSet |-> 0]
  /\ terminationDetected = FALSE

Send(i,j) ==
  /\ i \in NodeSet
  /\ j \in NodeSet
  /\ j = NextNode(i)
  /\ pending' = [pending EXCEPT ![j] = @ + 1]
  /\ active'   = active
  /\ terminationDetected' = terminationDetected

Receive(j) ==
  /\ j \in NodeSet
  /\ pending[j] > 0
  /\ pending' = [pending EXCEPT ![j] = @ - 1]
  /\ active'   = active
  /\ terminationDetected' = terminationDetected

Terminate(i) ==
  /\ i \in NodeSet
  /\ active[i] = TRUE
  /\ active'   = [active EXCEPT ![i] = FALSE]
  /\ pending'  = pending
  /\ terminationDetected' = terminationDetected

DetectTermination ==
  /\ \A i \in NodeSet : active[i] = FALSE
  /\ \A i \in NodeSet : pending[i] = 0
  /\ terminationDetected' = TRUE
  /\ active'   = active
  /\ pending'  = pending

Next ==
  \/ \E i,j \in NodeSet : Send(i,j)
  \/ \E j \in NodeSet : Receive(j)
  \/ \E i \in NodeSet : Terminate(i)
  \/ DetectTermination

StateConstraint ==
  \A i \in NodeSet : pending[i] <= MaxPending

SafetyInvariant1 ==
  terminationDetected => (\A i \in NodeSet : active[i] = FALSE)

SafetyInvariant2 ==
  terminationDetected => (\A i \in NodeSet : pending[i] = 0)

StabilityInvariant ==
  terminationDetected => terminationDetected'

LivenessProperty ==
  [] ( (\A i \in NodeSet : active[i] = FALSE /\ pending[i] = 0) => <> terminationDetected )

Spec ==
  Init
  /\ [][Next]_vars
  /\ WF_DetectTermination
  /\ []StateConstraint
  /\ []TypeInvariant

```
