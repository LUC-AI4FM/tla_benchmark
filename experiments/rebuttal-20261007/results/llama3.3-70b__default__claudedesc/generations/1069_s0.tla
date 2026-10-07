```tla
MODULE TerminationDetection
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES active, pending, terminationDetected

Init ==
  /\ active \in [1..N -> {TRUE, FALSE}]
  /\ pending \in [1..N -> 0..3]
  /\ terminationDetected = (active = [i \in 1..N |-> FALSE] /\ pending = [i \in 1..N |-> 0])

Next ==
  \/ \E i \in 1..N :
      /\ active[i] = TRUE
      /\ active' = [active EXCEPT ![i] = FALSE]
      /\ pending' = pending
      /\ IF (active = [i \in 1..N |-> FALSE] /\ pending = [i \in 1..N |-> 0])
         THEN terminationDetected' = TRUE
         ELSE terminationDetected' = terminationDetected
  \/ \E i, j \in 1..N :
      /\ active[i] = TRUE
      /\ pending'[j] = pending[j] + 1
      /\ UNCHANGED <<active, pending EXCEPT ![j], terminationDetected>>
  \/ \E i \in 1..N :
      /\ pending[i] > 0
      /\ pending' = [pending EXCEPT ![i] = @ - 1]
      /\ active' = [active EXCEPT ![i] = TRUE]
      /\ UNCHANGED terminationDetected
  \/ \E i \in 1..N :
      /\ (active = [i \in 1..N |-> FALSE] /\ pending = [i \in 1..N |-> 0])
      /\ terminationDetected' = TRUE
      /\ UNCHANGED <<active, pending>>

Spec ==
  Init /\ [][Next]_<<active, pending, terminationDetected>>
  /\ WF_(DetectTermination, <<active, pending, terminationDetected>>)

DetectTermination ==
  (active = [i \in 1..N |-> FALSE] /\ pending = [i \in 1..N |-> 0])
  /\ terminationDetected' = TRUE
  /\ UNCHANGED <<active, pending>>

Safe ==
  terminationDetected => (active = [i \in 1..N |-> FALSE] /\ pending = [i \in 1..N |-> 0])

Live ==
  <>[]terminationDetected

Quiescence ==
  []((active = [i \in 1..N |-> FALSE] /\ pending = [i \in 1..N |-> 0]) => [](active = [i \in 1..N |-> FALSE] /\ pending = [i \in 1..N |-> 0]))

TypeOK ==
  /\ active \in [1..N -> {TRUE, FALSE}]
  /\ pending \in [1..N -> 0..3]
  /\ terminationDetected \in {TRUE, FALSE}

IndInv ==
  TypeOK /\ Safe

THEOREM Spec => []Safe
THEOREM Spec => Live
THEOREM Spec => Quiescence
```