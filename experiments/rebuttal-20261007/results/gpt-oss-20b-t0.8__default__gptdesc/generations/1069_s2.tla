MODULE RingTermination
EXTENDS Naturals, TLC

CONSTANTS N, MAXP

VARIABLES active, pending, detect

TypeInvariant ==
  /\ active \in [1..N -> BOOLEAN]
  /\ pending \in [1..N -> Nat]
  /\ detect \in BOOLEAN
  /\ \A i \in 1..N : pending[i] <= MAXP

Init ==
  /\ active = [i \in 1..N |-> TRUE]
  /\ pending = [i \in 1..N |-> 0]
  /\ detect = FALSE
  /\ TypeInvariant

TerminateAction(i) ==
  /\ i \in 1..N
  /\ active[i] = TRUE
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ pending' = pending
  /\ detect' = detect

SendMsg(i,j) ==
  /\ i \in 1..N
  /\ j \in 1..N
  /\ active[i] = TRUE
  /\ pending' = [pending EXCEPT ![j] = pending[j]+1]
  /\ active' = active
  /\ detect' = detect

Receive(j) ==
  /\ j \in 1..N
  /\ pending[j] > 0
  /\ pending' = [pending EXCEPT ![j] = pending[j]-1]
  /\ active' = active
  /\ detect' = detect

DetectTermination ==
  /\ detect' = TRUE
  /\ active' = active
  /\ pending' = pending
  /\ \A i \in 1..N : active[i] = FALSE /\ pending[i] = 0

Next ==
  IF detect THEN
      UNCHANGED <<active, pending, detect>>
  ELSE
      (\E i \in 1..N : TerminateAction(i)) \/ 
      (\E i,j \in 1..N : SendMsg(i,j)) \/ 
      (\E j \in 1..N : Receive(j)) \/ 
      DetectTermination

DetInv ==
   detect => \A i \in 1..N : active[i] = FALSE /\ pending[i] = 0

StableDetect ==
   detect' = TRUE => detect

Spec == Init /\ [][Next]_<<active, pending, detect>> /\ WF(DetectTermination)

THEOREM Safety : Spec => [](DetInv)
THEOREM Stability : Spec => [](StableDetect)

TerminationCond ==
  \A i \in 1..N : active[i] = FALSE /\ pending[i] = 0

LivenessProp == [] (TerminationCond => <> detect)

THEOREM TerminationToDetection : Spec => LivenessProp