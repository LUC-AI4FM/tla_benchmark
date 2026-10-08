---------------------------- MODULE TerminationDetection ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE active, pending, terminationDetected

TypeOK == active \in [1..N -> BOOLEAN] /\ 
          pending \in [1..N -> Nat] /\ 
          terminationDetected \in BOOLEAN

Init == (* Initial condition *)
       TypeOK /\ 
       (\A i \in 1..N : pending[i] = 0) /\ 
       (terminationDetected <=> (\A i \in 1..N : ~active[i]))

Terminate(i \in 1..N) == 
  active[i] /\ 
  * active' = [active EXCEPT ![i] = FALSE]
  * pending' = pending
  * terminationDetected' = IF (\A j \in 1..N : ~active[j] /\ pending[j] = 0)
                            THEN TRUE
                            ELSE terminationDetected

SendMsg(i \in 1..N, j \in 1..N) == 
  active[i] /\ 
  * active' = active
  * pending' = [pending EXCEPT ![j] = @ + 1]
  * terminationDetected' = terminationDetected

RcvMsg(i \in 1..N) == 
  pending[i] > 0 /\ 
  * active' = [active EXCEPT ![i] = TRUE]
  * pending' = [pending EXCEPT ![i] = @ - 1]
  * terminationDetected' = terminationDetected

DetectTermination == 
  (\A i \in 1..N : ~active[i] /\ pending[i] = 0) /\ 
  * active' = active
  * pending' = pending
  * terminationDetected' = TRUE

Next == (\E i \in 1..N : Terminate(i)) \/ 
        (\E i, j \in 1..N : SendMsg(i, j)) \/ 
        (\E i \in 1..N : RcvMsg(i)) \/ 
        DetectTermination

Spec == Init /\ [][Next]_<<active, pending, terminationDetected>> /\ 
       WF_(DetectTermination)(<<active, pending, terminationDetected>>)

Safe == []!(terminationDetected /\ (\E i \in 1..N : active[i] \/ pending[i] > 0))

Live == <>[]~(\A i \in 1..N : ~active[i] /\ pending[i] = 0) => 
         <>(terminationDetected)

Quiescence == []((\A i \in 1..N : ~active[i] /\ pending[i] = 0) => 
                 (\A j \in 1..N : ~active'[j] /\ pending'[j] = 0))

IndInv == TypeOK /\ Safe

THEOREM Spec => []Safe
THEOREM Spec => Live
THEOREM Spec => Quiescence
=============================================================================