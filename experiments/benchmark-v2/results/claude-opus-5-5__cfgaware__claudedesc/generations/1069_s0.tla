---------------------- MODULE AsyncTerminationDetection ----------------------
EXTENDS Naturals

CONSTANT N

ASSUME NIsPosNat == N \in Nat \ {0}

Node == 0 .. N-1

VARIABLES
  active,
  pending,
  terminationDetected

vars == << active, pending, terminationDetected >>

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ pending \in [Node -> Nat]
  /\ terminationDetected \in BOOLEAN

terminated == \A n \in Node : ~ active[n] /\ pending[n] = 0

-----------------------------------------------------------------------------

Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ pending = [i \in Node |-> 0]
  /\ terminationDetected \in {FALSE, terminated}

Terminate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ pending' = pending
  /\ terminationDetected' \in {terminationDetected, terminated'}

SendMsg(i, j) ==
  /\ active[i]
  /\ pending' = [pending EXCEPT ![j] = @ + 1]
  /\ UNCHANGED << active, terminationDetected >>

RcvMsg(i) ==
  /\ pending[i] > 0
  /\ active' = [active EXCEPT ![i] = TRUE]
  /\ pending' = [pending EXCEPT ![i] = @ - 1]
  /\ UNCHANGED terminationDetected

DetectTermination ==
  /\ terminated
  /\ terminationDetected' = TRUE
  /\ UNCHANGED << active, pending >>

Next ==
  \/ \E i \in Node :
        \/ Terminate(i)
        \/ RcvMsg(i)
        \/ \E j \in Node : SendMsg(i, j)
  \/ DetectTermination

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

-----------------------------------------------------------------------------

StateConstraint == \A i \in Node : pending[i] <= 3

Safe == terminationDetected => terminated

Live == terminated ~> terminationDetected

Quiescence == [](terminated => []terminated)

QuiescenceAsActionInv == terminated => terminated'

QuiescenceAsTraceInv == [][terminated => terminated']_vars

IndInv == TypeOK /\ Safe

THEOREM Spec => []TypeOK /\ []Safe /\ Live /\ Quiescence

=============================================================================