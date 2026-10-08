---------------------------- MODULE termination ----------------------------

EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

VARIABLES active, pending, terminationDetected

vars == <<active, pending, terminationDetected>>

Node == 0..(N-1)

TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending \in [Node -> Nat]
    /\ terminationDetected \in BOOLEAN

Terminated ==
    /\ \A n \in Node : ~active[n]
    /\ \A n \in Node : pending[n] = 0

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending = [n \in Node |-> 0]
    /\ terminationDetected = (IF \A n \in Node : ~active[n] THEN TRUE ELSE FALSE)

Terminate(n) ==
    /\ active[n]
    /\ active' = [active EXCEPT ![n] = FALSE]
    /\ pending' = pending
    /\ \/ (Terminated' /\ terminationDetected' = TRUE)
       \/ terminationDetected' = terminationDetected

SendMsg(src, dst) ==
    /\ active[src]
    /\ pending' = [pending EXCEPT ![dst] = pending[dst] + 1]
    /\ active' = active
    /\ terminationDetected' = terminationDetected

RcvMsg(n) ==
    /\ pending[n] > 0
    /\ pending' = [pending EXCEPT ![n] = pending[n] - 1]
    /\ active' = [active EXCEPT ![n] = TRUE]
    /\ terminationDetected' = terminationDetected

DetectTermination ==
    /\ Terminated
    /\ terminationDetected' = TRUE
    /\ active' = active
    /\ pending' = pending

Next ==
    \/ \E n \in Node : Terminate(n)
    \/ \E src, dst \in Node : SendMsg(src, dst)
    \/ \E n \in Node : RcvMsg(n)
    \/ DetectTermination

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

Safe == terminationDetected => Terminated

Live == Terminated ~> terminationDetected

Quiescence == Terminated => [][Terminated]_vars

QuiescenceAction == Terminated => Terminated'

IndInv == TypeOK /\ Safe

StateConstraint == \A n \in Node : pending[n] <= 3

=============================================================================