---------------------------- MODULE AsyncTerminationDetection ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES
    active,
    pending,
    terminationDetected

vars == <<active, pending, terminationDetected>>

Node == 0..(N-1)

TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending \in [Node -> Nat]
    /\ terminationDetected \in BOOLEAN

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending \in [Node -> Nat]
    /\ terminationDetected = FALSE

Terminated ==
    /\ \A n \in Node : ~active[n]
    /\ \A n \in Node : pending[n] = 0

Terminate(n) ==
    /\ active[n]
    /\ active' = [active EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<pending, terminationDetected>>

SendMsg(sender, receiver) ==
    /\ active[sender]
    /\ pending' = [pending EXCEPT ![receiver] = @ + 1]
    /\ UNCHANGED <<active, terminationDetected>>

ReceiveMsg(n) ==
    /\ pending[n] > 0
    /\ pending' = [pending EXCEPT ![n] = @ - 1]
    /\ active' = [active EXCEPT ![n] = TRUE]
    /\ UNCHANGED terminationDetected

DetectTermination ==
    /\ ~terminationDetected
    /\ Terminated
    /\ terminationDetected' = TRUE
    /\ UNCHANGED <<active, pending>>

Next ==
    \/ \E n \in Node : Terminate(n)
    \/ \E s, r \in Node : SendMsg(s, r)
    \/ \E n \in Node : ReceiveMsg(n)
    \/ DetectTermination

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(DetectTermination)

Safety == terminationDetected => Terminated

TerminationStable == [][Terminated => Terminated']_vars

StableTermination == Terminated => []Terminated

DetectionImpliesTermination == terminationDetected => Terminated

Liveness == Terminated ~> terminationDetected

InvPendingNonNegative == \A n \in Node : pending[n] >= 0

InvDetectionOnlyWhenTerminated == terminationDetected => Terminated

InvActiveOrPending == 
    ~terminationDetected => 
        (\E n \in Node : active[n]) \/ (\E n \in Node : pending[n] > 0) \/ Terminated

StateConstraint == \A n \in Node : pending[n] <= 3

=============================================================================