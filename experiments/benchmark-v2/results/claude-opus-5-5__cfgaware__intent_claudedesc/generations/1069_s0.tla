---------------------- MODULE AsyncTerminationDetection ----------------------
EXTENDS Naturals

CONSTANT N

ASSUME NIsPosNat == N \in Nat \ {0}

Node == 0 .. N-1

MaxPending == 3

VARIABLES
    active,               \* active[n] : node n is active
    pending,              \* pending[n] : number of messages pending at node n
    terminationDetected   \* has termination been detected?

vars == << active, pending, terminationDetected >>

terminated == \A n \in Node : ~ active[n] /\ pending[n] = 0

-----------------------------------------------------------------------------

TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending \in [Node -> Nat]
    /\ terminationDetected \in BOOLEAN

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending = [n \in Node |-> 0]
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

Wakeup(i) ==
    /\ pending[i] > 0
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ UNCHANGED terminationDetected

DetectTermination ==
    /\ terminated
    /\ ~ terminationDetected
    /\ terminationDetected' = TRUE
    /\ UNCHANGED << active, pending >>

Next ==
    \/ DetectTermination
    \/ \E i \in Node :
         \/ Terminate(i)
         \/ Wakeup(i)
         \/ \E j \in Node : SendMsg(i, j)

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

-----------------------------------------------------------------------------

Safe == [](terminationDetected => terminated)

Quiescence == [](terminated => []terminated)

Live == terminated ~> terminationDetected

StateConstraint == \A n \in Node : pending[n] <= MaxPending

=============================================================================