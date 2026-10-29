---------------------------- MODULE TerminationDetection ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, pending, terminationDetected

vars == << active, pending, terminationDetected >>

Nodes == 0 .. (N - 1)

Succ(i) == (i + 1) % N

MaxPending == 2

-----------------------------------------------------------------------------

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ pending \in [Nodes -> Nat]
    /\ terminationDetected \in BOOLEAN

Terminated ==
    \A i \in Nodes : ~active[i] /\ pending[i] = 0

-----------------------------------------------------------------------------

Init ==
    /\ active = [i \in Nodes |-> TRUE]
    /\ pending = [i \in Nodes |-> 0]
    /\ terminationDetected = FALSE

Terminate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED << pending, terminationDetected >>

SendMsg(i) ==
    /\ active[i]
    /\ pending' = [pending EXCEPT ![Succ(i)] = @ + 1]
    /\ UNCHANGED << active, terminationDetected >>

RcvMsg(i) ==
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ UNCHANGED terminationDetected

DetectTermination ==
    /\ ~terminationDetected
    /\ Terminated
    /\ terminationDetected' = TRUE
    /\ UNCHANGED << active, pending >>

Done ==
    /\ terminationDetected
    /\ UNCHANGED vars

Next ==
    \/ \E i \in Nodes : Terminate(i) \/ SendMsg(i) \/ RcvMsg(i)
    \/ DetectTermination
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

-----------------------------------------------------------------------------

(* Safety: detection implies actual termination *)
Safe == terminationDetected => Terminated

(* Termination is stable once reached *)
Quiescence == [](Terminated => []Terminated)

(* Liveness: actual termination leads to eventual detection *)
Live == Terminated ~> terminationDetected

(* Auxiliary invariants *)
DetectedStable == terminationDetected => \A i \in Nodes : ~active[i]

NoPendingWhenDetected == terminationDetected => \A i \in Nodes : pending[i] = 0

(* State constraint for bounded model checking *)
StateConstraint == \A i \in Nodes : pending[i] <= MaxPending

=============================================================================