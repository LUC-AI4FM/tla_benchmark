-------------------------------- MODULE TerminationDetection --------------------------------

EXTENDS Integers, FiniteSets, TLAPS

CONSTANTS N

ASSUME NAssumption == N \in Nat /\ N > 0

VARIABLES active, pending, terminationDetected

vars == <<active, pending, terminationDetected>>

Nodes == 0..(N-1)

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ pending \in [Nodes -> Nat]
    /\ terminationDetected \in BOOLEAN

Terminated ==
    /\ \A n \in Nodes : ~active[n]
    /\ \A n \in Nodes : pending[n] = 0

Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ pending = [n \in Nodes |-> 0]
    /\ terminationDetected = (\A n \in Nodes : ~active[n])

Terminate(n) ==
    /\ active[n]
    /\ active' = [active EXCEPT ![n] = FALSE]
    /\ pending' = pending
    /\ terminationDetected' \in {terminationDetected, 
                                  IF Terminated' THEN TRUE ELSE terminationDetected}

SendMsg(sender, receiver) ==
    /\ active[sender]
    /\ pending' = [pending EXCEPT ![receiver] = pending[receiver] + 1]
    /\ active' = active
    /\ terminationDetected' = terminationDetected

RcvMsg(n) ==
    /\ pending[n] > 0
    /\ pending' = [pending EXCEPT ![n] = pending[n] - 1]
    /\ active' = [active EXCEPT ![n] = TRUE]
    /\ terminationDetected' = terminationDetected

DetectTermination ==
    /\ Terminated
    /\ ~terminationDetected
    /\ terminationDetected' = TRUE
    /\ active' = active
    /\ pending' = pending

Next ==
    \/ \E n \in Nodes : Terminate(n)
    \/ \E sender, receiver \in Nodes : SendMsg(sender, receiver)
    \/ \E n \in Nodes : RcvMsg(n)
    \/ DetectTermination

Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

-----------------------------------------------------------------------------
(* Safety Properties *)

Safe == terminationDetected => Terminated

(* Liveness Properties *)

Live == Terminated ~> terminationDetected

(* Quiescence Property *)

Quiescence == Terminated => [][Terminated]_vars

(* Action-formula variants of quiescence *)

QuiescenceAction == Terminated => Terminated'

StableTermination == [][Terminated => Terminated']_vars

-----------------------------------------------------------------------------
(* Inductive Invariant for Apalache *)

IndInv == TypeOK /\ Safe

-----------------------------------------------------------------------------
(* State Constraint for Model Checking *)

StateConstraint == \A n \in Nodes : pending[n] <= 3

=============================================================================