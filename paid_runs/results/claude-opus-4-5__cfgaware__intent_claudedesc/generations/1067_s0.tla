---------------------------- MODULE TerminationDetection ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

VARIABLE active
VARIABLE detected

vars == <<active, detected>>

Nodes == 0..(N-1)

AllInactive == \A n \in Nodes : ~active[n]

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ detected \in BOOLEAN

Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ detected \in IF AllInactive THEN BOOLEAN ELSE {FALSE}

Deactivate(n) ==
    /\ active[n]
    /\ active' = [active EXCEPT ![n] = FALSE]
    /\ detected' = detected

WakeUp(sender, receiver) ==
    /\ active[sender]
    /\ sender # receiver
    /\ active' = [active EXCEPT ![receiver] = TRUE]
    /\ detected' = detected

Detect ==
    /\ AllInactive
    /\ ~detected
    /\ detected' = TRUE
    /\ active' = active

Next ==
    \/ \E n \in Nodes : Deactivate(n)
    \/ \E s, r \in Nodes : WakeUp(s, r)
    \/ Detect

Fairness == WF_vars(Detect)

Spec == Init /\ [][Next]_vars /\ Fairness

Safety == detected => AllInactive

StableTermination == AllInactive => [][AllInactive]_vars

Liveness == AllInactive ~> detected

=============================================================================