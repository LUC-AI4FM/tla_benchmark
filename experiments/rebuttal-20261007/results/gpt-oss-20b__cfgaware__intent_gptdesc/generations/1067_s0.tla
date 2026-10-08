---- MODULE RingTermination ----
EXTENDS Naturals, TLC

CONSTANT N \in Nat
ASSUME N > 0

VARIABLES active, terminated

vars == <<active, terminated>>

(* All processes are inactive *)
AllInactive == \A i \in 1..N : active[i] = FALSE

Init ==
    /\ active \in [1..N -> BOOLEAN]
    /\ terminated = FALSE

LocalDeactivation ==
    \E i \in 1..N :
        /\ active[i] = TRUE
        /\ active' = [active EXCEPT ![i] = FALSE]
        /\ terminated' = terminated

ActivationAction ==
    \E i, j \in 1..N :
        /\ i /= j
        /\ active[i] = TRUE
        /\ active' = [active EXCEPT ![j] = TRUE]
        /\ terminated' = terminated

TerminationEvent ==
    /\ ~terminated
    /\ AllInactive
    /\ terminated' = TRUE
    /\ active' = active

Next == LocalDeactivation \/ ActivationAction \/ TerminationEvent

Spec == Init /\ [][Next]_vars

Fairness == WF_vars(TerminationEvent)

SafetyInvariant == terminated => AllInactive

LivenessProperty == [] (AllInactive => <> terminated)

THEOREM SpecSatisfiesSafety == Spec => SafetyInvariant
THEOREM SpecEnsuresTermination == Spec /\ Fairness => LivenessProperty

====