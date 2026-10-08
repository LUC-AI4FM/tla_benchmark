---- MODULE MutualExclusionLock ----

EXTENDS Integers, FiniteSets, TLC

CONSTANTS P \* Set of processes, e.g., {1, 2}

VARIABLES lock, loc

Init == /\ lock = FALSE
        /\ loc = [p \in P -> "non-critical"]

Next ==
    \/ /\ lock = FALSE
       /\ \E p \in P : loc[p] = "waiting"
       /\ /\ loc' = [loc EXCEPT ![p] = "critical"]
          /\ lock' = TRUE
    \/ /\ \E p \in P : loc[p] = "critical"
       /\ loc' = [loc EXCEPT ![p] = "non-critical"]
          /\ lock' = FALSE
    \/ /\ \E p \in P : loc[p] = "non-critical"
       /\ loc' = [loc EXCEPT ![p] = IF lock THEN "waiting" ELSE "critical"]

Spec ==
    /\ Init
    /\ [][Next]_<<lock, loc>>
    /\ WF_next(<<lock, loc>>)

MutualExclusion == 
    \A p1, p2 \in P : p1 # p2 => ~(\E i \in 0..1 : loc[i][p1] = "critical" /\ loc[i][p2] = "critical")

SpecWithInvariants ==
    Spec
    /\ <>[]MutualExclusion

LivenessProperty ==
    \A p \in P : <>(loc[p] = "critical")

SpecWithProperties ==
    SpecWithInvariants
    /\ <><>(\E p \in P : loc[p] = "waiting") => LivenessProperty

====