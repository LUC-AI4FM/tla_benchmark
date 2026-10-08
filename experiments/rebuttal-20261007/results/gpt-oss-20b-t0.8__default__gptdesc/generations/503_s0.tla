MODULE SingleValueConsensus
EXTENDS Naturals

CONSTANTS Values

VARIABLE chosen

Init == chosen = {}

Choose(v) ==
    /\ chosen = {}
    /\ chosen' = {v}

Identity ==
    /\ chosen' = chosen

Next ==
    \E v \in Values : Choose(v)
    \/ Identity

Spec == Init
        /\ [][Next]_chosen
        /\ WF_NEXT(Next)

Invariant == (#chosen <= 1) /\ (chosen \subseteq Values)

THEOREM SafetyInvariant == Spec => [] Invariant

THEOREM LivenessTheorem == Spec => <> (chosen /= {})