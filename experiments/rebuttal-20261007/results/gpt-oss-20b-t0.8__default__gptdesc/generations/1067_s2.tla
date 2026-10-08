MODULE RingTermination
EXTENDS Naturals, TLC

CONSTANTS Node

VARIABLES active, detection

vars == <<active, detection>>

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ detection = FALSE

Terminate(n) ==
    /\ n \in Node
    /\ active[n] = TRUE
    /\ active' = [active EXCEPT ![n] = FALSE]
    /\ UNCHANGED detection

WakeUp(m, n) ==
    /\ m \in Node
    /\ n \in Node
    /\ active[m] = TRUE
    /\ active[n] = FALSE
    /\ active' = [active EXCEPT ![n] = TRUE]
    /\ UNCHANGED detection

Detect ==
    /\ detection = FALSE
    /\ (\A n \in Node : active[n] = FALSE)
    /\ detection' = TRUE
    /\ UNCHANGED active

Next ==
    \/ \E n \in Node: Terminate(n)
    \/ \E m, n \in Node: WakeUp(m, n)
    \/ Detect

SafetyInvariant ==
    /\ (detection => (\A n \in Node : NOT active[n]))

Correctness ==
    [] ((\A n \in Node : NOT active[n]) => <> detection)

Quiescence ==
    [] (detection => [] (active = [x \in Node |-> FALSE]))

Spec ==
    Init
    /\ [][Next]_vars
    /\ WF(Detect)
    /\ SafetyInvariant
    /\ Correctness
    /\ Quiescence

===============================================================================