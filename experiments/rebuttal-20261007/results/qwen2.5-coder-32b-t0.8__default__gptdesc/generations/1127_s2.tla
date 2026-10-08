------------------------------ MODULE TwoPhaseCommit ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS RMs  \* Set of resource managers

VARIABLES states \* A mapping from each RM to its state

(* --algorithm TwoPhaseCommit *)

Init == 
    /\ states \in [RMs -> {"working"}]

Next ==
    \/ \E rm \in RMs : Prepare(rm)
    \/ \E rm \in RMs : Decide(rm)

Prepare(rm) ==
    /\ states[rm] = "working"
    /\ /\[states' = [states EXCEPT ![rm] = "prepared"]\]

Decide(rm) ==
    /\ states[rm] \in {"prepared", "working"}
    /\ \/ states[rm] = "prepared" -> (\A rm2 \in RMs : states[rm2] \notin {"committed", "aborted"})
       \/ states[rm] = "working"  -> TRUE
    /\ /\[states' = [states EXCEPT ![rm] = IF states[rm] = "prepared" THEN CHOOSE s \in {"committed", "aborted"} : TRUE ELSE states[rm]]\]

Spec == 
    Init /\ [][Next]_<<states>>

TypeInvariant ==
    /\ states \in [RMs -> {"working", "prepared", "committed", "aborted"}]

ConsistencyInvariant ==
    \/ (\A rm1, rm2 \in RMs : states[rm1] = states[rm2])
    \/ (\E rm \in RMs : states[rm] = "aborted" /\ (\A rm2 \in RMs \ {rm} : states[rm2] \in {"aborted", "working"}))
    \/ (\E rm \in RMs : states[rm] = "committed" /\ (\A rm2 \in RMs \ {rm} : states[rm2] \in {"committed", "working"}))

Safety ==
    TypeInvariant /\ ConsistencyInvariant

Liveness ==
    <>[](\A rm \in RMs : states[rm] \notin {"working", "prepared"})

=============================================================================