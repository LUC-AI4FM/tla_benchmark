MODULE FiniteStateSystem
EXTENDS Naturals

CONSTANTS STATE_SET, DOMAIN

VARIABLES state, mapping

(* Type invariant *)
TypeInvariant == mapping \in [DOMAIN -> STATE_SET]

(* Safety invariant: some index maps to current state *)
StateMappingInvariant ==
  \E i \in DOMAIN : mapping[i] = state

Init ==
  /\ state \in STATE_SET
  /\ mapping \in [DOMAIN -> STATE_SET]
  /\ StateMappingInvariant

Next ==
  \E newState \in STATE_SET, newMapping \in [DOMAIN -> STATE_SET] :
    /\ \E j \in DOMAIN : newMapping[j] = newState
    /\ state' = newState
    /\ mapping' = newMapping

(* Liveness property: system never deadlocks *)
NoDeadlock ==
  \A s, m : \E ns \in STATE_SET :
          \E nm \in [DOMAIN -> STATE_SET] :
            (\E j \in DOMAIN : nm[j] = ns)

Spec == Init /\ [][Next]_<<state,mapping>> /\ NoDeadlock

===============================================================================