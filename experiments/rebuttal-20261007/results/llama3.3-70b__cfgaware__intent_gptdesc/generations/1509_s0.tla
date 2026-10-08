---------------------------- MODULE SimpleFiniteState ----------------------------
EXTENDS Integers

CONSTANT Domain
VARIABLE state, mapping

Init == (* Initial condition: arbitrary choice of state from {1,2,3,4,5} *)
        /\ state \in {1,2,3,4,5}
        /\ mapping \in [Domain -> {1,2,3,4,5}]

Next == (* Nondeterministic step: may change state or keep it unchanged *)
        /\ state' \in {1,2,3,4,5}
        /\ mapping' = mapping

Inv == (* Safety invariant: exists index in Domain whose mapped value equals state *)
       \E i \in Domain : mapping[i] = state

Liveness == (* Liveness property: always has at least one enabled transition *)
            <>(state /= state')

Spec == Init /\ [][Next]_<<state, mapping>>
THEOREM Spec => []Inv
THEOREM Spec => Liveness

=============================================================================