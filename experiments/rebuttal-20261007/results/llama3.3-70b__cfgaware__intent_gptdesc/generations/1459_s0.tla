---------------------------- MODULE Counter ----------------------------
EXTENDS Integers

CONSTANT Limit

VARIABLE state

Spec == 
  /\ state = 0
  /\ [][
      IF state < Limit THEN
        /\ (state' = state + 1) OR (state' = state)
      ELSE
        /\ state' = state
    ]

THEOREM Spec => [] (state >= 0)
THEOREM Spec => [] (state' >= state)
THEOREM Spec => [] (state <= Limit)
THEOREM Spec => <> (state = Limit)

INVARIANT StateInvariant == state >= 0 /\ state <= Limit

Liveness == <> (state = Limit)

ModelCheck == 
  Spec
  /\ Liveness

=============================================================================