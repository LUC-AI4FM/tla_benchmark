---------------------------- MODULE StateMachine ----------------------------
EXTENDS Integers

CONSTANT InitialValue, MinValue, MaxValue
VARIABLE state

TypeInvariant == state \in MinValue..MaxValue

Init == state = InitialValue

NextState ==
  \/ state = InitialValue /\ state' = InitialValue
  \/ state = MinValue /\ state' \in (MinValue + 1)..MaxValue
  \/ state = MaxValue /\ state' = MinValue
  \/ state \in MinValue..(MaxValue - 1) /\ state' \in (state + 1)..MaxValue

Spec == Init /\ [][NextState]_state

THEOREM Spec => []TypeInvariant
THEOREM Spec => []Init
=============================================================================