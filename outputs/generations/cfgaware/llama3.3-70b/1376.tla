---------------------------- MODULE SmallStateTransition ----------------------------
EXTENDS Integers

CONSTANT Data

VARIABLE state

Init == state = {}

Next == 
  \E x \in Data : 
    state' = state \cup {x}

=============================================================================