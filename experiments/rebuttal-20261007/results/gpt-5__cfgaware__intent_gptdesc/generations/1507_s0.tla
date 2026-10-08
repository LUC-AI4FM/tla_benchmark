------------------------------ MODULE ToggleBit ------------------------------

EXTENDS TLC

VARIABLES bit

TypeOK == bit \in BOOLEAN

Init == TypeOK

Next == /\ TypeOK
        /\ bit' = ~bit

Spec == Init /\ [][Next]_bit

(*
  Relational (non-primed) view of the transition for stating meta-properties.
*)
NextRel(old, new) == new = ~old

(*
  Correctness properties (to be used as invariants or temporal properties):
  - Type safety: the state is always a Boolean.
  - Determinism: from any state, exactly one Boolean successor is defined by NextRel.
  - Progress (no deadlock): a Next-step is always enabled.
  - Safety of toggling: every Next-step flips the bit.
  - Boolean negation involution (assumption/constraint): ~~bit = bit.
*)
TypeSafety       == []TypeOK
Determinism      == [](\A x, y \in BOOLEAN: (NextRel(bit, x) /\ NextRel(bit, y)) => x = y)
NoDeadlock       == []ENABLED Next
ToggleSafety     == [](Next => (bit' # bit))
NegationInvolution == ~~bit = bit

=============================================================================