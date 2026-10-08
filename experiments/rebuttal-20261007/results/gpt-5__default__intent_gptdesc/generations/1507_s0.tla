----------------------------- MODULE ToggleBit -----------------------------

EXTENDS TLC

CONSTANTS DUMMY

VARIABLES bit

Init ==
  bit \in BOOLEAN

Next ==
  bit' = ~bit

Spec ==
  Init /\ [] Next

TypeInv ==
  bit \in BOOLEAN

TypeSafety ==
  [] TypeInv

ToggleSafety ==
  [] (bit' = ~bit)

NoDeadlock ==
  [] ENABLED Next

DeterministicValue ==
  \A v1, v2 \in BOOLEAN: (v1 = ~bit /\ v2 = ~bit) => v1 = v2

Determinism ==
  [] DeterministicValue

DoubleNeg ==
  \A b \in BOOLEAN: ~~b = b

ASSUME DoubleNeg

ASSUME DUMMY = TRUE

============================================================================