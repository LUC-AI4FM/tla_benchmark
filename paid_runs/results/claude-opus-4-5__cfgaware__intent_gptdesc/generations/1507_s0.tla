---------------------------- MODULE specification ----------------------------

VARIABLE bit

(* Type invariant: bit must always be a boolean *)
TypeOK == bit \in BOOLEAN

(* Initial state: bit starts as some valid boolean value *)
Init == bit \in BOOLEAN

(* Transition relation: toggle the bit to its logical negation *)
Next == bit' = ~bit

(* Specification: initial state and always take a next step *)
Spec == Init /\ [][Next]_bit

(* Liveness specification: ensure progress by requiring Next always eventually happens *)
LiveSpec == Init /\ [][Next]_bit /\ WF_bit(Next)

(* Safety of toggling: every transition changes the bit *)
TogglingProperty == [][bit' = ~bit]_bit

(* Determinism: for any state, there is exactly one successor *)
(* This is inherently satisfied since Next deterministically assigns bit' = ~bit *)
(* We express this as: if we can take a step, the next value is uniquely determined *)
DeterminismInvariant == ENABLED Next => \A b \in BOOLEAN : (bit' = b) => (b = ~bit)

(* No deadlock: from any state, a next state exists *)
NoDeadlock == ENABLED Next

(* Assumption/Constraint: double negation returns original value *)
(* This validates the boolean negation relationship *)
DoubleNegationAxiom == \A b \in BOOLEAN : ~~b = b

(* Alternative constraint relating current value and its negation *)
NegationRelation == bit \in BOOLEAN /\ ~bit \in BOOLEAN /\ ~~bit = bit

(* Combined constraint for model checking validation *)
BooleanConstraint == DoubleNegationAxiom /\ NegationRelation

=============================================================================