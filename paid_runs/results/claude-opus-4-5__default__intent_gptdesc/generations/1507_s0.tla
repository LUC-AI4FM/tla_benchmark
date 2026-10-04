---------------------------- MODULE ToggleBit ----------------------------
EXTENDS Booleans

VARIABLES bit

\* Type definition for the state variable
TypeInvariant == bit \in BOOLEAN

\* Initial state: bit starts as a valid boolean value
Init == bit \in BOOLEAN

\* Transition relation: deterministically toggle the bit
Next == bit' = ~bit

\* The complete specification with weak fairness to ensure progress
Spec == Init /\ [][Next]_bit /\ WF_bit(Next)

\* --------------------------------------------------------------------------
\* Safety Invariants
\* --------------------------------------------------------------------------

\* Type safety: the state must always be a boolean in all reachable states
TypeSafety == bit \in BOOLEAN

\* Safety of toggling: captured by the Next relation itself
\* This invariant states that if a step occurs, the bit must change
TogglingProperty == [][bit' = ~bit]_bit

\* --------------------------------------------------------------------------
\* Liveness Properties
\* --------------------------------------------------------------------------

\* Liveness/Progress: the system never deadlocks - a next state always exists
\* ENABLED Next means the Next action is enabled in the current state
NoDeadlock == []ENABLED(Next)

\* Progress property: the bit eventually changes (due to fairness)
EventuallyToggle == [](bit = TRUE => <>bit' = FALSE) /\ [](bit = FALSE => <>bit' = TRUE)

\* Alternative liveness: the system keeps making progress
AlwaysProgress == []<><<Next>>_bit

\* --------------------------------------------------------------------------
\* Determinism Property
\* --------------------------------------------------------------------------

\* Invariance of determinism: for any reachable state there is exactly one successor
\* This is inherently satisfied because Next defines bit' = ~bit uniquely
\* We express this as: the next state value is uniquely determined
DeterministicNext == ENABLED(Next) => \A b \in BOOLEAN : (bit' = b) => (b = ~bit)

\* --------------------------------------------------------------------------
\* Boolean Negation Constraint (Assumption)
\* --------------------------------------------------------------------------

\* Constraint that validates double negation returns original value
\* This is an axiom of boolean logic that we assert holds
DoubleNegationProperty == \A b \in BOOLEAN : ~~b = b

\* Applied to current state: double negation of bit equals bit
DoubleNegationHolds == ~~bit = bit

\* Theorem-like assertion combining the constraint with state
NegationInvolution == [](~~bit = bit)

\* --------------------------------------------------------------------------
\* Combined Invariants for Model Checking
\* --------------------------------------------------------------------------

\* All safety properties combined
SafetyInvariant == TypeSafety /\ DoubleNegationHolds

\* All temporal properties combined
LivenessProperty == NoDeadlock /\ AlwaysProgress

\* Complete correctness specification
Correctness == []SafetyInvariant /\ LivenessProperty /\ TogglingProperty /\ NegationInvolution

==========================================================================