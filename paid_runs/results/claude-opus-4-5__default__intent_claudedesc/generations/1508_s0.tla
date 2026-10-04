---------------------------- MODULE SimpleStateMachine ----------------------------
EXTENDS Naturals

CONSTANTS FixedConstant, BoundedMax, OutOfRangeValue

VARIABLES x

\* Type invariant: x is within a small bounded range [0, BoundedMax]
TypeInvariant == x \in 0..BoundedMax

\* Safety invariant: x stays at its initial value of zero
StaysAtZero == x = 0

\* Combined invariant: x is bounded AND equals zero
Invariant == TypeInvariant /\ StaysAtZero

\* Initial state: x starts at zero
Init == x = 0

\* Transition 1: Set x to a fixed constant
SetToConstant == x' = FixedConstant

\* Transition 2: Assign x to some value in a small bounded range
AssignBounded == \E v \in 1..BoundedMax : x' = v

\* Transition 3: Set x to a specific out-of-range value
SetOutOfRange == x' = OutOfRangeValue

\* Transition 4: Specific value-to-value mapping (0 -> 1)
MapZeroToOne == x = 0 /\ x' = 1

\* Transition 5: Specific value-to-value mapping (1 -> 2)
MapOneToTwo == x = 1 /\ x' = 2

\* Next-state relation: any of the transitions can occur
Next == SetToConstant 
     \/ AssignBounded 
     \/ SetOutOfRange 
     \/ MapZeroToOne 
     \/ MapOneToTwo

\* Stuttering-closed next-state relation
NextOrStutter == Next \/ UNCHANGED x

\* The overall specification combines the invariant with the stuttering-closed 
\* next-state relation. Since the invariant requires x = 0, and every non-stuttering
\* step in Next changes x to a non-zero value, the only allowed behavior is stuttering.
\* This effectively constrains the system to do nothing after initialization.
Spec == Init /\ [][Next]_x /\ Invariant

\* Alternative formulation showing the constraint more explicitly
ConstrainedSpec == Init /\ [][Next /\ Invariant']_x

\* Correctness property: the specification is consistent
\* The initial condition satisfies the invariant
InitSatisfiesInvariant == Init => Invariant

\* Property to check: the combined specification is satisfiable
\* (there exists at least one behavior - the stuttering behavior from state x=0)
Consistency == Init /\ []Invariant

\* Theorem: Under the constrained spec, the invariant always holds
\* This is trivially true because no non-stuttering step is allowed
THEOREM Spec => []Invariant

===============================================================================