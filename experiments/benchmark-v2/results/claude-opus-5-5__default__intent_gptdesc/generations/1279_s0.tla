---------------------------- MODULE PositiveChoice ----------------------------
EXTENDS Integers

CONSTANTS InitVal,     \* the concrete initial integer
          Allowed      \* the small finite set of permitted values

ASSUME InitVal \in Int
ASSUME Allowed \subseteq Int
ASSUME InitVal # 0

VARIABLES x

vars == << x >>

\* The values that may actually be assigned: allowed AND strictly positive
PositiveAllowed == { v \in Allowed : v > 0 }

TypeOK == x \in ({InitVal} \cup PositiveAllowed)

Init == x = InitVal

\* Nondeterministic reassignment to any allowed, strictly positive value
Assign == \E v \in Allowed : /\ v > 0
                             /\ x' = v

Next == Assign

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Safety invariant: the variable is never zero in any reachable state
NeverZero == x # 0

\* Transition constraint: every non-stuttering step assigns a permitted,
\* strictly positive value
StepOK == (x' # x) => (x' \in Allowed /\ x' > 0)

TransitionConstraint == [][StepOK]_vars

THEOREM Spec => []TypeOK
THEOREM Spec => []NeverZero
THEOREM Spec => TransitionConstraint
=============================================================================