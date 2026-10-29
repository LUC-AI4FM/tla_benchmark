---------------------------- MODULE StateGeneration ----------------------------
EXTENDS Naturals

CONSTANTS
    Values,      \* the three distinct target values of the first component
    InitX,       \* fixed initial value of the first component
    InitY        \* fixed (constant) value of the second component

ASSUME ValuesAssumption ==
    /\ \E a, b, c \in Values :
          /\ a # b /\ b # c /\ a # c
          /\ Values = {a, b, c}

VARIABLES x, y

vars == << x, y >>

-----------------------------------------------------------------------------
TypeOK ==
    /\ x \in Values \cup {InitX}
    /\ y = InitY

Init ==
    /\ x = InitX
    /\ y = InitY

\* Nondeterministically set the first component to value v;
\* the second component stays unchanged.
SetX(v) ==
    /\ x' = v
    /\ UNCHANGED y

\* Explicit stutter step: both components remain unchanged.
Stutter ==
    UNCHANGED vars

Next ==
    \/ \E v \in Values : SetX(v)
    \/ Stutter

\* Trace-based execution model: any behavior starting in Init whose every
\* step is a Next step or a stuttering step.
Spec == Init /\ [][Next]_vars

\* Optional fair variant: guarantees that every target value is eventually
\* produced in every fair behavior, without fixing any order of generation.
FairSpec == Spec /\ \A v \in Values : SF_vars(SetX(v))

-----------------------------------------------------------------------------
\* Safety: trivial invariant, always true; places no constraint on states.
TrivialInvariant == TRUE

\* The second component never changes.
YConstant == [][y' = y]_vars

-----------------------------------------------------------------------------
\* Coverage / liveness.

\* Under FairSpec, each of the three values is eventually reached.
Coverage == \A v \in Values : <>(x = v)

\* Reachability witnesses (existential coverage under Spec): for each v,
\* the property NeverReach(v) is expected to be VIOLATED when checked
\* against Spec, demonstrating that some execution reaches x = v.
NeverReach(v) == [](x # v)

\* State-predicate witnesses usable as invariants (each should be violated,
\* showing that the corresponding value is reachable from Init).
NotReached(v) == x # v

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []TrivialInvariant
THEOREM Spec => YConstant
THEOREM FairSpec => Coverage
=============================================================================