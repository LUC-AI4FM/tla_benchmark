---------------------------- MODULE MC ----------------------------
EXTENDS DijkstraMutex, TLC

\* MV CONSTANT declarations (model values)
CONSTANTS
    p1, p2, p3

\* CONSTANT definitions: substitution for Proc
const_Proc == {p1, p2, p3}

\* SPECIFICATION definition
spec_LSpec == LSpec

\* INVARIANT definition
inv_MutualExclusion == MutualExclusion

\* PROPERTY definition
prop_DeadlockFreedom == DeadlockFreedom

=============================================================================