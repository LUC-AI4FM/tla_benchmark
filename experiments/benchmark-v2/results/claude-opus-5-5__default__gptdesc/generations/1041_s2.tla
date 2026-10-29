---------------------------- MODULE MC ----------------------------
EXTENDS DijkstraMutex, TLC

\* MV CONSTANT declarations: model values used to instantiate Proc
CONSTANTS
    p1, p2, p3

\* MV CONSTANT definition: the set of processes substituted for Proc
const_Proc ==
    {p1, p2, p3}

\* SPECIFICATION definition: the behavior specification
spec_LSpec ==
    LSpec

\* INVARIANT definition: mutual exclusion safety property
inv_MutualExclusion ==
    MutualExclusion

\* PROPERTY definition: deadlock freedom liveness property
prop_DeadlockFreedom ==
    DeadlockFreedom

=============================================================================