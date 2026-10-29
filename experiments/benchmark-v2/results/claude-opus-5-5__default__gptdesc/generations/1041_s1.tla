---------------------------- MODULE MC ----------------------------
EXTENDS DijkstraMutex, TLC

\* MV CONSTANT declarations
CONSTANTS
p1, p2, p3

\* MV CONSTANT definitions Proc
const_ProcMV ==
{p1, p2, p3}

\* SPECIFICATION definition
spec_LSpec ==
LSpec

\* INVARIANT definition
inv_MutualExclusion ==
MutualExclusion

\* PROPERTY definition
prop_DeadlockFreedom ==
DeadlockFreedom

=============================================================================