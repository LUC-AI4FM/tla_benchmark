---- MODULE MC ----
EXTENDS DijkstraMutex, TLC

\* Model values used to instantiate the set of processes
CONSTANTS
p1, p2, p3

\* Constant definition: substituted for Proc in the model
const_Proc ==
{p1, p2, p3}

\* Behavior specification: the underlying LSpec from DijkstraMutex
spec_LSpec ==
LSpec

\* Safety invariant: mutual exclusion of the critical section
inv_MutualExclusion ==
MutualExclusion

\* Temporal (liveness) property: deadlock freedom
prop_DeadlockFreedom ==
DeadlockFreedom

=============================================================================