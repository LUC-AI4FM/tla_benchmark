---- MODULE MC ----
EXTENDS DijkstraMutex, TLC

\* Model values used to instantiate the set of processes
CONSTANTS
    p1, p2, p3

\* Constant definition: Proc <- {p1, p2, p3}
const_Proc == {p1, p2, p3}
----

\* SPECIFICATION definition: the behavior spec imported from DijkstraMutex
spec_LSpec == LSpec
----

\* INVARIANT definition: safety property imported from DijkstraMutex
inv_MutualExclusion == MutualExclusion
----

\* PROPERTY definition: temporal property imported from DijkstraMutex
prop_DeadlockFreedom == DeadlockFreedom
----
=============================================================================